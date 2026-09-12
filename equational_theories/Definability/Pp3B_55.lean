import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = m(Y,X) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_pyx_pxy_pxx_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq20 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq15
    | exact resolve eq15 eq17
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
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X3 X1) X0) X0
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq23 X0 X1 X2 X3
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq23
    | exact resolve eq23 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq31 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq35 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq37 : ∀ X0 X1 X2 : G, (k (τ X2) (k X0 (τ X1))) = (τ (k X2 (k (σ X0) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 X2 (k X0 (τ X1))
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq22
    | exact resolve eq22 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq43 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq43 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq43 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq57 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq57 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq57
    | (have j0 := eq57 (σ X0) (σ X1)
       grind)
    | exact resolve eq57 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq22 (σ X0) X0
       have i₂ := eq44 (σ X0)
       grind)
    | exact superpose eq44 eq22
    | exact resolve eq22 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq83 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq44 (τ X0)
       grind)
    | exact superpose eq44 eq18
    | exact resolve eq18 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq84 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq83 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq83
    | exact resolve eq83 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq85 : ∀ X0 : G, (k X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq82 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq82
    | exact resolve eq82 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq92 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq84 X0
       have i₂ := eq44 X0
       grind)
    | exact superpose eq44 eq84
    | exact resolve eq84 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq93 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq85 X0
       have i₂ := eq44 X0
       grind)
    | exact superpose eq44 eq85
    | exact resolve eq85 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq96 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq92 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq92
    | exact resolve eq92 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : ∀ X0 X1 X2 : G, (M.op (k X0 (σ X1)) (σ X2)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq68 X0 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq68
    | exact resolve eq68 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq68 x y
       grind)
    | exact superpose eq68 eq16
    | (have j1 := eq68 x y
       grind)
    | exact resolve eq16 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq152 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = (M.op X1 (M.op (σ (M.op X0 X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25 X2 (σ X0) X1 (σ X0)
       have i₂ := eq96 X0
       grind)
    | exact superpose eq96 eq25
    | exact resolve eq25 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq353 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq152 X0 X1 (σ (M.op X0 X0))
       have i₂ := eq96 (M.op X0 X0)
       grind)
    | exact superpose eq96 eq152
    | exact resolve eq152 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq407 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq125
       have i₂ := eq57 x y
       grind)
    | exact superpose eq57 eq125
    | (have j1 := eq57 (σ x) (σ y)
       grind)
    | exact resolve eq125 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq125
  have eq408 : (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq407
  have eq647 : ∀ X0 X1 X2 : G, (M.op (σ X0) (k X1 (σ X2))) ≠ (M.op (σ X0) (k X1 (σ X2))) ∨ (σ X0) = (M.op (σ X0) (k X1 (σ X2))) ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (k X1 (σ X2))) ∨ (σ (k X0 (k (τ X1) X2))) = (M.op (σ X0) (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (σ X2) (k X0 (σ X1))
       have i₂ := eq122 X0 X1 X2
       grind)
    | exact superpose eq122 eq13
    | (have j0 := eq13 (σ X0) (k X1 (σ X2))
       have j1 := eq122 X1 X2 X0
       grind)
    | (have r₁ := eq13 (k X0 (σ X1)) (σ X2)
       have r₂ := eq122 X0 X1 X2
       grind)
    | (have r₁ := eq13 (σ X2) (k X0 (σ X1))
       have r₂ := eq122 X0 X1 X2
       grind)
    | exact resolve eq13 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq649 : ∀ X0 X1 X2 : G, (σ X0) ≠ (M.op (σ X0) (k X1 (σ X2))) ∨ (k (σ X0) (k X1 (σ X2))) = (M.op (σ X0) (k X1 (σ X2))) ∨ (σ (k X0 (k (τ X1) X2))) = (M.op (σ X0) (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (σ X0) (k X1 (σ X2))
       have i₂ := eq122 X1 X2 X0
       grind)
    | exact superpose eq122 eq12
    | (have j0 := eq12 (σ X0) (k X1 (σ X2))
       have j1 := eq122 X1 X2 X0
       grind)
    | exact resolve eq12 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq657 : ∀ X0 X1 X2 X3 : G, (M.op X3 (k X0 (σ X1))) = (M.op X3 (M.op (M.op (k X0 (σ X1)) (σ X2)) X3)) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (k X0 (σ X1)) (σ X2)
       have i₂ := eq122 X0 X1 X2
       grind)
    | exact superpose eq122 eq9
    | (have j1 := eq122 X0 X1 X2
       grind)
    | exact resolve eq9 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq661 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) (k X1 (σ X2))) ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (k X1 (σ X2))) ∨ (σ (k X0 (k (τ X1) X2))) = (M.op (σ X0) (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq647 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647
  have eq662 : ∀ X0 X1 X2 X3 : G, (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) ∨ (M.op X3 (σ X2)) = (M.op X3 (k X0 (σ X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq657 X0 X1 X2 X3
       have i₂ := eq9 X3 (σ X2) (k X0 (σ X1))
       grind)
    | exact superpose eq9 eq657
    | (have j0 := eq657 X0 X1 X2 X3
       grind)
    | exact resolve eq657 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657
  have eq668 : ∀ X0 X1 X2 : G, (σ (k X0 (k (τ X1) X2))) = (M.op (σ X0) (k X1 (σ X2))) ∨ (σ X0) ≠ (M.op (σ X0) (k X1 (σ X2))) ∨ (σ (k X0 (k (τ X1) X2))) = (M.op (σ X0) (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq649 X0 X1 X2
       have i₂ := eq20 X1 X2 X0
       grind)
    | exact superpose eq20 eq649
    | (have j0 := eq649 X0 X1 X2
       grind)
    | exact resolve eq649 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649
  have eq669 : ∀ X0 X1 X2 : G, (σ X0) ≠ (M.op (σ X0) (k X1 (σ X2))) ∨ (σ (k X0 (k (τ X1) X2))) = (M.op (σ X0) (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq668 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668
  have eq671 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 (k (τ X1) X2))) ∨ (σ X0) = (M.op (σ X0) (k X1 (σ X2))) ∨ (σ (k X0 (k (τ X1) X2))) = (M.op (σ X0) (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq661 X0 X1 X2
       have i₂ := eq20 X1 X2 X0
       grind)
    | exact superpose eq20 eq661
    | (have j0 := eq661 X0 X1 X2
       grind)
    | exact resolve eq661 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq661
  have eq684 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (σ (k X0 (k (τ X1) X2))) ∨ (σ X0) = (M.op (σ X0) (k X1 (σ X2))) ∨ (σ (k X0 (k (τ X1) X2))) = (M.op (σ X0) (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq671 X0 X1 X2
       have i₂ := eq96 X0
       grind)
    | exact superpose eq96 eq671
    | (have j0 := eq671 X0 X1 X2
       grind)
    | exact resolve eq671 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671
  have eq1311 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op (M.op x y) X1)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 x X0 y
       have i₂ := eq408
       grind)
    | exact superpose eq408 eq25
    | exact resolve eq25 eq408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408
  have eq1320 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op X0 x) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq1311 X0 x
       have i₂ := eq25 x y X0 x
       grind)
    | exact superpose eq25 eq1311
    | exact resolve eq1311 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1311
  have eq1471 : ∀ X0 X1 X2 X3 : G, (M.op X3 (σ (M.op (M.op X0 X1) X2))) = (M.op X3 (σ (M.op (M.op (M.op (M.op X0 X1) X2) X1) (M.op (M.op (M.op X0 X1) X2) X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq353 (M.op (M.op X3 X1) X0) X1
       have i₂ := eq25 X0 X1 (M.op (M.op X3 X1) X0) X3
       grind)
    | exact superpose eq25 eq353
    | exact resolve eq353 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353
  have eq1556 : ∀ X0 X1 X2 X3 : G, (M.op X3 (σ (M.op (M.op X0 X1) X2))) = (M.op X3 (σ (M.op (M.op (M.op (M.op X0 X1) X2) X1) X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1471 X0 X1 X2 X3
       have i₂ := eq25 X1 X2 (M.op (M.op (M.op X0 X1) X2) X1) (M.op X0 X1)
       grind)
    | exact superpose eq25 eq1471
    | exact resolve eq1471 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1471
  have eq3082 : ∀ X0 X1 X2 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) ∨ (M.op X2 x) = (M.op X2 y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25 X1 (σ x) X0 (σ y)
       have i₂ := eq1320 X2
       grind)
    | exact superpose eq1320 eq25
    | (have j1 := eq1320 X2
       grind)
    | exact resolve eq25 eq1320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1320
  have eq3091 : ∀ X0 X2 : G, (M.op X2 x) = (M.op X2 y) ∨ (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
    intro X0 X2
    first
    | (have i₁ := eq3082 X0 x X2
       have i₂ := eq25 x (σ y) X0 (σ x)
       grind)
    | exact superpose eq25 eq3082
    | (have j0 := eq3082 X0 x X2
       grind)
    | exact resolve eq3082 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3082
  have eq6010 : ∀ X0 X1 X2 X3 : G, (σ (k X1 (k X0 X2))) = (M.op (σ X1) (k (σ X0) (σ X2))) ∨ (M.op X3 (σ X1)) = (M.op X3 (k (σ X0) (σ X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq662 (σ X0) X2 X1 X3
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq662
    | (have j0 := eq662 (σ X0) X2 X1 X3
       grind)
    | exact resolve eq662 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662
  have eq6141 : ∀ X0 X1 X2 X3 : G, (σ (k X1 (k X0 X2))) = (M.op (σ X1) (σ (k X0 X2))) ∨ (M.op X3 (σ X1)) = (M.op X3 (k (σ X0) (σ X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6010 X0 X1 X2 X3
       have i₂ := eq15 X0 X2
       grind)
    | exact superpose eq15 eq6010
    | (have j0 := eq6010 X0 X1 X2 X3
       grind)
    | exact resolve eq6010 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6010
  have eq6167 : ∀ X0 X1 X2 X3 : G, (σ (k X1 (k X0 X2))) = (M.op (σ X1) (σ (k X0 X2))) ∨ (M.op X3 (σ X1)) = (M.op X3 (σ (k X0 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6141 X0 X1 X2 X3
       have i₂ := eq15 X0 X2
       grind)
    | exact superpose eq15 eq6141
    | (have j0 := eq6141 X0 X1 X2 X3
       grind)
    | exact resolve eq6141 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6141
  have eq18830 : ∀ X0 X1 X2 : G, (σ (k X0 (k (τ X1) X2))) = (M.op (σ X0) (k X1 (σ X2))) ∨ (σ (M.op X0 X0)) = (σ (k X0 (k (τ X1) X2))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq684 X0 X1 X2
       have j1 := eq669 X0 X1 X2
       grind)
    | (have r₁ := eq684 X0 X1 X2
       have r₂ := eq669 X0 X1 X2
       grind)
    | exact resolve eq684 eq669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669 eq684
  have eq19019 : ∀ X0 X1 X2 : G, (σ (τ (k X0 (k (σ (τ X1)) X2)))) = (M.op (σ (τ X0)) (k X1 (σ (τ X2)))) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (τ (k X0 (k (σ (τ X1)) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18830 (τ X2) X1 (τ X1)
       have i₂ := eq37 (τ X1) X1 X2
       grind)
    | exact superpose eq37 eq18830
    | exact resolve eq18830 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq18830
  have eq19213 : ∀ X0 X1 X2 : G, (M.op (σ (τ X0)) (k X1 X2)) = (σ (τ (k X0 (k (σ (τ X1)) X2)))) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (τ (k X0 (k (σ (τ X1)) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19019 X0 X1 X2
       have i₂ := eq11 X2
       grind)
    | exact superpose eq11 eq19019
    | (have j0 := eq19019 X0 X1 X2
       grind)
    | exact resolve eq19019 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19019
  have eq19261 : ∀ X0 X1 X2 : G, (k X0 (k (σ (τ X1)) X2)) = (M.op (σ (τ X0)) (k X1 X2)) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (τ (k X0 (k (σ (τ X1)) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19213 X0 X1 X2
       have i₂ := eq11 (k X0 (k (σ (τ X1)) X2))
       grind)
    | exact superpose eq11 eq19213
    | (have j0 := eq19213 X0 X1 X2
       grind)
    | exact resolve eq19213 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19213
  have eq19300 : ∀ X0 X1 X2 : G, (k X0 (k (σ (τ X1)) X2)) = (M.op X0 (k X1 X2)) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (τ (k X0 (k (σ (τ X1)) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19261 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq19261
    | (have j0 := eq19261 X0 X1 X2
       grind)
    | exact resolve eq19261 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19261
  have eq19325 : ∀ X0 X1 X2 : G, (k X0 (k X1 X2)) = (M.op X0 (k X1 X2)) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (τ (k X0 (k (σ (τ X1)) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19300 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq19300
    | (have j0 := eq19300 X0 X1 X2
       grind)
    | exact resolve eq19300 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19300
  have eq19335 : ∀ X0 X1 X2 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (k (σ (τ X1)) X2)) ∨ (k X0 (k X1 X2)) = (M.op X0 (k X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19325 X0 X1 X2
       have i₂ := eq11 (k X0 (k (σ (τ X1)) X2))
       grind)
    | exact superpose eq11 eq19325
    | (have j0 := eq19325 X0 X1 X2
       grind)
    | exact resolve eq19325 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19325
  have eq19341 : ∀ X0 X1 X2 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (k X1 X2)) ∨ (k X0 (k X1 X2)) = (M.op X0 (k X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19335 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq19335
    | (have j0 := eq19335 X0 X1 X2
       grind)
    | exact resolve eq19335 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19335
  have eq19343 : ∀ X0 X1 X2 : G, (k X0 (k X1 X2)) = (M.op X0 (k X1 X2)) ∨ (M.op X0 X0) = (k X0 (k X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19341 X0 X1 X2
       have i₂ := eq92 X0
       grind)
    | exact superpose eq92 eq19341
    | (have j0 := eq19341 X0 X1 X2
       grind)
    | exact resolve eq19341 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19341
  have eq19480 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X0 (k X1 X2)) ∨ (M.op X0 X0) = (k X0 (k X1 X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq19343 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19343
  have eq19770 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) ≠ (M.op X1 X1) ∨ (k X1 (M.op X0 X0)) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19480 X0 X0 X0
       have i₂ := eq44 X0
       grind)
    | exact superpose eq44 eq19480
    | exact resolve eq19480 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19480
  have eq20105 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 (M.op (M.op X2 X1) (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19770 (M.op X2 X1) X0
       have i₂ := eq25 (M.op X2 X1) X1 X0 X2
       grind)
    | exact superpose eq25 eq19770
    | (have j0 := eq19770 (M.op X2 X1) X0
       grind)
    | (have r₁ := eq19770 X0 (M.op (M.op x (M.op X0 X0)) X0)
       have r₂ := eq25 X0 (M.op X0 X0) (M.op (M.op x (M.op X0 X0)) X0) x
       grind)
    | (have r₁ := eq19770 (M.op x X1) X1
       have r₂ := eq25 (M.op x X1) X1 X1 x
       grind)
    | exact resolve eq19770 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19770
  have eq22077 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq20105 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20105
  have eq22556 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (M.op (M.op X1 (σ X0)) (M.op X1 (σ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 (M.op (M.op X1 (σ X0)) (M.op X1 (σ X0)))
       have i₂ := eq22077 (σ X0) X1
       grind)
    | exact superpose eq22077 eq31
    | exact resolve eq31 eq22077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq22576 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (M.op (M.op X1 (τ X0)) (M.op X1 (τ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (M.op (M.op X1 (τ X0)) (M.op X1 (τ X0)))
       have i₂ := eq22077 (τ X0) X1
       grind)
    | exact superpose eq22077 eq17
    | exact resolve eq17 eq22077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22077
  have eq22644 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (σ (M.op (M.op X1 (τ X0)) (M.op X1 (τ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq22576 X0 X1
       have i₂ := eq92 X0
       grind)
    | exact superpose eq92 eq22576
    | exact resolve eq22576 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22576
  have eq22663 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (τ (M.op (M.op X1 (σ X0)) (M.op X1 (σ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq22556 X0 X1
       have i₂ := eq93 X0
       grind)
    | exact superpose eq93 eq22556
    | exact resolve eq22556 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22556
  have eq154612 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X0)) ≠ (σ (k X0 (k X1 X2))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ (k X1 X2))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq6167 X1 X0 X2 (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6167
  have eq154613 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) ≠ (σ (k X0 (k X1 X2))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ (k X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq154612 X0 X1 X2
       have i₂ := eq96 X0
       grind)
    | exact superpose eq96 eq154612
    | (have j0 := eq154612 X0 X1 X2
       grind)
    | exact resolve eq154612 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154612
  have eq154685 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) ≠ (σ (k X0 (k X1 X2))) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ (k X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq154613 X0 X1 X2
       have i₂ := eq96 X0
       grind)
    | exact superpose eq96 eq154613
    | (have j0 := eq154613 X0 X1 X2
       grind)
    | exact resolve eq154613 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154613
  have eq439042 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (σ (k (τ X0) (k X1 X2))) ∨ (M.op X0 X0) = (M.op (σ (τ X0)) (σ (k X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq154685 (τ X0) X1 X2
       have i₂ := eq92 X0
       grind)
    | exact superpose eq92 eq154685
    | exact resolve eq154685 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq154685
  have eq439548 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (k X0 (σ (k X1 X2))) ∨ (M.op X0 X0) = (M.op (σ (τ X0)) (σ (k X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq439042 X0 X1 X2
       have i₂ := eq17 X0 (k X1 X2)
       grind)
    | exact superpose eq17 eq439042
    | (have j0 := eq439042 X0 X1 X2
       grind)
    | exact resolve eq439042 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq439042
  have eq439669 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (k X0 (σ (k X1 X2))) ∨ (M.op X0 X0) = (M.op X0 (σ (k X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq439548 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq439548
    | (have j0 := eq439548 X0 X1 X2
       grind)
    | exact resolve eq439548 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439548
  have eq439837 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X1 (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq439669 X0 X0 X0
       have i₂ := eq44 X0
       grind)
    | exact superpose eq44 eq439669
    | (have r₁ := eq439669 (σ (k X1 x)) X1 x
       have r₂ := eq44 (σ (k X1 x))
       grind)
    | exact resolve eq439669 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq440013 : ∀ X0 X1 X2 : G, (M.op X2 X2) ≠ (k X2 (σ (τ (k X0 X1)))) ∨ (M.op X2 X2) = (M.op X2 (σ (τ (k X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq439669 X0 (τ X1) (τ X0)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq439669
    | exact resolve eq439669 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq439669
  have eq440236 : ∀ X0 X1 X2 : G, (k X2 (k X0 X1)) ≠ (M.op X2 X2) ∨ (M.op X2 X2) = (M.op X2 (σ (τ (k X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq440013 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq440013
    | (have j0 := eq440013 X0 X1 X2
       grind)
    | exact resolve eq440013 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440013
  have eq440288 : ∀ X0 X1 X2 : G, (k X2 (k X0 X1)) ≠ (M.op X2 X2) ∨ (M.op X2 X2) = (M.op X2 (k X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq440236 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq440236
    | (have j0 := eq440236 X0 X1 X2
       grind)
    | exact resolve eq440236 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440236
  have eq440314 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) ≠ (M.op X1 X1) ∨ (M.op X1 (M.op X0 X0)) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq440288 X0 X0 x
       have i₂ := eq44 X0
       grind)
    | exact superpose eq44 eq440288
    | (have r₁ := eq440288 X0 X1 (k X0 X1)
       have r₂ := eq44 (k X0 X1)
       grind)
    | exact resolve eq440288 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq440288
  have eq500218 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 (σ (M.op (M.op X1 (τ X0)) (M.op X1 (τ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq439837 (M.op X1 (τ X0)) X0
       have i₂ := eq22644 X0 X1
       grind)
    | exact superpose eq22644 eq439837
    | (have j0 := eq439837 (M.op X1 (τ X0)) X0
       grind)
    | (have r₁ := eq439837 (M.op X1 (τ X0)) X0
       have r₂ := eq22644 X0 X1
       grind)
    | exact resolve eq439837 eq22644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22644 eq439837
  have eq500257 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (σ (M.op (M.op X1 (τ X0)) (M.op X1 (τ X0))))) := by
    intro X0 X1
    first
    | (have j0 := eq500218 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500218
  have eq500455 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X2 (σ (M.op (M.op (M.op X0 X1) (τ X2)) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq500257 X2 (M.op X0 X1)
       have i₂ := eq25 (τ X2) X1 (M.op (M.op X0 X1) (τ X2)) X0
       grind)
    | exact superpose eq25 eq500257
    | exact resolve eq500257 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500257
  have eq502005 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 (σ (M.op (M.op X1 (τ X0)) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq500455 (M.op X1 (τ X0)) X2 X0
       have i₂ := eq1556 X1 (τ X0) X2 X0
       grind)
    | exact superpose eq1556 eq500455
    | exact resolve eq500455 eq1556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1556 eq500455
  have eq504662 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op (M.op X0 X0) X4)) = (M.op X1 (σ (M.op (M.op X2 (τ X0)) X3))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq25 X4 (σ (M.op (M.op X2 (τ X0)) X3)) X1 X0
       have i₂ := eq502005 X0 X2 X3
       grind)
    | exact superpose eq502005 eq25
    | exact resolve eq25 eq502005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502005
  have eq505283 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X1 (σ (M.op (M.op X2 (τ X0)) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq504662 X0 X1 X2 X3 x
       have i₂ := eq25 x X0 X1 X0
       grind)
    | exact superpose eq25 eq504662
    | exact resolve eq504662 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq504662
  have eq511511 : ∀ X0 X1 X2 X3 : G, (M.op X1 (σ X0)) = (M.op X1 (σ (M.op (M.op X2 X0) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq505283 (σ X0) X1 X2 X3
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq505283
    | exact resolve eq505283 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505283
  have eq516445 : ∀ X0 X1 X2 X3 : G, (M.op X1 (σ y)) = (M.op X1 (σ (M.op (M.op X0 x) X2))) ∨ (M.op X3 (σ x)) = (M.op X3 (σ y)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq511511 y X1 X0 X2
       have i₂ := eq3091 X3 X0
       grind)
    | exact superpose eq3091 eq511511
    | (have j1 := eq3091 X3 X2
       grind)
    | exact resolve eq511511 eq3091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3091
  have eq517738 : ∀ X1 X3 : G, (M.op X1 (σ x)) = (M.op X1 (σ y)) ∨ (M.op X3 (σ x)) = (M.op X3 (σ y)) := by
    intro X1 X3
    first
    | (have i₁ := eq516445 x X1 x X3
       have i₂ := eq511511 x X1 x x
       grind)
    | exact superpose eq511511 eq516445
    | (have j0 := eq516445 x X1 x X1
       grind)
    | exact resolve eq516445 eq511511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511511 eq516445
  have eq663688 : ∀ X0 : G, (M.op X0 (σ x)) ≠ (M.op X0 (σ x)) ∨ (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq517738 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517738
  have eq663689 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq663688 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663688
  have eq665044 : (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq663689 (σ y)
       have i₂ := eq96 y
       grind)
    | exact superpose eq96 eq663689
    | exact resolve eq663689 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq665627 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq663689 (σ x)
       grind)
    | exact superpose eq663689 eq16
    | exact resolve eq16 eq663689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663689
  have eq665977 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq665627
       have i₂ := eq96 x
       grind)
    | exact superpose eq96 eq665627
    | exact resolve eq665627 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq665627
  have eq668543 : (M.op x x) = (k x (τ (M.op (σ (M.op y y)) (σ (M.op y y))))) := by
    first
    | (have i₁ := eq22663 x (σ y)
       have i₂ := eq665044
       grind)
    | exact superpose eq665044 eq22663
    | exact resolve eq22663 eq665044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22663 eq665044
  have eq668683 : (M.op x x) = (k x (M.op (M.op y y) (M.op y y))) := by
    first
    | (have i₁ := eq668543
       have i₂ := eq93 (M.op y y)
       grind)
    | exact superpose eq93 eq668543
    | exact resolve eq668543 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq668543
  have eq680756 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (M.op x (M.op (M.op y y) (M.op y y))) := by
    first
    | (have i₁ := eq440314 (M.op y y) x
       have i₂ := eq668683
       grind)
    | exact superpose eq668683 eq440314
    | (have j0 := eq440314 (M.op y y) x
       grind)
    | (have r₁ := eq440314 (M.op y y) x
       have r₂ := eq668683
       grind)
    | exact resolve eq440314 eq668683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440314 eq668683
  have eq680868 : (M.op x x) = (M.op x (M.op (M.op y y) (M.op y y))) := by grind
  clear eq680756
  have eq680948 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq680868
       have i₂ := eq25 (M.op y y) y x y
       grind)
    | exact superpose eq25 eq680868
    | exact resolve eq680868 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq680868
  have eq682394 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq665977
       have i₂ := eq680948
       grind)
    | exact superpose eq680948 eq665977
    | exact resolve eq665977 eq680948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665977 eq680948
  have eq682510 : False := by grind
  exact eq682510

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_pyy_pxy_pyy_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq22 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq22 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq22 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq22 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq27 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
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
  have eq29 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
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
  have eq30 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
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
  have eq32 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq29 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq33 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq27 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq34 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq36 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq30 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq30 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq30 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq37 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq32 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq32 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq32 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq39 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq34 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq34 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq41 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq36 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq36
    | (have j0 := eq36 X0 X1
       grind)
    | exact resolve eq36 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq42 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq37
    | (have j0 := eq37 X0 X1
       grind)
    | exact resolve eq37 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq37
  have eq44 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X1
       have j1 := eq41 X0 X1
       grind)
    | (have r₁ := eq42 X0 X1
       have r₂ := eq41 X0 X1
       grind)
    | exact resolve eq42 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq42
  have eq117 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq39 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq121 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq117 X0 X1
       have j1 := eq44 X0 X1
       grind)
    | (have r₁ := eq117 X0 X1
       have r₂ := eq44 X0 X1
       grind)
    | (have r₁ := eq117 X0 X0
       have r₂ := eq44 X0 X0
       grind)
    | exact resolve eq117 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq117
  have eq223 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq121 (σ X0) (σ X1)
       grind)
    | exact superpose eq121 eq15
    | exact resolve eq15 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq230 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq223 X0 X1
       have i₂ := eq121 X0 X1
       grind)
    | exact superpose eq121 eq223
    | exact resolve eq223 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq223
  have eq232 : False := by grind
  exact eq232

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_x_pxy_pxx_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X0 := by
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
  have eq19 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X3 X1) X0) X0
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 X0 X1 X2 X3
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq19
    | exact resolve eq19 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq25 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq34 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X2 X1) X0) ∨ (M.op (M.op (M.op X2 X1) X0) X0) = (k (M.op (M.op X2 X1) X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op (M.op X2 X1) X0) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 (M.op (M.op X2 X1) X0) X0
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq84 : ∀ X0 X1 : G, (M.op (σ X1) X0) = X0 ∨ (M.op X0 (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
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
  have eq3228 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (k (τ X1) (τ X0)) = (τ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq84 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq84
    | exact resolve eq84 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3255 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (σ X1)
       have i₂ := eq84 X0 X1
       grind)
    | exact superpose eq84 eq12
    | (have j0 := eq12 X0 (σ X1)
       have j1 := eq84 X0 X1
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq84 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X1)
       have r₂ := eq84 (σ X1) X1
       grind)
    | exact resolve eq12 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3272 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k (τ (σ X0)) X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq84 (σ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3273 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k (τ (σ X0)) X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq3272 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3272
  have eq3274 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 (σ X1)) = X0 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3255 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3255
  have eq3275 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq3273 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3273
    | (have j0 := eq3273 X0
       grind)
    | exact resolve eq3273 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3273
  have eq3280 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3228 X0 X1
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq3228
    | (have j0 := eq3228 X0 X1
       grind)
    | exact resolve eq3228 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3228
  have eq3303 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k (σ X0) (σ X0)) ∨ (k X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq12 (σ X0) (σ X0)
       have i₂ := eq3275 X0
       grind)
    | exact superpose eq3275 eq12
    | (have j1 := eq3275 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq3275 X0
       grind)
    | exact resolve eq12 eq3275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3275
  have eq3317 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ X0)) ∨ (k X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq3303 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3303
  have eq3319 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (k X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq3317 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq3317
    | (have j0 := eq3317 X0
       grind)
    | exact resolve eq3317 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3317
  have eq3810 : ∀ X0 : G, (τ (σ X0)) = (k X0 X0) ∨ (k X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq3319 X0
       grind)
    | exact superpose eq3319 eq10
    | (have j1 := eq3319 X0
       grind)
    | exact resolve eq10 eq3319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3319
  have eq3866 : ∀ X0 : G, (k X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3810 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3810
    | (have j0 := eq3810 X0
       grind)
    | exact resolve eq3810 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3810
  have eq4088 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X0))
       have i₂ := eq3866 X0
       grind)
    | exact superpose eq3866 eq11
    | (have j1 := eq3866 X0
       grind)
    | exact resolve eq11 eq3866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3866
  have eq4150 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq4088 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4088
    | (have j0 := eq4088 (τ X0)
       grind)
    | exact resolve eq4088 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4088
  have eq4214 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq4150 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq4150
    | (have j0 := eq4150 X0
       grind)
    | exact resolve eq4150 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4150
  have eq4220 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq4214 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4214
    | (have j0 := eq4214 X0
       grind)
    | exact resolve eq4214 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4214
  have eq4221 : ∀ X0 : G, (τ X0) = (τ (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq4220 X0
       have i₂ := eq35 X0 X0
       grind)
    | exact superpose eq35 eq4220
    | (have j0 := eq4220 X0
       grind)
    | exact resolve eq4220 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4220
  have eq16798 : ∀ X0 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4221 X0
       have i₂ := eq3280 X0 X0
       grind)
    | exact superpose eq3280 eq4221
    | (have j0 := eq4221 X0
       have j1 := eq3280 X0 X0
       grind)
    | exact resolve eq4221 eq3280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3280 eq4221
  have eq16890 : ∀ X0 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq16798 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16798
  have eq16950 : ∀ X0 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq16890 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq16890 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq16890 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16890
  have eq17121 : ∀ X0 : G, (σ (τ X0)) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op X0 X0)
       have i₂ := eq16950 X0
       grind)
    | exact superpose eq16950 eq11
    | (have j1 := eq16950 X0
       grind)
    | exact resolve eq11 eq16950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16950
  have eq17242 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq17121 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq17121
    | (have j0 := eq17121 X0
       grind)
    | exact resolve eq17121 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17121
  have eq17253 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq17242 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq17242 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq17242 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17242
  have eq17338 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq17253 (σ X0)
       grind)
    | exact superpose eq17253 eq15
    | exact resolve eq15 eq17253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17414 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq17338 X0
       have i₂ := eq17253 X0
       grind)
    | exact superpose eq17253 eq17338
    | exact resolve eq17338 eq17253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17253 eq17338
  have eq183600 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 (σ X1))
       have i₂ := eq3274 X0 X1
       grind)
    | exact superpose eq3274 eq11
    | (have j1 := eq3274 X0 X1
       grind)
    | exact resolve eq11 eq3274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3274
  have eq183771 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq183600 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq183600
    | (have j0 := eq183600 X0 X1
       grind)
    | exact resolve eq183600 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq183600
  have eq183772 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq183771 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183771
  have eq183926 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq183772 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq183772
    | exact resolve eq183772 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184157 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq183772 (σ x) y
       grind)
    | exact superpose eq183772 eq16
    | (have j1 := eq183772 (σ x) y
       grind)
    | exact resolve eq16 eq183772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183772
  have eq184234 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq184157
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq184157
    | exact resolve eq184157 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184157
  have eq184444 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq183926 X1 X0
       grind)
    | exact superpose eq183926 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq183926 X1 X0
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq183926 X0 X1
       grind)
    | exact resolve eq13 eq183926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184447 : ∀ X0 X1 X2 X3 : G, (M.op X0 X2) = (k X0 X2) ∨ (M.op X1 X2) = (M.op X1 (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21 X3 X2 X1 X0
       have i₂ := eq183926 X2 X0
       grind)
    | exact superpose eq183926 eq21
    | (have j1 := eq183926 X2 X0
       grind)
    | exact resolve eq21 eq183926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184508 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op X0 X1)) ∨ (M.op (M.op X0 X1) X3) = (k (M.op X0 X1) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21 X3 X1 X2 X0
       have i₂ := eq183926 X3 (M.op X0 X1)
       grind)
    | exact superpose eq183926 eq21
    | (have j1 := eq183926 X3 (M.op X0 X1)
       grind)
    | exact resolve eq21 eq183926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184509 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 X1) ∨ (M.op (M.op X0 X1) X2) = (k (M.op X0 X1) X2) ∨ (M.op (M.op X0 X1) X2) = (k (M.op X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34 X0 X1 X2
       have i₂ := eq183926 X0 (M.op X2 X1)
       grind)
    | exact superpose eq183926 eq34
    | (have j1 := eq183926 X2 (M.op X0 X1)
       grind)
    | (have r₁ := eq34 X0 X1 X0
       have r₂ := eq183926 X0 (M.op X0 X1)
       grind)
    | exact resolve eq34 eq183926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq184664 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 X1) ∨ (M.op (M.op X0 X1) X2) = (k (M.op X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq184509 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184509
  have eq184669 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq184444 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184444
  have eq184727 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq184669 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq184669 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq184669 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184669
  have eq184810 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq184727 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq184727
    | exact resolve eq184727 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184961 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (k X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq184727 X0 (τ X1)
       grind)
    | exact superpose eq184727 eq18
    | (have j1 := eq184727 X0 (τ X1)
       grind)
    | exact resolve eq18 eq184727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq185182 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq184727 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184727
  have eq185369 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq184810 X0 X1
       have i₂ := eq17414 X0
       grind)
    | exact superpose eq17414 eq184810
    | (have j0 := eq184810 X0 X1
       grind)
    | exact resolve eq184810 eq17414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184810
  have eq187354 : ∀ X0 X1 X2 X3 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 (σ X1)) = (M.op X2 (M.op (σ X0) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq184447 (σ X0) X2 (σ X1) X3
       grind)
    | exact superpose eq184447 eq15
    | (have j1 := eq184447 (σ X0) X2 (σ X1) X3
       grind)
    | exact resolve eq15 eq184447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184447
  have eq188430 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq184234
       have i₂ := eq183926 y x
       grind)
    | exact superpose eq183926 eq184234
    | (have j1 := eq183926 y x
       grind)
    | exact resolve eq184234 eq183926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184234
  have eq188431 : (M.op x y) = (k x y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by grind
  clear eq188430
  have eq190760 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq184664 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184664
  have eq191970 : ∀ X0 X1 : G, (k (τ (M.op (σ X0) X1)) X0) = (τ (M.op (M.op (σ X0) X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq25 (M.op (σ X0) X1) X0
       have i₂ := eq190760 (σ X0) X1
       grind)
    | exact superpose eq190760 eq25
    | exact resolve eq25 eq190760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq190760
  have eq208890 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq191970 X1 X0
       have i₂ := eq84 X0 X1
       grind)
    | exact superpose eq84 eq191970
    | (have j1 := eq84 X0 X1
       grind)
    | exact resolve eq191970 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq191970
  have eq209187 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq208890 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208890
  have eq211488 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq209187 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq209187
    | exact resolve eq209187 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209187
  have eq211897 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq211488 X0 X1
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq211488
    | (have j0 := eq211488 X0 X1
       grind)
    | exact resolve eq211488 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq211488
  have eq212317 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq211897 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq211897
    | (have j0 := eq211897 (σ X1) (σ X0)
       grind)
    | exact resolve eq211897 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211897
  have eq212718 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq212317 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq212317
    | (have j0 := eq212317 X0 X1
       grind)
    | exact resolve eq212317 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212317
  have eq232039 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq184961 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq184961
    | exact resolve eq184961 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184961
  have eq232575 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq232039 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq232039
    | (have j0 := eq232039 X0 X1
       grind)
    | exact resolve eq232039 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232039
  have eq314185 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq212718 X0 X1
       grind)
    | exact superpose eq212718 eq11
    | (have j1 := eq212718 X0 X1
       grind)
    | exact resolve eq11 eq212718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212718
  have eq326632 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq314185 x y
       grind)
    | exact superpose eq314185 eq16
    | (have j1 := eq314185 x y
       grind)
    | exact resolve eq16 eq314185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314185
  have eq342798 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq326632
       have i₂ := eq232575 y x
       grind)
    | exact superpose eq232575 eq326632
    | (have j1 := eq232575 y x
       grind)
    | (have r₁ := eq326632
       have r₂ := eq232575 y x
       grind)
    | exact resolve eq326632 eq232575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232575
  have eq342801 : (k x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq342798
  have eq345518 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq326632
       have i₂ := eq342801
       grind)
    | exact superpose eq342801 eq326632
    | exact resolve eq326632 eq342801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326632 eq342801
  have eq345585 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq345518
  have eq469479 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq185369 x y
       grind)
    | exact superpose eq185369 eq16
    | (have j1 := eq185369 x y
       grind)
    | exact resolve eq16 eq185369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185369
  have eq470434 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq469479
       have i₂ := eq188431
       grind)
    | exact superpose eq188431 eq469479
    | exact resolve eq469479 eq188431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188431 eq469479
  have eq470449 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by grind
  clear eq470434
  have eq502319 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq470449
       grind)
    | exact superpose eq470449 eq16
    | exact resolve eq16 eq470449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470449
  have eq705300 : ∀ X0 X1 X2 X3 : G, (k X0 X3) = (M.op X0 X3) ∨ (M.op X1 X0) = (M.op X1 X2) ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq184508 X1 X0 X2 X3
       have i₂ := eq183926 X0 X1
       grind)
    | exact superpose eq183926 eq184508
    | (have j1 := eq183926 X3 X0
       grind)
    | exact resolve eq184508 eq183926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183926 eq184508
  have eq1230934 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16
       have i₂ := eq187354 x y X0 X1
       grind)
    | exact superpose eq187354 eq16
    | (have j1 := eq187354 x y X0 X1
       grind)
    | exact resolve eq16 eq187354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187354
  have eq1242960 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X2 X1) = (M.op X2 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq705300 X0 X2 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705300
  have eq1242961 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X2 X1) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1242960 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1242960
  have eq1248414 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq502319
       have i₂ := eq1242961 x y X0
       grind)
    | exact superpose eq1242961 eq502319
    | (have j1 := eq1242961 x y X0
       grind)
    | exact resolve eq502319 eq1242961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502319 eq1242961
  have eq1248437 : ∀ X0 : G, (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq1248414 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1248414
  have eq1252662 : ∀ X0 : G, (M.op x y) = (τ (σ (M.op x x))) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq1248437 X0
       grind)
    | exact superpose eq1248437 eq10
    | (have j1 := eq1248437 X0
       grind)
    | exact resolve eq10 eq1248437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1248437
  have eq1253107 : ∀ X0 : G, (M.op x y) = (M.op x x) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq1252662 X0
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq1252662
    | (have j0 := eq1252662 x
       grind)
    | exact resolve eq1252662 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1252662
  have eq1256957 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have j0 := eq1253107 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1253107
  have eq1256958 : (M.op x y) = (M.op x x) := by grind
  clear eq1256957
  have eq1256986 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq345585
       have i₂ := eq1256958
       grind)
    | exact superpose eq1256958 eq345585
    | exact resolve eq345585 eq1256958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345585
  have eq1257006 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x x) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq21 X1 y X0 x
       have i₂ := eq1256958
       grind)
    | exact superpose eq1256958 eq21
    | exact resolve eq21 eq1256958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1257036 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq185182 x y
       have i₂ := eq1256958
       grind)
    | exact superpose eq1256958 eq185182
    | (have j0 := eq185182 x x
       grind)
    | (have r₁ := eq185182 x y
       have r₂ := eq1256958
       grind)
    | exact resolve eq185182 eq1256958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185182 eq1256958
  have eq1257063 : (k x y) = (M.op x x) := by grind
  clear eq1257036
  have eq1257064 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1256986
  have eq1257065 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq1257006 X0 x
       have i₂ := eq21 x x X0 x
       grind)
    | exact superpose eq21 eq1257006
    | exact resolve eq1257006 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1257006
  have eq1260932 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1230934 X0 X1
       have i₂ := eq1257063
       grind)
    | exact superpose eq1257063 eq1230934
    | (have j0 := eq1230934 X0 X1
       grind)
    | exact resolve eq1230934 eq1257063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1230934 eq1257063
  have eq1261030 : ∀ X0 X1 : G, (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1260932 X0 X1
       have i₂ := eq1257065 x
       grind)
    | exact superpose eq1257065 eq1260932
    | (have j0 := eq1260932 X0 X1
       grind)
    | exact resolve eq1260932 eq1257065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1260932
  have eq1261031 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1261030 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1261030
  have eq1265814 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1257064
       grind)
    | exact superpose eq1257064 eq16
    | exact resolve eq16 eq1257064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1265942 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1265814
       have i₂ := eq1257065 x
       grind)
    | exact superpose eq1257065 eq1265814
    | exact resolve eq1265814 eq1257065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1257065 eq1265814
  have eq1275759 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1261031 X0 (σ y)
       have i₂ := eq1257064
       grind)
    | exact superpose eq1257064 eq1261031
    | exact resolve eq1261031 eq1257064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1261031
  have eq1278198 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1257064
       have i₂ := eq1275759 (σ x)
       grind)
    | exact superpose eq1275759 eq1257064
    | exact resolve eq1257064 eq1275759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1257064 eq1275759
  have eq1278371 : (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq1278198
       have i₂ := eq17414 x
       grind)
    | exact superpose eq17414 eq1278198
    | exact resolve eq1278198 eq17414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17414 eq1278198
  have eq1278805 : False := by grind
  exact eq1278805

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_y_pxy_y_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X3 X1) X0) X0
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq61 X0 X1 X2 X3
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq281 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq283 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (k X0 X2) ∨ (M.op X0 X2) = X2 ∨ (M.op X1 X0) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X0 X2
       have i₂ := eq14 X0 X2
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X2
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq290 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq281 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq291 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq290 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq399 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq291 X1 X0
       grind)
    | exact superpose eq291 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq291 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq291 X0 X1
       grind)
    | exact resolve eq13 eq291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq407 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq291 (σ x) (σ y)
       grind)
    | exact superpose eq291 eq16
    | (have j1 := eq291 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq411 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq399 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399
  have eq412 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq407
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq407
    | exact resolve eq407 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407
  have eq415 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq411 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq411 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq411 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411
  have eq418 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq415 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq415
    | exact resolve eq415 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq440 : ∀ X0 X1 : G, (k (τ X0) X1) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq415 X1 (τ X0)
       grind)
    | exact superpose eq415 eq17
    | (have j1 := eq415 X1 (τ X0)
       grind)
    | exact resolve eq17 eq415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq446 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq415 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415
  have eq1091 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X1)) X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ X1)
       have i₂ := eq440 X1 (τ X0)
       grind)
    | exact superpose eq440 eq18
    | (have j1 := eq440 X1 (τ X0)
       grind)
    | exact resolve eq18 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq440
  have eq1098 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1091 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1091
    | (have j0 := eq1091 X0 X1
       grind)
    | exact resolve eq1091 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1091
  have eq1111 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1098 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1098
    | (have j0 := eq1098 X0 X1
       grind)
    | exact resolve eq1098 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1098
  have eq1114 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X1) (τ X0))) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1111 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1111
    | (have j0 := eq1111 X0 X1
       grind)
    | exact resolve eq1111 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1111
  have eq1167 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1114 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1114
    | (have j0 := eq1114 X1 (σ X0)
       grind)
    | exact resolve eq1114 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1114
  have eq1379 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1167 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1167
    | (have j0 := eq1167 X1 (σ X0)
       grind)
    | exact resolve eq1167 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1167
  have eq1429 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1379 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1379
    | (have j0 := eq1379 X0 X1
       grind)
    | exact resolve eq1379 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1379
  have eq1436 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1429 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1429
    | (have j0 := eq1429 X0 X1
       grind)
    | exact resolve eq1429 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1429
  have eq1578 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq418 x y
       grind)
    | exact superpose eq418 eq16
    | (have j1 := eq418 x y
       grind)
    | exact resolve eq16 eq418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418
  have eq1615 : (σ y) = (σ (k x y)) := by
    first
    | (have j1 := eq1436 y x
       grind)
    | (have r₁ := eq1578
       have r₂ := eq1436 y x
       grind)
    | exact resolve eq1578 eq1436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1436 eq1578
  have eq1639 : (k x y) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq1615
       grind)
    | exact superpose eq1615 eq10
    | exact resolve eq10 eq1615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1677 : y = (k x y) := by
    first
    | (have i₁ := eq1639
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1639
    | exact resolve eq1639 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1639
  have eq1683 : ∀ X0 : G, y = (M.op x y) ∨ y = (M.op x y) ∨ (M.op X0 x) = (M.op X0 (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq283 x X0 y
       have i₂ := eq1677
       grind)
    | exact superpose eq1677 eq283
    | (have j0 := eq283 x X0 y
       grind)
    | exact resolve eq283 eq1677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283
  have eq1687 : ∀ X0 : G, y = (M.op x y) ∨ (M.op X0 x) = (M.op X0 (M.op x X0)) := by
    intro X0
    first
    | (have j0 := eq1683 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1683
  have eq2115 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op X0 x) = (M.op X0 (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq412
       have i₂ := eq1687 X0
       grind)
    | exact superpose eq1687 eq412
    | (have j1 := eq1687 X0
       grind)
    | exact resolve eq412 eq1687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2126 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op X0 x) = (M.op X0 (M.op x X0)) := by
    intro X0
    first
    | (have j0 := eq2115 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2115
  have eq2127 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op X0 x) = (M.op X0 (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq2126 X0
       have i₂ := eq1615
       grind)
    | exact superpose eq1615 eq2126
    | (have j0 := eq2126 X0
       grind)
    | exact resolve eq2126 eq1615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2126
  have eq7105 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ y) ∨ (M.op X0 x) = (M.op X0 (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq2127 X0
       grind)
    | exact superpose eq2127 eq16
    | (have j1 := eq2127 X0
       grind)
    | exact resolve eq16 eq2127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2127
  have eq7144 : ∀ X0 X1 : G, (σ y) ≠ (σ y) ∨ (M.op X0 x) = (M.op X0 (M.op x X0)) ∨ (M.op X1 x) = (M.op X1 (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7105 X0
       have i₂ := eq1687 X1
       grind)
    | exact superpose eq1687 eq7105
    | (have j0 := eq7105 X0
       have j1 := eq1687 X0
       grind)
    | exact resolve eq7105 eq1687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1687 eq7105
  have eq7155 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op x X0)) ∨ (M.op X1 x) = (M.op X1 (M.op x X1)) := by
    intro X0 X1
    first
    | (have j0 := eq7144 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7144
  have eq17392 : ∀ X0 : G, (M.op X0 x) ≠ (M.op X0 x) ∨ (M.op X0 x) = (M.op X0 (M.op x X0)) := by
    intro X0
    first
    | (have j0 := eq7155 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7155
  have eq17393 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op x X0)) := by
    intro X0
    first
    | (have j0 := eq17392 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17392
  have eq17401 : ∀ X0 : G, (M.op x X0) = (k x X0) ∨ (M.op X0 X0) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq17393 X0
       have i₂ := eq291 x X0
       grind)
    | exact superpose eq291 eq17393
    | (have j1 := eq291 x X0
       grind)
    | exact resolve eq17393 eq291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18083 : y = (M.op x y) ∨ (M.op y x) = (M.op y y) := by
    first
    | (have i₁ := eq1677
       have i₂ := eq17401 y
       grind)
    | exact superpose eq17401 eq1677
    | (have j1 := eq17401 y
       grind)
    | exact resolve eq1677 eq17401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17401
  have eq18143 : (M.op y x) = (M.op y y) ∨ (M.op y x) = (M.op y y) := by
    first
    | (have i₁ := eq17393 y
       have i₂ := eq18083
       grind)
    | exact superpose eq18083 eq17393
    | exact resolve eq17393 eq18083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17393 eq18083
  have eq18169 : (M.op y x) = (M.op y y) := by grind
  clear eq18143
  have eq18213 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op (M.op y x) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X1 y X0 y
       have i₂ := eq18169
       grind)
    | exact superpose eq18169 eq63
    | exact resolve eq63 eq18169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18169
  have eq18230 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq18213 X0 x
       have i₂ := eq63 x x X0 y
       grind)
    | exact superpose eq63 eq18213
    | exact resolve eq18213 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq18213
  have eq18277 : ∀ X0 : G, y = (M.op X0 x) ∨ (M.op X0 x) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq291 X0 y
       have i₂ := eq18230 X0
       grind)
    | exact superpose eq18230 eq291
    | exact resolve eq291 eq18230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291
  have eq18281 : ∀ X0 : G, y ≠ (M.op X0 x) ∨ y = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq446 X0 y
       have i₂ := eq18230 X0
       grind)
    | exact superpose eq18230 eq446
    | (have j0 := eq446 X0 y
       grind)
    | exact resolve eq446 eq18230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446
  have eq18318 : (σ y) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq412
       have i₂ := eq18230 x
       grind)
    | exact superpose eq18230 eq412
    | exact resolve eq412 eq18230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412
  have eq18354 : (σ y) ≠ (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18318
       have i₂ := eq1615
       grind)
    | exact superpose eq1615 eq18318
    | exact resolve eq18318 eq1615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1615 eq18318
  have eq18481 : ∀ X0 : G, y ≠ y ∨ y = (k X0 y) ∨ (M.op X0 x) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq18281 X0
       have i₂ := eq18277 X0
       grind)
    | exact superpose eq18277 eq18281
    | (have j0 := eq18281 X0
       have j1 := eq18277 X0
       grind)
    | (have r₁ := eq18281 X0
       have r₂ := eq18277 X0
       grind)
    | exact resolve eq18281 eq18277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18281
  have eq18563 : ∀ X0 : G, y = (k X0 y) ∨ (M.op X0 x) = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq18481 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18481
  have eq18691 : ∀ X0 : G, y ≠ (M.op X0 x) ∨ (M.op X0 x) = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq18563 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18563
  have eq18694 : ∀ X0 : G, (M.op X0 x) = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq18691 X0
       have j1 := eq18277 X0
       grind)
    | (have r₁ := eq18691 X0
       have r₂ := eq18277 X0
       grind)
    | exact resolve eq18691 eq18277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18277 eq18691
  have eq18836 : y = (M.op x x) := by
    first
    | (have i₁ := eq1677
       have i₂ := eq18694 x
       grind)
    | exact superpose eq18694 eq1677
    | exact resolve eq1677 eq18694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1677 eq18694
  have eq25324 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18354
       have i₂ := eq18836
       grind)
    | exact superpose eq18836 eq18354
    | exact resolve eq18354 eq18836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18354
  have eq25329 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq25324
  have eq25339 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25329
       grind)
    | exact superpose eq25329 eq16
    | exact resolve eq16 eq25329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25329
  have eq25384 : (σ y) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq25339
       have i₂ := eq18230 x
       grind)
    | exact superpose eq18230 eq25339
    | exact resolve eq25339 eq18230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18230 eq25339
  have eq25390 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq25384
       have i₂ := eq18836
       grind)
    | exact superpose eq18836 eq25384
    | exact resolve eq25384 eq18836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18836 eq25384
  have eq25391 : False := by grind
  exact eq25391

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(Y,X) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_pyy_pxy_pxx_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq91 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
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
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 (M.op X1 X1) X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) X2)) = (M.op X2 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X0 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq9 X0 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq91 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq106 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq102 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq102 X1 (k X1 X1)
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq102 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq102 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq108 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) X2)) = (M.op X2 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq99 X0 X1 X2
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq99 X1 X0 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq99 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq115 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq105 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq105 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq105 X0 (M.op X1 (M.op X0 X0))
       have r₂ := eq12 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq105 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq105 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq120 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq108 X0 X1 X2
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq108
    | (have j0 := eq108 X0 X1 X2
       grind)
    | exact resolve eq108 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq124 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq115 X0 X1
       have j1 := eq106 X0 X1
       grind)
    | (have r₁ := eq115 X0 X0
       have r₂ := eq106 X0 (k X0 X0)
       grind)
    | (have r₁ := eq115 X0 X1
       have r₂ := eq106 X0 X1
       grind)
    | (have r₁ := eq115 X0 (M.op X0 X0)
       have r₂ := eq106 X0 (M.op X0 X0)
       grind)
    | exact resolve eq115 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq115
  have eq365 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq124 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq367 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq365 X0 X1
       have j1 := eq120 X1 X0 x
       grind)
    | (have r₁ := eq365 X0 X1
       have r₂ := eq120 X0 X1 X0
       grind)
    | (have r₁ := eq365 X1 X0
       have r₂ := eq120 X0 X1 X1
       grind)
    | exact resolve eq365 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq365
  have eq388 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq367 (σ X0) (σ X1)
       grind)
    | exact superpose eq367 eq15
    | exact resolve eq15 eq367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq395 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq388 X0 X1
       have i₂ := eq367 X0 X1
       grind)
    | exact superpose eq367 eq388
    | exact resolve eq388 eq367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367 eq388
  have eq501 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq395 x y
       grind)
    | exact superpose eq395 eq16
    | (have r₁ := eq16
       have r₂ := eq395 x y
       grind)
    | exact resolve eq16 eq395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395
  have eq517 : False := by grind
  exact eq517

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(Y,Y) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyy_x_pxy_pxx_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
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
  have eq40 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10
    | (have j0 := eq10 X0 x
       grind)
    | exact resolve eq10 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 X0 y
       grind)
    | exact resolve eq10 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 : G, (σ (k x (τ X0))) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq36 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq36
    | exact resolve eq36 eq15
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
  have eq46 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq21
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
  clear eq44
  have eq51 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x y) X0)) := by
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
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op (M.op X3 X1) X0) X0
       have i₂ := eq14 X0 X1 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X0 X1 X2 X3
       have i₂ := eq14 X2 X1 X0
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq63 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq46 eq16
    | exact resolve eq16 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X2 X1) X0) ∨ (M.op (M.op (M.op X2 X1) X0) X0) = (k (M.op (M.op X2 X1) X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op X2 X1) X0) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 (M.op (M.op X2 X1) X0) X0
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq37 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq37
    | exact resolve eq37 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq75 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq76 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
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
    | (have r₁ := eq11 (M.op X1 (M.op X1 X1)) X1
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq16
    | exact resolve eq16 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq76 eq16
    | exact resolve eq16 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq77 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq77
    | (have j0 := eq77 (σ X0) (σ X1)
       grind)
    | exact resolve eq77 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq77 x y
       grind)
    | exact superpose eq77 eq45
    | (have j1 := eq77 x y
       grind)
    | exact resolve eq45 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
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
  have eq110 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq109
    | exact resolve eq109 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq128 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  have eq129 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq38 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq38
    | (have j0 := eq38 y
       grind)
    | exact resolve eq38 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq139 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq128 eq16
    | exact resolve eq16 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq146 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq129 eq16
    | exact resolve eq16 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq77 (σ X0) sF3
       grind)
    | exact superpose eq77 eq41
    | (have j1 := eq77 (σ X0) (σ y)
       grind)
    | exact resolve eq41 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq207 : ∀ X0 : G, (M.op X0 y) ≠ (M.op (M.op x y) X0) ∨ (M.op (M.op (M.op x y) X0) X0) = (k (M.op (M.op x y) X0) X0) := by
    intro X0
    first
    | exact superpose eq51 eq13
    | (have j0 := eq13 (M.op (M.op x y) X0) X0
       grind)
    | exact resolve eq13 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq208 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x y) X0)) = (M.op X1 (M.op (M.op X0 y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x y) X0)) = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq208 X0 X1
       have i₂ := eq14 X1 y X0
       grind)
    | exact superpose eq14 eq208
    | exact resolve eq208 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq235 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (k x (τ X0))
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq16
    | exact resolve eq16 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq301 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X0 X1
       have i₂ := eq77 (τ X0) X1
       grind)
    | exact superpose eq77 eq35
    | (have j1 := eq77 (τ X0) X1
       grind)
    | exact resolve eq35 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq304 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq327 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq39 X1 X0
       have i₂ := eq77 X0 (τ X1)
       grind)
    | exact superpose eq77 eq39
    | (have j1 := eq77 X0 (τ X1)
       grind)
    | exact resolve eq39 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq338 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq488 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq304 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq304
    | (have j0 := eq304 X0 x
       grind)
    | exact resolve eq304 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304
  have eq586 : ∀ X0 X1 X2 X3 : G, (M.op X2 (σ X1)) = (M.op X2 (M.op (σ (k X0 X1)) X3)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq55 X3 (σ X1) X2 (σ X0)
       have i₂ := eq93 X0 X1
       grind)
    | exact superpose eq93 eq55
    | (have j1 := eq93 X0 X1
       grind)
    | exact resolve eq55 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq587 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq93 X0 X1
       grind)
    | exact superpose eq93 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq93 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq93 X0 X0
       grind)
    | exact resolve eq13 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq592 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq587 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq587
    | (have j0 := eq587 X0 X1
       grind)
    | exact resolve eq587 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587
  have eq644 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq338 X0 X1
       have i₂ := eq77 (σ X0) X1
       grind)
    | exact superpose eq77 eq338
    | (have j1 := eq77 (σ X0) X1
       grind)
    | exact resolve eq338 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq674 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq110 eq77
    | (have j0 := eq77 (σ x) (σ y)
       grind)
    | exact resolve eq77 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq675 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq674
    | exact resolve eq674 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674
  have eq678 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq675
       have r₂ := eq28
       grind)
    | exact resolve eq675 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq675
  have eq680 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X1)) ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | exact superpose eq678 eq55
    | exact resolve eq55 eq678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq681 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq678 eq13
    | exact resolve eq13 eq678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq683 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) := by grind
  have eq738 : ∀ X0 X1 : G, (M.op (M.op X0 X1) y) ≠ (M.op (M.op (M.op x y) (M.op X0 X1)) X1) ∨ (M.op (M.op (M.op X0 X1) y) (M.op (M.op x y) (M.op X0 X1))) = (k (M.op (M.op X0 X1) y) (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1
    first
    | exact superpose eq51 eq67
    | exact resolve eq67 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq749 : ∀ X0 X1 : G, (M.op (M.op X0 X1) y) ≠ (M.op (M.op (M.op x y) (M.op X0 X1)) X1) ∨ (k (M.op (M.op X0 X1) y) (M.op (M.op x y) (M.op X0 X1))) = (M.op (M.op (M.op X0 X1) y) y) := by
    intro X0 X1
    first
    | exact superpose eq210 eq738
    | (have j0 := eq738 X0 X1
       grind)
    | exact resolve eq738 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq738
  have eq759 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq683 eq110
    | exact resolve eq110 eq683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683
  have eq762 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq759
  have eq766 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq762 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq762
       grind)
    | exact resolve eq13 eq762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762
  have eq768 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq766
  have eq769 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq768
    | exact resolve eq768 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768
  have eq800 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq769 eq110
    | exact resolve eq110 eq769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq769
  have eq803 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq800
  have eq807 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq803
       have r₂ := eq28
       grind)
    | exact resolve eq803 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803
  have eq809 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq807 eq680
    | exact resolve eq680 eq807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680 eq807
  have eq816 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq809 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq809
  have eq875 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq816 eq678
    | exact resolve eq678 eq816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq878 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op y y) := by grind
  clear eq875
  have eq2220 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ X0) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq816 eq186
    | (have j0 := eq186 X0
       grind)
    | exact resolve eq186 eq816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186 eq816
  have eq2271 : (σ (k y y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2220 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq2220
    | (have j0 := eq2220 y
       grind)
    | exact resolve eq2220 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2220
  have eq2286 : (k (σ y) (σ y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2271
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq2271
    | exact resolve eq2271 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2271
  have eq2303 : (k y y) = (τ (M.op (σ y) (σ (M.op x y)))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq2286 eq87
    | exact resolve eq87 eq2286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2286
  have eq2435 : (τ (σ x)) = (k y y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq878 eq2303
    | exact resolve eq2303 eq878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq878 eq2303
  have eq2460 : (τ (σ x)) = (k y y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq2435
  have eq2462 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq2460
    | exact resolve eq2460 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2460
  have eq2465 : (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq2462 eq678
    | exact resolve eq678 eq2462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678 eq2462
  have eq2479 : x = (k y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq2465
  have eq2483 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq2479
       grind)
    | exact superpose eq2479 eq75
    | exact resolve eq75 eq2479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2479
  have eq2487 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2483
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq2483
    | exact resolve eq2483 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2483
  have eq2488 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq2487
       have r₂ := eq681
       grind)
    | exact resolve eq2487 eq681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681 eq2487
  have eq2493 : (τ (σ x)) = (k y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq2488 eq87
    | exact resolve eq87 eq2488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2488
  have eq2500 : x = (k y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq2493
    | exact resolve eq2493 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2493
  have eq2503 : x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq77 y y
       have i₂ := eq2500
       grind)
    | exact superpose eq2500 eq77
    | (have j0 := eq77 x y
       grind)
    | exact resolve eq77 eq2500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2504 : y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq2503
  have eq2513 : y ≠ y ∨ y = (k y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq2504
       grind)
    | exact superpose eq2504 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq2504
       grind)
    | exact resolve eq13 eq2504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2515 : x ≠ y ∨ x = (M.op y y) := by grind
  clear eq2504
  have eq2516 : y = (k y y) ∨ x = (M.op y y) := by grind
  clear eq2513
  have eq2612 : x = y ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2500
       have i₂ := eq2516
       grind)
    | exact superpose eq2516 eq2500
    | exact resolve eq2500 eq2516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2500 eq2516
  have eq2618 : x = y ∨ x = (M.op y y) := by grind
  clear eq2612
  have eq2624 : x = (M.op y y) := by
    first
    | (have r₁ := eq2618
       have r₂ := eq2515
       grind)
    | exact resolve eq2618 eq2515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2515 eq2618
  have eq2726 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X1 y X0 y
       have i₂ := eq2624
       grind)
    | exact superpose eq2624 eq55
    | exact resolve eq55 eq2624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2727 : x ≠ y ∨ x = (k y y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq2624
       grind)
    | exact superpose eq2624 eq13
    | exact resolve eq13 eq2624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2831 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq2726 X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq2726
    | (have j0 := eq2726 X0 y
       grind)
    | exact resolve eq2726 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3002 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (k (M.op x y) X0) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq2831 eq13
    | (have j0 := eq13 (M.op x y) X0
       grind)
    | (have r₁ := eq13 (M.op x y) x
       have r₂ := eq2831 x
       grind)
    | exact resolve eq13 eq2831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3043 : (M.op x y) ≠ (M.op x y) ∨ (k (M.op x y) x) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq3002 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq3002
    | (have j0 := eq3002 x
       grind)
    | (have r₁ := eq3002 x
       have r₂ := eq19
       grind)
    | exact resolve eq3002 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3044 : x ≠ (M.op x y) ∨ (k (M.op x y) y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq3002 y
       have i₂ := eq2624
       grind)
    | exact superpose eq2624 eq3002
    | (have j0 := eq3002 y
       grind)
    | exact resolve eq3002 eq2624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3002
  have eq3046 : (k (M.op x y) x) = (M.op (M.op x y) x) := by grind
  clear eq3043
  have eq3898 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq301 (σ X0) X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq301
    | exact resolve eq301 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3937 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (σ (M.op (τ X0) y)) ∨ (τ X0) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq2831 eq301
    | (have j0 := eq301 X0 (M.op x y)
       grind)
    | exact resolve eq301 eq2831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301
  have eq3974 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (σ (M.op (τ X0) y)) ∨ (τ X0) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq21 eq3937
    | (have j0 := eq3937 X0
       grind)
    | exact resolve eq3937 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3937
  have eq3989 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3898 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq3898
    | (have j0 := eq3898 X0 X1
       grind)
    | exact resolve eq3898 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3898
  have eq3990 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (σ (M.op (τ X0) y)) ∨ (τ X0) = (M.op (M.op x y) y) := by
    intro X0
    first
    | exact superpose eq2831 eq3974
    | (have j0 := eq3974 X0
       grind)
    | exact resolve eq3974 eq2831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3974
  have eq4063 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op (M.op x y) y) := by
    first
    | exact superpose eq29 eq3990
    | exact resolve eq3990 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4064 : (k (σ y) (σ (M.op x y))) = (σ (M.op y y)) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq30 eq3990
    | exact resolve eq3990 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3990
  have eq4099 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq4064
       have i₂ := eq2624
       grind)
    | exact superpose eq2624 eq4064
    | exact resolve eq4064 eq2624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4064
  have eq4100 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq4063
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq4063
    | exact resolve eq4063 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4063
  have eq4106 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq4099
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq4099
    | exact resolve eq4099 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4099
  have eq4107 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op (M.op x y) y) := by
    first
    | exact superpose eq21 eq4100
    | exact resolve eq4100 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4100
  have eq4114 : (τ (σ x)) = (k y (M.op x y)) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq4106 eq92
    | exact resolve eq92 eq4106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4106
  have eq4116 : y = (M.op (M.op x y) y) ∨ x = (k y (M.op x y)) := by
    first
    | exact superpose eq29 eq4114
    | exact resolve eq4114 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4114
  have eq4117 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq4107
       have i₂ := eq77 sF2 sF1
       grind)
    | exact superpose eq77 eq4107
    | (have j1 := eq77 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq4107 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4107
  have eq4124 : y ≠ y ∨ (k y (M.op x y)) = (M.op y (M.op x y)) ∨ x = (k y (M.op x y)) := by
    first
    | exact superpose eq4116 eq13
    | (have j0 := eq13 y (M.op x y)
       grind)
    | (have r₁ := eq13 y (M.op x y)
       have r₂ := eq4116
       grind)
    | exact resolve eq13 eq4116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4116
  have eq4126 : (k y (M.op x y)) = (M.op y (M.op x y)) ∨ x = (k y (M.op x y)) := by grind
  clear eq4124
  have eq4127 : (k y (M.op x y)) = (M.op y y) ∨ x = (k y (M.op x y)) := by
    first
    | exact superpose eq2831 eq4126
    | exact resolve eq4126 eq2831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4126
  have eq4129 : x = (k y (M.op x y)) ∨ x = (k y (M.op x y)) := by
    first
    | (have i₁ := eq4127
       have i₂ := eq2624
       grind)
    | exact superpose eq2624 eq4127
    | exact resolve eq4127 eq2624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4127
  have eq4130 : x = (k y (M.op x y)) := by grind
  clear eq4129
  have eq4132 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq4130 eq76
    | exact resolve eq76 eq4130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4135 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq4132
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq4132
    | exact resolve eq4132 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4132
  have eq4160 : ∀ X0 : G, (k (σ X0) (k (σ y) (σ (M.op x y)))) = (σ (M.op X0 (k y (M.op x y)))) ∨ (M.op (k y (M.op x y)) (k y (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq92 eq327
    | exact resolve eq327 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4163 : ∀ X0 : G, (k (σ X0) (σ (M.op x y))) = (σ (M.op X0 (M.op x y))) ∨ (M.op (M.op x y) (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq31 eq327
    | exact resolve eq327 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4165 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (M.op X0 y)) ∨ (M.op y y) = X0 := by
    intro X0
    first
    | exact superpose eq30 eq327
    | exact resolve eq327 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327
  have eq4205 : ∀ X0 : G, (σ (k X0 y)) = (σ (M.op X0 y)) ∨ (M.op y y) = X0 := by
    intro X0
    first
    | exact superpose eq41 eq4165
    | (have j0 := eq4165 X0
       grind)
    | exact resolve eq4165 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4165
  have eq4207 : ∀ X0 : G, (k (σ X0) (σ (M.op x y))) = (σ (M.op X0 y)) ∨ (M.op (M.op x y) (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq2831 eq4163
    | (have j0 := eq4163 X0
       grind)
    | exact resolve eq4163 eq2831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4163
  have eq4208 : ∀ X0 : G, (k (σ X0) (k (σ y) (σ (M.op x y)))) = (σ (M.op X0 x)) ∨ (M.op (k y (M.op x y)) (k y (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq4130 eq4160
    | (have j0 := eq4160 X0
       grind)
    | exact resolve eq4160 eq4130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4160
  have eq4214 : ∀ X0 : G, (σ (k X0 y)) = (σ (M.op X0 y)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq4205 X0
       have i₂ := eq2624
       grind)
    | exact superpose eq2624 eq4205
    | (have j0 := eq4205 X0
       grind)
    | exact resolve eq4205 eq2624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4205
  have eq4215 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (σ (M.op X0 y)) ∨ (M.op (M.op x y) (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq42 eq4207
    | (have j0 := eq4207 X0
       grind)
    | exact resolve eq4207 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq4207
  have eq4216 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (M.op X0 x)) ∨ (M.op (k y (M.op x y)) (k y (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq4135 eq4208
    | (have j0 := eq4208 X0
       grind)
    | exact resolve eq4208 eq4135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4208
  have eq4219 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (σ (M.op X0 y)) ∨ (M.op (M.op x y) y) = X0 := by
    intro X0
    first
    | exact superpose eq2831 eq4215
    | (have j0 := eq4215 X0
       grind)
    | exact resolve eq4215 eq2831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4215
  have eq4220 : ∀ X0 : G, (σ (k X0 x)) = (σ (M.op X0 x)) ∨ (M.op (k y (M.op x y)) (k y (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq40 eq4216
    | (have j0 := eq4216 X0
       grind)
    | exact resolve eq4216 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq4216
  have eq4223 : ∀ X0 : G, (σ (k X0 x)) = (σ (M.op X0 x)) ∨ (M.op x x) = X0 := by
    intro X0
    first
    | exact superpose eq4130 eq4220
    | (have j0 := eq4220 X0
       grind)
    | exact resolve eq4220 eq4130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4220
  have eq4257 : (M.op (M.op x y) y) ≠ (M.op (M.op x y) y) ∨ (k (M.op (M.op x y) y) (M.op x y)) = (M.op (M.op (M.op x y) y) (M.op x y)) := by
    first
    | exact superpose eq2831 eq207
    | (have r₁ := eq207 (M.op x y)
       have r₂ := eq2831 (M.op x y)
       grind)
    | exact resolve eq207 eq2831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4258 : (k (M.op (M.op x y) y) (M.op x y)) = (M.op (M.op (M.op x y) y) (M.op x y)) := by grind
  clear eq4257
  have eq4259 : (k (M.op (M.op x y) y) (M.op x y)) = (M.op (M.op (M.op x y) y) y) := by
    first
    | exact superpose eq2831 eq4258
    | exact resolve eq4258 eq2831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4258
  have eq4272 : (k (σ (M.op x y)) (σ y)) = (σ (M.op (M.op x y) y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq129 eq4214
    | (have j0 := eq4214 (M.op x y)
       grind)
    | exact resolve eq4214 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4275 : ∀ X0 : G, (k X0 (σ y)) = (σ (M.op (τ X0) y)) ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq35 X0 y
       have i₂ := eq4214 (τ X0)
       grind)
    | exact superpose eq4214 eq35
    | (have j1 := eq4214 (τ X0)
       grind)
    | exact resolve eq35 eq4214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4278 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ x = y := by
    first
    | (have i₁ := eq75
       have i₂ := eq4214 y
       grind)
    | exact superpose eq4214 eq75
    | (have j1 := eq4214 y
       grind)
    | exact resolve eq75 eq4214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4214
  have eq4331 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq4278
       have i₂ := eq2624
       grind)
    | exact superpose eq2624 eq4278
    | exact resolve eq4278 eq2624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4278
  have eq4332 : ∀ X0 : G, (k X0 (σ y)) = (σ (M.op (τ X0) y)) ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq4275 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq4275
    | (have j0 := eq4275 X0
       grind)
    | exact resolve eq4275 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4275
  have eq4337 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq4331
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq4331
    | exact resolve eq4331 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4331
  have eq4355 : (τ (σ x)) = (k y y) ∨ x = y := by
    first
    | exact superpose eq4337 eq87
    | exact resolve eq87 eq4337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq4337
  have eq4359 : x = (k y y) ∨ x = y := by
    first
    | exact superpose eq29 eq4355
    | exact resolve eq4355 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4355
  have eq4360 : x = (k y y) := by
    first
    | (have r₁ := eq4359
       have r₂ := eq2727
       grind)
    | exact resolve eq4359 eq2727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2727 eq4359
  have eq4364 : (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq75
       have i₂ := eq4360
       grind)
    | exact superpose eq4360 eq75
    | exact resolve eq75 eq4360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq4360
  have eq4369 : (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq4364
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq4364
    | exact resolve eq4364 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4364
  have eq4374 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq4369
       have i₂ := eq77 sF3 sF3
       grind)
    | exact superpose eq77 eq4369
    | (have j1 := eq77 (σ y) (σ y)
       grind)
    | exact resolve eq4369 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4438 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq4374 eq13
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq4374
       grind)
    | exact resolve eq13 eq4374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4440 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq4374
  have eq4441 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq4438
  have eq4442 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq4369 eq4441
    | exact resolve eq4441 eq4369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4369 eq4441
  have eq4443 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq4442
       have r₂ := eq4440
       grind)
    | exact resolve eq4442 eq4440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4440 eq4442
  have eq4456 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X1)) := by
    intro X0 X1
    first
    | exact superpose eq4443 eq55
    | exact resolve eq55 eq4443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4465 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq27 eq4456
    | (have j0 := eq4456 X0 (σ y)
       grind)
    | exact resolve eq4456 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4547 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op (M.op (σ x) (σ y)) X0) = (k (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq4465 eq13
    | (have j0 := eq13 (M.op (σ x) (σ y)) X0
       grind)
    | (have r₁ := eq13 (M.op (σ x) (σ y)) (σ x)
       have r₂ := eq4465 (σ x)
       grind)
    | exact resolve eq13 eq4465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4465
  have eq4578 : (M.op (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4272 eq16
    | exact resolve eq16 eq4272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4272
  have eq4609 : (k (M.op x y) y) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq146 eq4578
    | exact resolve eq4578 eq146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4578
  have eq4610 : (k (M.op x y) y) = (M.op (M.op x y) y) := by
    first
    | (have r₁ := eq4609
       have r₂ := eq3044
       grind)
    | exact resolve eq4609 eq3044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3044 eq4609
  have eq4687 : (k (σ (M.op x y)) (σ y)) = (σ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq4610 eq129
    | exact resolve eq129 eq4610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4692 : (k (σ x) (k (σ (M.op x y)) (σ y))) = (σ (k x (M.op (M.op x y) y))) := by
    first
    | exact superpose eq4687 eq36
    | exact resolve eq36 eq4687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq4693 : (k (σ y) (k (σ (M.op x y)) (σ y))) = (σ (k y (M.op (M.op x y) y))) := by
    first
    | exact superpose eq4687 eq37
    | exact resolve eq37 eq4687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq4687
  have eq4727 : (k (σ x) (k (σ (M.op x y)) (σ y))) = (σ (M.op x (M.op (M.op x y) y))) ∨ x = (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq4692
       have i₂ := eq77 x (M.op sF0 y)
       grind)
    | exact superpose eq77 eq4692
    | (have j1 := eq77 x (M.op (M.op x y) y)
       grind)
    | exact resolve eq4692 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4730 : (τ (k (σ x) (k (σ (M.op x y)) (σ y)))) = (k x (M.op (M.op x y) y)) := by
    first
    | exact superpose eq4692 eq16
    | exact resolve eq16 eq4692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4692
  have eq4759 : (σ (M.op x y)) = (k (σ x) (k (σ (M.op x y)) (σ y))) ∨ x = (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) := by
    first
    | exact superpose eq210 eq4727
    | exact resolve eq4727 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4727
  have eq4760 : (σ (M.op x y)) = (k (σ x) (k (σ (M.op x y)) (σ y))) ∨ x = (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq4759
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq4759
    | exact resolve eq4759 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4759
  have eq4761 : (σ (M.op x y)) = (k (σ x) (k (σ (M.op x y)) (σ y))) ∨ x = (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) := by
    first
    | exact superpose eq21 eq4760
    | exact resolve eq4760 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4760
  have eq4762 : (σ (M.op x y)) = (k (σ x) (k (σ (M.op x y)) (σ y))) ∨ x = (M.op (M.op (M.op x y) y) y) := by
    first
    | exact superpose eq210 eq4761
    | exact resolve eq4761 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4761
  have eq4764 : (k (σ y) (k (σ (M.op x y)) (σ y))) = (σ (M.op y (M.op (M.op x y) y))) ∨ y = (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq4693
       have i₂ := eq77 y (M.op sF0 y)
       grind)
    | exact superpose eq77 eq4693
    | (have j1 := eq77 y (M.op (M.op x y) y)
       grind)
    | exact resolve eq4693 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4767 : (τ (k (σ y) (k (σ (M.op x y)) (σ y)))) = (k y (M.op (M.op x y) y)) := by
    first
    | exact superpose eq4693 eq16
    | exact resolve eq16 eq4693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4796 : (σ (M.op y y)) = (k (σ y) (k (σ (M.op x y)) (σ y))) ∨ y = (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) := by
    first
    | exact superpose eq51 eq4764
    | exact resolve eq4764 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4764
  have eq4797 : (σ x) = (k (σ y) (k (σ (M.op x y)) (σ y))) ∨ y = (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq4796
       have i₂ := eq2624
       grind)
    | exact superpose eq2624 eq4796
    | exact resolve eq4796 eq2624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4796
  have eq4798 : (σ x) = (k (σ y) (k (σ (M.op x y)) (σ y))) ∨ y = (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq4797
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq4797
    | exact resolve eq4797 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4797
  have eq4799 : (σ x) = (k (σ y) (k (σ (M.op x y)) (σ y))) ∨ y = (M.op (M.op (M.op x y) y) y) := by
    first
    | exact superpose eq210 eq4798
    | exact resolve eq4798 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210 eq4798
  have eq4923 : ∀ X0 X1 : G, (M.op X0 (σ (M.op x y))) = (M.op X0 (M.op (k (σ y) (σ (M.op x y))) X1)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq76 eq586
    | (have j0 := eq586 y (M.op x y) x x
       grind)
    | exact resolve eq586 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586
  have eq5010 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) X1)) = (M.op X0 (σ (M.op x y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq4135 eq4923
    | exact resolve eq4923 eq4135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4923
  have eq5066 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) X1)) = (M.op X0 (σ (M.op x y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq21 eq5010
    | (have j0 := eq5010 X0 X1
       grind)
    | exact resolve eq5010 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5010
  have eq5118 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq4456 eq5066
    | exact resolve eq5066 eq4456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5066
  have eq5160 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq21 eq5118
    | (have j0 := eq5118 X0
       grind)
    | exact resolve eq5118 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5118
  have eq5178 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq5160 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq5160
    | (have j0 := eq5160 X0
       grind)
    | exact resolve eq5160 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5160
  have eq5900 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (M.op (σ x) (σ y)) (σ x)) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq27 eq4547
    | (have j0 := eq4547 (σ x)
       grind)
    | (have r₁ := eq4547 (σ x)
       have r₂ := eq27
       grind)
    | exact resolve eq4547 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5905 : (M.op (M.op (σ x) (σ y)) (σ x)) = (k (M.op (σ x) (σ y)) (σ x)) := by grind
  clear eq5900
  have eq6507 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ y) X0) ∨ (σ (k (τ X0) y)) = (M.op (σ (τ X0)) (σ y)) ∨ (σ y) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq592 y (τ X0)
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq592
    | (have j0 := eq592 y (τ X0)
       grind)
    | exact resolve eq592 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq6539 : ∀ X0 : G, (k (σ y) X0) ≠ X0 ∨ (σ (k (τ X0) y)) = (M.op (σ (τ X0)) (σ y)) ∨ (σ y) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq6507 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq6507
    | (have j0 := eq6507 X0
       grind)
    | exact resolve eq6507 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6507
  have eq6608 : ∀ X0 : G, (σ (k (τ X0) y)) = (M.op (σ (τ X0)) (σ y)) ∨ (k (σ y) X0) ≠ X0 ∨ (σ y) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq6539 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq6539
    | (have j0 := eq6539 X0
       grind)
    | exact resolve eq6539 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6539
  have eq6664 : ∀ X0 : G, (M.op X0 (σ y)) = (σ (k (τ X0) y)) ∨ (k (σ y) X0) ≠ X0 ∨ (σ y) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq6608 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq6608
    | (have j0 := eq6608 X0
       grind)
    | exact resolve eq6608 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6608
  have eq6719 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (k (σ y) X0) ≠ X0 ∨ (σ y) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq6664 X0
       have i₂ := eq35 X0 y
       grind)
    | exact superpose eq35 eq6664
    | (have j0 := eq6664 X0
       grind)
    | exact resolve eq6664 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6664
  have eq6771 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (k (σ y) X0) ≠ X0 ∨ (σ y) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq6719 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq6719
    | (have j0 := eq6719 X0
       grind)
    | exact resolve eq6719 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6719
  have eq6819 : ∀ X0 : G, (M.op X0 X0) = (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (k (σ y) X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq6771 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq6771
    | (have j0 := eq6771 X0
       grind)
    | exact resolve eq6771 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6771
  have eq6860 : ∀ X0 : G, (k (σ y) X0) ≠ X0 ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq6819 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq6819
    | (have j0 := eq6819 X0
       grind)
    | exact resolve eq6819 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6819
  have eq8211 : (M.op (M.op x y) y) ≠ (M.op (M.op (M.op x y) (M.op x y)) y) ∨ (M.op (M.op (M.op x y) y) y) = (k (M.op (M.op x y) y) (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq749 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq749
    | (have j0 := eq749 x y
       grind)
    | exact resolve eq749 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq749
  have eq8293 : (M.op (M.op x y) y) ≠ (M.op (M.op (M.op x y) y) y) ∨ (M.op (M.op (M.op x y) y) y) = (k (M.op (M.op x y) y) (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq2831 eq8211
    | exact resolve eq8211 eq2831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8211
  have eq8323 : (M.op (M.op x y) y) ≠ (M.op (M.op (M.op x y) y) y) ∨ (k (M.op (M.op x y) y) (M.op (M.op x y) y)) = (M.op (M.op (M.op x y) y) y) := by
    first
    | exact superpose eq2831 eq8293
    | exact resolve eq8293 eq2831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2831 eq8293
  have eq8588 : ∀ X0 : G, (σ (τ (k X0 (σ x)))) = (σ (M.op (τ X0) x)) ∨ (τ X0) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq4223 (τ X0)
       have i₂ := eq488 X0
       grind)
    | exact superpose eq488 eq4223
    | (have j0 := eq4223 (τ X0)
       grind)
    | exact resolve eq4223 eq488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488 eq4223
  have eq8675 : ∀ X0 : G, (k X0 (σ x)) = (σ (M.op (τ X0) x)) ∨ (τ X0) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq8588 X0
       have i₂ := eq15 (k X0 sF2)
       grind)
    | exact superpose eq15 eq8588
    | (have j0 := eq8588 X0
       grind)
    | exact resolve eq8588 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8588
  have eq10996 : (τ (σ (M.op x y))) = (k x (M.op (M.op x y) y)) ∨ x = (M.op (M.op (M.op x y) y) y) := by
    first
    | exact superpose eq4762 eq4730
    | exact resolve eq4730 eq4762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4730 eq4762
  have eq11001 : (M.op x y) = (k x (M.op (M.op x y) y)) ∨ x = (M.op (M.op (M.op x y) y) y) := by
    first
    | exact superpose eq31 eq10996
    | exact resolve eq10996 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq10996
  have eq11008 : (τ (σ x)) = (k y (M.op (M.op x y) y)) ∨ y = (M.op (M.op (M.op x y) y) y) := by
    first
    | exact superpose eq4799 eq4767
    | exact resolve eq4767 eq4799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4767 eq4799
  have eq11013 : y = (M.op (M.op (M.op x y) y) y) ∨ x = (k y (M.op (M.op x y) y)) := by
    first
    | exact superpose eq29 eq11008
    | exact resolve eq11008 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11008
  have eq11238 : y ≠ y ∨ (M.op y (M.op (M.op x y) y)) = (k y (M.op (M.op x y) y)) ∨ x = (k y (M.op (M.op x y) y)) := by
    first
    | exact superpose eq11013 eq13
    | (have j0 := eq13 y (M.op (M.op x y) y)
       grind)
    | (have r₁ := eq13 y (M.op (M.op x y) y)
       have r₂ := eq11013
       grind)
    | exact resolve eq13 eq11013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11013
  have eq11250 : (M.op y (M.op (M.op x y) y)) = (k y (M.op (M.op x y) y)) ∨ x = (k y (M.op (M.op x y) y)) := by grind
  clear eq11238
  have eq11253 : (M.op y y) = (k y (M.op (M.op x y) y)) ∨ x = (k y (M.op (M.op x y) y)) := by
    first
    | exact superpose eq51 eq11250
    | exact resolve eq11250 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq11250
  have eq11258 : x = (k y (M.op (M.op x y) y)) ∨ x = (k y (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq11253
       have i₂ := eq2624
       grind)
    | exact superpose eq2624 eq11253
    | exact resolve eq11253 eq2624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11253
  have eq11259 : x = (k y (M.op (M.op x y) y)) := by grind
  clear eq11258
  have eq11266 : (σ x) = (k (σ y) (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq11259 eq4693
    | exact resolve eq4693 eq11259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11275 : (σ x) = (k (σ y) (k (σ (M.op x y)) (σ y))) := by
    first
    | (have i₁ := eq11266
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq11266
    | exact resolve eq11266 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11266
  have eq67774 : ∀ X0 : G, (σ (σ (k X0 y))) = (σ (M.op (σ X0) (σ y))) ∨ (σ X0) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq41 eq3989
    | (have j0 := eq3989 (σ X0) (σ y)
       grind)
    | exact resolve eq3989 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq3989
  have eq68485 : ∀ X0 : G, (σ (σ (k X0 y))) = (σ (M.op (σ X0) (σ y))) ∨ (σ X0) = (σ x) := by
    intro X0
    first
    | exact superpose eq4443 eq67774
    | (have j0 := eq67774 X0
       grind)
    | exact resolve eq67774 eq4443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67774
  have eq68801 : ∀ X0 : G, (σ (M.op X0 (σ y))) = (σ (σ (k (τ X0) y))) ∨ (σ x) = X0 := by
    intro X0
    first
    | (have i₁ := eq68485 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq68485
    | exact resolve eq68485 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68999 : (σ (M.op (σ (M.op x y)) (σ y))) = (σ (σ (k (M.op x y) y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq21 eq68485
    | (have j0 := eq68485 (M.op x y)
       grind)
    | exact resolve eq68485 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68485
  have eq69119 : (σ (k (σ (M.op x y)) (σ y))) = (σ (M.op (σ (M.op x y)) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq129 eq68999
    | exact resolve eq68999 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq68999
  have eq69137 : ∀ X0 : G, (σ (M.op X0 (σ y))) = (σ (k X0 (σ y))) ∨ (σ x) = X0 := by
    intro X0
    first
    | (have i₁ := eq68801 X0
       have i₂ := eq35 X0 y
       grind)
    | exact superpose eq35 eq68801
    | (have j0 := eq68801 X0
       grind)
    | exact resolve eq68801 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq68801
  have eq69148 : ∀ X0 : G, (σ (k X0 (σ y))) = (σ (M.op X0 (σ y))) ∨ (σ x) = X0 := by
    intro X0
    first
    | (have i₁ := eq69137 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq69137
    | (have j0 := eq69137 X0
       grind)
    | exact resolve eq69137 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69137
  have eq69157 : (k (σ (M.op x y)) (σ y)) = (τ (σ (M.op (σ (M.op x y)) (σ y)))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq69119 eq16
    | exact resolve eq16 eq69119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69119
  have eq69274 : (k (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq69157
       have i₂ := eq16 (M.op sF1 sF3)
       grind)
    | exact superpose eq16 eq69157
    | exact resolve eq69157 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69157
  have eq69494 : ∀ X0 : G, (k X0 (σ y)) = (τ (σ (M.op X0 (σ y)))) ∨ (σ x) = X0 := by
    intro X0
    first
    | exact superpose eq69148 eq16
    | (have j1 := eq69148 X0
       grind)
    | exact resolve eq16 eq69148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69148
  have eq69607 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (σ x) = X0 := by
    intro X0
    first
    | (have i₁ := eq69494 X0
       have i₂ := eq16 (M.op X0 sF3)
       grind)
    | exact superpose eq16 eq69494
    | (have j0 := eq69494 X0
       grind)
    | exact resolve eq69494 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69494
  have eq79939 : ∀ X0 : G, (k (k y (M.op x y)) (τ X0)) = (τ (M.op (k (σ y) (σ (M.op x y))) X0)) ∨ (M.op X0 X0) = (k (σ y) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq76 eq644
    | exact resolve eq644 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq644
  have eq80169 : ∀ X0 : G, (k (k y (M.op x y)) (τ X0)) = (τ (M.op (σ x) X0)) ∨ (M.op X0 X0) = (k (σ y) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq4135 eq79939
    | (have j0 := eq79939 X0
       grind)
    | exact resolve eq79939 eq4135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79939
  have eq80193 : ∀ X0 : G, (k x (τ X0)) = (τ (M.op (σ x) X0)) ∨ (M.op X0 X0) = (k (σ y) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq4130 eq80169
    | (have j0 := eq80169 X0
       grind)
    | exact resolve eq80169 eq4130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80169
  have eq80199 : ∀ X0 : G, (τ (k (σ x) X0)) = (τ (M.op (σ x) X0)) ∨ (M.op X0 X0) = (k (σ y) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq80193 X0
       have i₂ := eq235 X0
       grind)
    | exact superpose eq235 eq80193
    | (have j0 := eq80193 X0
       grind)
    | exact resolve eq80193 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235 eq80193
  have eq80203 : ∀ X0 : G, (τ (k (σ x) X0)) = (τ (M.op (σ x) X0)) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | exact superpose eq4135 eq80199
    | (have j0 := eq80199 X0
       grind)
    | exact resolve eq80199 eq4135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80199
  have eq80281 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq50 eq80203
    | (have j0 := eq80203 (σ x)
       grind)
    | exact resolve eq80203 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq80203
  have eq85557 : (σ (M.op x y)) ≠ (σ x) ∨ (k (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq4135 eq6860
    | (have j0 := eq6860 (σ (M.op x y))
       grind)
    | exact resolve eq6860 eq4135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6860
  have eq85570 : (k (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq85557
       have r₂ := eq69274
       grind)
    | exact resolve eq85557 eq69274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69274 eq85557
  have eq85599 : (k (M.op x y) y) = (τ (M.op (σ (M.op x y)) (σ y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq85570 eq146
    | exact resolve eq146 eq85570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146 eq85570
  have eq85685 : (M.op (M.op x y) y) = (τ (M.op (σ (M.op x y)) (σ y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq4610 eq85599
    | exact resolve eq85599 eq4610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4610 eq85599
  have eq85885 : (M.op (M.op x y) y) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq5178 eq85685
    | exact resolve eq85685 eq5178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5178 eq85685
  have eq85959 : (M.op (M.op x y) y) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq85885
  have eq86140 : (τ (σ x)) = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq4117 eq85959
    | exact resolve eq85959 eq4117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4117 eq85959
  have eq86232 : x = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq29 eq86140
    | exact resolve eq86140 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86140
  have eq86233 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op (M.op x y) y) := by grind
  clear eq86232
  have eq86377 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op (M.op x y) y) := by
    intro X0
    first
    | exact superpose eq86233 eq4456
    | exact resolve eq4456 eq86233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4456
  have eq86538 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op (M.op x y) y) := by
    first
    | exact superpose eq27 eq86377
    | (have j0 := eq86377 (σ x)
       grind)
    | exact resolve eq86377 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86377
  have eq86790 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = (M.op (M.op x y) y) := by
    first
    | exact superpose eq86538 eq86233
    | exact resolve eq86233 eq86538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86233 eq86538
  have eq86821 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op (M.op x y) y) := by grind
  clear eq86790
  have eq86829 : x = (M.op (M.op x y) y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq86821
       have r₂ := eq28
       grind)
    | exact resolve eq86821 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86821
  have eq86894 : x ≠ (M.op x y) ∨ (M.op x y) = (k x x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq86829 eq8323
    | exact resolve eq8323 eq86829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8323
  have eq86896 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq86829 eq11001
    | exact resolve eq11001 eq86829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11001
  have eq86898 : x = (k y x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq86829 eq11259
    | exact resolve eq11259 eq86829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11259
  have eq86903 : x ≠ (M.op y y) ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq86829 eq207
    | exact resolve eq207 eq86829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207 eq86829
  have eq86934 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq77 x y
       grind)
    | (have r₁ := eq86903
       have r₂ := eq77 x y
       grind)
    | exact resolve eq86903 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86903
  have eq86937 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq86896
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq86896
    | exact resolve eq86896 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86896
  have eq86939 : x ≠ (M.op x y) ∨ (M.op x y) = (k x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq86894
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq86894
    | exact resolve eq86894 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86894
  have eq87001 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq86934
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq86934
    | exact resolve eq86934 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86934
  have eq87003 : (M.op x y) = (k x x) ∨ x ≠ (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq86939
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq86939
    | exact resolve eq86939 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86939
  have eq87116 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq592 y x
       have i₂ := eq86898
       grind)
    | exact superpose eq86898 eq592
    | (have j0 := eq592 y x
       grind)
    | exact resolve eq592 eq86898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592 eq86898
  have eq87121 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq87116
  have eq87124 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq87121
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq87121
    | exact resolve eq87121 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87121
  have eq87151 : (k (σ x) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq87124
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq87124
    | exact resolve eq87124 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87124
  have eq87154 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq87151
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq87151
    | exact resolve eq87151 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87151
  have eq87157 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq87154
    | exact resolve eq87154 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87154
  have eq87159 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq87157
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq87157
    | exact resolve eq87157 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87157
  have eq87160 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq87159
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq87159
    | exact resolve eq87159 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87159
  have eq87466 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq87001
       grind)
    | exact superpose eq87001 eq45
    | exact resolve eq45 eq87001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87001
  have eq87538 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq87466
    | exact resolve eq87466 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87466
  have eq94571 : (M.op x y) = (k x x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq87003
       have r₂ := eq86937
       grind)
    | exact resolve eq87003 eq86937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86937 eq87003
  have eq127544 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq87160 eq87538
    | exact resolve eq87538 eq87160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87160 eq87538
  have eq127564 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq127544
  have eq127572 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq127564
       have r₂ := eq28
       grind)
    | exact resolve eq127564 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127564
  have eq128140 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq127572 eq80281
    | exact resolve eq80281 eq127572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80281 eq127572
  have eq128190 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) := by grind
  clear eq128140
  have eq128222 : y = (k x x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq30 eq128190
    | exact resolve eq128190 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq128190
  have eq128261 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq94571
       have i₂ := eq128222
       grind)
    | exact superpose eq128222 eq94571
    | exact resolve eq94571 eq128222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94571 eq128222
  have eq128287 : (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq128261
  have eq128940 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq128287 eq27
    | exact resolve eq27 eq128287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128951 : (τ (k (σ x) (σ (M.op x y)))) = (k y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq128287 eq92
    | exact resolve eq92 eq128287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq128992 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq128287 eq4135
    | exact resolve eq4135 eq128287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4135
  have eq129001 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq128287 eq4443
    | exact resolve eq4443 eq128287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128287
  have eq129368 : x = (τ (k (σ x) (σ (M.op x y)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4130 eq128951
    | exact resolve eq128951 eq4130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4130 eq128951
  have eq129382 : x = (k x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq63 eq129368
    | exact resolve eq129368 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq129368
  have eq133061 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq129001 eq128940
    | exact resolve eq128940 eq129001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128940 eq129001
  have eq133112 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq133061
  have eq133668 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq133112 eq28
    | exact resolve eq28 eq133112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133112
  have eq134938 : (σ (M.op x y)) = (σ x) ∨ x = (M.op (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq129382 eq4219
    | (have j0 := eq4219 x
       grind)
    | exact resolve eq4219 eq129382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4219 eq129382
  have eq134969 : (σ (M.op x y)) = (σ x) ∨ x = (M.op (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq134938
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq134938
    | exact resolve eq134938 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134938
  have eq135001 : (σ (M.op x y)) = (σ x) ∨ x = (M.op (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq134969
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq134969
    | exact resolve eq134969 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134969
  have eq135008 : (σ (M.op x y)) = (σ x) ∨ x = (M.op (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq135001
    | exact resolve eq135001 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135001
  have eq135014 : x = (M.op (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq135008
       have r₂ := eq133668
       grind)
    | exact resolve eq135008 eq133668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135008
  have eq138593 : (M.op x y) = (k x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq135014 eq4259
    | exact resolve eq4259 eq135014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135014
  have eq138765 : (M.op x y) = (k x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq138593
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq138593
    | exact resolve eq138593 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138593
  have eq142577 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq138765 eq46
    | exact resolve eq46 eq138765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq138765
  have eq142667 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq142577
    | exact resolve eq142577 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142577
  have eq149170 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq142667 eq128992
    | exact resolve eq128992 eq142667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128992 eq142667
  have eq149187 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq149170
  have eq149193 : y = (M.op x y) := by
    first
    | (have r₁ := eq149187
       have r₂ := eq133668
       grind)
    | exact resolve eq149187 eq133668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133668 eq149187
  have eq149215 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq149193 eq21
    | exact resolve eq21 eq149193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq149320 : (k (M.op y y) y) = (M.op (M.op y y) y) := by
    first
    | exact superpose eq149193 eq4259
    | exact resolve eq4259 eq149193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4259
  have eq149327 : (k (σ y) (k (σ (M.op x y)) (σ y))) = (σ (k y (M.op y y))) := by
    first
    | exact superpose eq149193 eq4693
    | exact resolve eq4693 eq149193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4693
  have eq149643 : (σ (k y x)) = (k (σ y) (k (σ (M.op x y)) (σ y))) := by
    first
    | (have i₁ := eq149327
       have i₂ := eq2624
       grind)
    | exact superpose eq2624 eq149327
    | exact resolve eq149327 eq2624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149327
  have eq149648 : (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq149320
       have i₂ := eq2624
       grind)
    | exact superpose eq2624 eq149320
    | exact resolve eq149320 eq2624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2624 eq149320
  have eq149728 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq149215
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq149215
    | exact resolve eq149215 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149215
  have eq149802 : (σ x) = (σ (k y x)) := by
    first
    | exact superpose eq11275 eq149643
    | exact resolve eq149643 eq11275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11275 eq149643
  have eq149806 : (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq149648
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq149648
    | exact resolve eq149648 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149648
  have eq149835 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq149802
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq149802
    | exact resolve eq149802 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq149802
  have eq149836 : y = (k x y) := by
    first
    | exact superpose eq149193 eq149806
    | exact resolve eq149806 eq149193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149806
  have eq149848 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq149728 eq27
    | exact resolve eq27 eq149728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq149909 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq149728 eq4443
    | exact resolve eq4443 eq149728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4443
  have eq149913 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ (M.op x y))) ∨ (M.op (M.op (σ x) (σ y)) X0) = (k (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq149728 eq4547
    | (have j0 := eq4547 X0
       grind)
    | exact resolve eq4547 eq149728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4547
  have eq150176 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (M.op X0 (σ (M.op x y))) ∨ (σ x) = X0 := by
    intro X0
    first
    | exact superpose eq149728 eq69607
    | (have j0 := eq69607 X0
       grind)
    | exact resolve eq69607 eq149728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69607
  have eq151844 : (σ x) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq149728 eq149835
    | exact resolve eq149835 eq149728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149835
  have eq151857 : (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq149836
       grind)
    | exact superpose eq149836 eq45
    | exact resolve eq45 eq149836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq149836
  have eq151945 : (σ y) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq149728 eq151857
    | exact resolve eq151857 eq149728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151857
  have eq151975 : (σ y) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq151945
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq151945
    | exact resolve eq151945 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151945
  have eq152004 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq149728 eq151975
    | exact resolve eq151975 eq149728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151975
  have eq152033 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq151844
       have i₂ := eq77 sF1 sF2
       grind)
    | exact superpose eq77 eq151844
    | (have j1 := eq77 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq151844 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq152034 : (τ (σ x)) = (k (M.op x y) x) := by
    first
    | exact superpose eq151844 eq139
    | exact resolve eq139 eq151844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139 eq151844
  have eq152116 : (τ (σ x)) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq3046 eq152034
    | exact resolve eq152034 eq3046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3046 eq152034
  have eq152142 : (τ (σ x)) = (M.op y x) := by
    first
    | exact superpose eq149193 eq152116
    | exact resolve eq152116 eq149193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152116
  have eq152156 : x = (M.op y x) := by
    first
    | exact superpose eq29 eq152142
    | exact resolve eq152142 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq152142
  have eq152539 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X1 x X0 y
       have i₂ := eq152156
       grind)
    | exact superpose eq152156 eq55
    | exact resolve eq55 eq152156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152156
  have eq152563 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq152539 X0 x
       have i₂ := eq2726 X0 x
       grind)
    | exact superpose eq2726 eq152539
    | exact resolve eq152539 eq2726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2726 eq152539
  have eq152800 : ∀ X0 : G, (k X0 (σ y)) = (σ (M.op (τ X0) x)) ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq4332 X0
       have i₂ := eq152563 (τ X0)
       grind)
    | exact superpose eq152563 eq4332
    | (have j0 := eq4332 X0
       grind)
    | exact resolve eq4332 eq152563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4332
  have eq152838 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq152563 x
       grind)
    | exact superpose eq152563 eq19
    | (have j1 := eq152563 x
       grind)
    | exact resolve eq19 eq152563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq152563
  have eq153013 : y = (M.op x x) := by
    first
    | exact superpose eq149193 eq152838
    | exact resolve eq152838 eq149193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149193 eq152838
  have eq153026 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (σ (M.op (τ X0) x)) ∨ (τ X0) = x := by
    intro X0
    first
    | exact superpose eq149728 eq152800
    | (have j0 := eq152800 X0
       grind)
    | exact resolve eq152800 eq149728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152800
  have eq267297 : (σ x) ≠ (σ x) ∨ (k (σ x) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq152033 eq13
    | (have j0 := eq13 (σ x) (σ (M.op x y))
       grind)
    | (have r₁ := eq13 (σ x) (σ (M.op x y))
       have r₂ := eq152033
       grind)
    | exact resolve eq13 eq152033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152033
  have eq267315 : (k (σ x) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq267297
  have eq267328 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq149848 eq267315
    | exact resolve eq267315 eq149848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267315
  have eq267340 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq152004 eq267328
    | exact resolve eq267328 eq152004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267328
  have eq267347 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq267340
       have r₂ := eq28
       grind)
    | exact resolve eq267340 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267340
  have eq365839 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq149909 eq149913
    | (have j0 := eq149913 (σ (M.op x y))
       grind)
    | exact resolve eq149913 eq149909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149909 eq149913
  have eq365860 : (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq150176 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq365839
       have r₂ := eq150176 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq365839 eq150176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150176 eq365839
  have eq536231 : ∀ X0 : G, (k X0 (σ x)) = (k X0 (σ (M.op x y))) ∨ (τ X0) = (M.op x x) ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq8675 X0
       have i₂ := eq153026 X0
       grind)
    | exact superpose eq153026 eq8675
    | (have j0 := eq8675 X0
       have j1 := eq153026 X0
       grind)
    | exact resolve eq8675 eq153026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8675 eq153026
  have eq536407 : ∀ X0 : G, (k X0 (σ x)) = (k X0 (σ (M.op x y))) ∨ (τ X0) = y ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq536231 X0
       have i₂ := eq153013
       grind)
    | exact superpose eq153013 eq536231
    | (have j0 := eq536231 X0
       grind)
    | exact resolve eq536231 eq153013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153013 eq536231
  have eq1256365 : (M.op (M.op (σ x) (σ y)) (σ x)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ y = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq536407 eq5905
    | (have j1 := eq536407 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq5905 eq536407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5905 eq536407
  have eq1256923 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ y = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq365860 eq1256365
    | exact resolve eq1256365 eq365860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1256365
  have eq1282967 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) X1)) ∨ y = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq1256923 eq55
    | exact resolve eq55 eq1256923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1256923
  have eq1283009 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ (M.op x y))) ∨ y = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq1282967 x X0
       have i₂ := eq55 X0 sF1 x sF4
       grind)
    | exact superpose eq55 eq1282967
    | exact resolve eq1282967 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq1282967
  have eq1310684 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1283009 eq267347
    | exact resolve eq267347 eq1283009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267347 eq1283009
  have eq1310713 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq149848 eq1310684
    | exact resolve eq1310684 eq149848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1310684
  have eq1310848 : y = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq1310713
       have r₂ := eq28
       grind)
    | exact resolve eq1310713 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1310713
  have eq1311294 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1310848 eq15
    | exact resolve eq15 eq1310848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1310848
  have eq1311840 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1311294
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1311294
    | exact resolve eq1311294 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1311294
  have eq1311945 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq149728 eq1311840
    | exact resolve eq1311840 eq149728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149728 eq1311840
  have eq1312020 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq1311945
       have r₂ := eq28
       grind)
    | exact resolve eq1311945 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1311945
  have eq1312088 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1312020 eq15
    | exact resolve eq15 eq1312020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1312020
  have eq1312621 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1312088
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1312088
    | exact resolve eq1312088 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1312088
  have eq1312848 : (k (σ x) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1312621 eq365860
    | exact resolve eq365860 eq1312621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365860 eq1312621
  have eq1312881 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq149848 eq1312848
    | exact resolve eq1312848 eq149848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149848 eq1312848
  have eq1312931 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq152004 eq1312881
    | exact resolve eq1312881 eq152004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152004 eq1312881
  have eq1312966 : False := by grind
  exact eq1312966

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyx_pxx_pyx_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
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
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X3 X1) X0) X0
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq61 X0 X1 X2 X3
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq271 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq272 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq271 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq271 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq271 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq283 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq272 (σ X0)
       grind)
    | exact superpose eq272 eq15
    | exact resolve eq15 eq272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq290 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (τ X0)
       have i₂ := eq272 (τ X0)
       grind)
    | exact superpose eq272 eq17
    | exact resolve eq17 eq272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq295 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq290 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq290
    | exact resolve eq290 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq302 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq283 X0
       have i₂ := eq272 X0
       grind)
    | exact superpose eq272 eq283
    | exact resolve eq283 eq272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283
  have eq315 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq295 X0
       have i₂ := eq272 X0
       grind)
    | exact superpose eq272 eq295
    | exact resolve eq295 eq272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272 eq295
  have eq339 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = (M.op X1 (M.op (σ (M.op X0 X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq63 X2 (σ X0) X1 (σ X0)
       have i₂ := eq302 X0
       grind)
    | exact superpose eq302 eq63
    | exact resolve eq63 eq302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq353 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq315 X0
       grind)
    | exact superpose eq315 eq10
    | exact resolve eq10 eq315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315
  have eq363 : ∀ X0 X1 X2 : G, (M.op X1 (τ X0)) = (M.op X1 (M.op (τ (M.op X0 X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq63 X2 (τ X0) X1 (τ X0)
       have i₂ := eq353 X0
       grind)
    | exact superpose eq353 eq63
    | exact resolve eq63 eq353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq391 : ∀ X0 X1 : G, (M.op X1 (τ X0)) = (M.op X1 (τ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq363 X0 X1 (τ (M.op X0 X0))
       have i₂ := eq353 (M.op X0 X0)
       grind)
    | exact superpose eq353 eq363
    | exact resolve eq363 eq353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353 eq363
  have eq414 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq563 : ∀ X0 X1 : G, (M.op X1 (τ (σ (M.op X0 X0)))) = (M.op X1 (τ (M.op (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq391 (σ (M.op X0 X0)) X1
       have i₂ := eq339 X0 (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) (σ (M.op X0 X0))
       grind)
    | exact superpose eq339 eq391
    | exact resolve eq391 eq339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391
  have eq593 : ∀ X0 X1 : G, (M.op X1 (τ (σ (M.op X0 X0)))) = (M.op X1 (τ (M.op (σ (M.op (M.op X0 X0) (M.op X0 X0))) (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq563 X0 X1
       have i₂ := eq302 (M.op X0 X0)
       grind)
    | exact superpose eq302 eq563
    | exact resolve eq563 eq302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563
  have eq608 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X1 (τ (M.op (σ (M.op (M.op X0 X0) (M.op X0 X0))) (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq593 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq593
    | exact resolve eq593 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593
  have eq5177 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op X2 (τ (M.op (σ (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X1)) (σ (M.op X0 X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq608 (M.op X0 X1) X2
       have i₂ := eq63 (M.op X0 X1) X1 (M.op (M.op X0 X1) (M.op X0 X1)) X0
       grind)
    | exact superpose eq63 eq608
    | exact resolve eq608 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608
  have eq5299 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 (τ (M.op (σ (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X1)) (σ (M.op X0 X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5177 X0 X1 X2
       have i₂ := eq63 (M.op X0 X1) X1 X2 X0
       grind)
    | exact superpose eq63 eq5177
    | exact resolve eq5177 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5177
  have eq9546 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq414 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq414 X0 X1
       grind)
    | exact superpose eq414 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq414 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq414 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq414 X0 X1
       grind)
    | exact resolve eq13 eq414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9558 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq414 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414
  have eq9559 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq9546 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9546
  have eq9566 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9559 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq9559
    | (have j0 := eq9559 X0 X1
       grind)
    | exact resolve eq9559 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9559
  have eq9567 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq9566 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9566
  have eq9602 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq9567 X1 X0
       have j1 := eq9558 X0 X1
       grind)
    | (have r₁ := eq9567 X1 X0
       have r₂ := eq9558 X0 X1
       grind)
    | (have r₁ := eq9567 X1 X1
       have r₂ := eq9558 X1 X1
       grind)
    | exact resolve eq9567 eq9558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9558 eq9567
  have eq9628 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9602 (τ X1) (τ X0)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq9602
    | (have j0 := eq9602 (τ X1) (τ X0)
       grind)
    | exact resolve eq9602 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq9722 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) X1) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9628 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq9628
    | (have j0 := eq9628 X0 X1
       grind)
    | exact resolve eq9628 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9628
  have eq9739 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9722 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq9722
    | (have j0 := eq9722 X0 X1
       grind)
    | exact resolve eq9722 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9722
  have eq9744 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9739 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq9739
    | (have j0 := eq9739 X0 X1
       grind)
    | exact resolve eq9739 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9739
  have eq9749 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9744 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq9744
    | (have j0 := eq9744 X0 X1
       grind)
    | exact resolve eq9744 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9744
  have eq9754 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9749 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq9749
    | (have j0 := eq9749 X0 X1
       grind)
    | exact resolve eq9749 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9749
  have eq9769 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9602 X1 X0
       have i₂ := eq9754 X0 X1
       grind)
    | exact superpose eq9754 eq9602
    | (have j0 := eq9602 X1 X0
       have j1 := eq9754 (σ X0) (σ X1)
       grind)
    | exact resolve eq9602 eq9754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14307 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9769 x y
       grind)
    | exact superpose eq9769 eq16
    | (have j1 := eq9769 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq9769 x y
       grind)
    | exact resolve eq16 eq9769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9769
  have eq14377 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq14307
  have eq14470 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq14377
       grind)
    | exact superpose eq14377 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq14377
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq14377
       grind)
    | exact resolve eq12 eq14377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14472 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) X1)) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X1 (σ x) X0 (σ y)
       have i₂ := eq14377
       grind)
    | exact superpose eq14377 eq63
    | exact resolve eq63 eq14377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14486 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq14470
  have eq14494 : (k (σ x) (σ y)) = (σ (M.op x x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq14486
       have i₂ := eq302 x
       grind)
    | exact superpose eq302 eq14486
    | exact resolve eq14486 eq302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14486
  have eq14505 : (σ (M.op x x)) = (σ (k x y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq14494
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq14494
    | exact resolve eq14494 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14494
  have eq14507 : (σ (M.op x y)) = (σ (M.op x x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq9754 eq14505
    | (have j1 := eq9754 x y
       grind)
    | exact resolve eq14505 eq9754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9754 eq14505
  have eq14509 : (M.op x y) = (τ (σ (M.op x x))) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq14507
       grind)
    | exact superpose eq14507 eq10
    | exact resolve eq10 eq14507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14507
  have eq14668 : (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq14509
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq14509
    | exact resolve eq14509 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14509
  have eq14670 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x x) X1)) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X1 y X0 x
       have i₂ := eq14668
       grind)
    | exact superpose eq14668 eq63
    | exact resolve eq63 eq14668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14668
  have eq14683 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq14670 X0 x
       have i₂ := eq63 x x X0 x
       grind)
    | exact superpose eq63 eq14670
    | exact resolve eq14670 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14670
  have eq14796 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq14472 X0 (σ x)
       have i₂ := eq14377
       grind)
    | exact superpose eq14377 eq14472
    | exact resolve eq14472 eq14377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14377 eq14472
  have eq14924 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq14796 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14796
  have eq15074 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14924 (σ x)
       grind)
    | exact superpose eq14924 eq16
    | exact resolve eq16 eq14924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14924
  have eq15095 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq15074
       have i₂ := eq302 x
       grind)
    | exact superpose eq302 eq15074
    | exact resolve eq15074 eq302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15074
  have eq15153 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq14683 eq15095
    | exact resolve eq15095 eq14683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14683 eq15095
  have eq15154 : y = (M.op y x) := by grind
  clear eq15153
  have eq15231 : y ≠ y ∨ (M.op x x) = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq15154
       grind)
    | exact superpose eq15154 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq15154
       grind)
    | exact resolve eq12 eq15154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15233 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op y X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X1 x X0 y
       have i₂ := eq15154
       grind)
    | exact superpose eq15154 eq63
    | exact resolve eq63 eq15154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq15247 : (M.op x x) = (k x y) := by grind
  clear eq15231
  have eq15251 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq9602 y x
       have i₂ := eq15247
       grind)
    | exact superpose eq15247 eq9602
    | (have j0 := eq9602 y x
       grind)
    | exact resolve eq9602 eq15247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9602 eq15247
  have eq15253 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq15233 X0 x
       have i₂ := eq15154
       grind)
    | exact superpose eq15154 eq15233
    | exact resolve eq15233 eq15154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15233
  have eq15428 : (M.op (σ x) (σ y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15253 x
       grind)
    | exact superpose eq15253 eq16
    | exact resolve eq16 eq15253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15429 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ (M.op y x)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq339 y X0 X1
       have i₂ := eq15253 y
       grind)
    | exact superpose eq15253 eq339
    | exact resolve eq339 eq15253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339
  have eq15554 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) X1)) = (M.op X0 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq15429 X0 X1
       have i₂ := eq15154
       grind)
    | exact superpose eq15154 eq15429
    | exact resolve eq15429 eq15154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15429
  have eq19745 : (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq15428
       have r₂ := eq15251
       grind)
    | exact resolve eq15428 eq15251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15251
  have eq19769 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (τ (M.op (σ (M.op (M.op (σ y) (σ y)) (σ x))) (σ (σ y))))) := by
    intro X0
    first
    | (have i₁ := eq5299 (σ y) (σ x) x
       have i₂ := eq19745
       grind)
    | exact superpose eq19745 eq5299
    | exact resolve eq5299 eq19745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5299
  have eq19772 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (τ (M.op (σ (M.op (σ (M.op y y)) (σ x))) (σ (σ y))))) := by
    intro X0
    first
    | (have i₁ := eq19769 X0
       have i₂ := eq302 y
       grind)
    | exact superpose eq302 eq19769
    | exact resolve eq19769 eq302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19769
  have eq19787 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (τ (M.op (σ (M.op (σ (M.op y x)) (σ x))) (σ (σ y))))) := by
    intro X0
    first
    | (have i₁ := eq19772 X0
       have i₂ := eq15253 y
       grind)
    | exact superpose eq15253 eq19772
    | exact resolve eq19772 eq15253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15253 eq19772
  have eq19796 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (τ (M.op (σ (M.op (σ y) (σ x))) (σ (σ y))))) := by
    intro X0
    first
    | (have i₁ := eq19787 X0
       have i₂ := eq15154
       grind)
    | exact superpose eq15154 eq19787
    | exact resolve eq19787 eq15154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15154 eq19787
  have eq19802 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (τ (M.op (σ (σ y)) (σ (σ y))))) := by
    intro X0
    first
    | (have i₁ := eq19796 X0
       have i₂ := eq19745
       grind)
    | exact superpose eq19745 eq19796
    | exact resolve eq19796 eq19745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19745 eq19796
  have eq19806 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (τ (σ (M.op (σ y) (σ y))))) := by
    intro X0
    first
    | (have i₁ := eq19802 X0
       have i₂ := eq302 (σ y)
       grind)
    | exact superpose eq302 eq19802
    | exact resolve eq19802 eq302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19802
  have eq19810 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq19806 X0
       have i₂ := eq10 (M.op (σ y) (σ y))
       grind)
    | exact superpose eq10 eq19806
    | exact resolve eq19806 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19806
  have eq19814 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq19810 X0
       have i₂ := eq15554 X0 (σ y)
       grind)
    | exact superpose eq15554 eq19810
    | exact resolve eq19810 eq15554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15554 eq19810
  have eq19820 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq15428
       have i₂ := eq19814 (σ x)
       grind)
    | exact superpose eq19814 eq15428
    | exact resolve eq15428 eq19814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15428 eq19814
  have eq19985 : False := by grind
  exact eq19985

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(X,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_pxx_pyx_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
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
  clear eq17
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
  clear eq22
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X3 X1) X0) X0
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq61 X0 X1 X2 X3
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq270 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq271 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq14
    | (have j0 := eq14 (τ X0) (τ X1)
       grind)
    | exact resolve eq14 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq949 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq270 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq270
    | (have j0 := eq270 X0 X1
       have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq270 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq974 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq270 X0 X1
       grind)
    | exact superpose eq270 eq10
    | (have j1 := eq270 X0 X1
       grind)
    | exact resolve eq10 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5370 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X1)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) (τ X1)
       have i₂ := eq271 X0 X1
       grind)
    | exact superpose eq271 eq13
    | (have j0 := eq13 (τ X0) (τ X1)
       have j1 := eq271 X1 X0
       grind)
    | (have r₁ := eq13 (τ X0) (τ X1)
       have r₂ := eq271 X0 X1
       grind)
    | (have r₁ := eq13 (τ X1) (τ X0)
       have r₂ := eq271 X0 X1
       grind)
    | exact resolve eq13 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5373 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X1)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq271 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5374 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq271 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq5375 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq5374 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5374
  have eq5376 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X1)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq5370 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5370
  have eq5380 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X1)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq5376 X0 X1
       have j1 := eq13 (τ X0) (τ X1)
       grind)
    | (have r₁ := eq5376 X0 X1
       have r₂ := eq13 (τ X1) (τ X0)
       grind)
    | (have r₁ := eq5376 X0 X1
       have r₂ := eq13 (τ X0) (τ X1)
       grind)
    | exact resolve eq5376 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5376
  have eq5387 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5380 X0 X1
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq5380
    | (have j0 := eq5380 X0 X1
       grind)
    | exact resolve eq5380 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq5380
  have eq5396 : ∀ X0 : G, (τ (σ X0)) ≠ (k X0 (τ (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq5375 (σ X0)
       have i₂ := eq28 X0 (σ X0)
       grind)
    | exact superpose eq28 eq5375
    | (have j0 := eq5375 (σ X0)
       grind)
    | exact resolve eq5375 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq5375
  have eq5414 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq5396 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5396
    | (have j0 := eq5396 X0
       grind)
    | exact resolve eq5396 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5396
  have eq5429 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5414 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5414
    | (have j0 := eq5414 X0
       grind)
    | exact resolve eq5414 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5414
  have eq5704 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (τ (σ (k X0 X1))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X1))) ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5373 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq5373
    | (have j0 := eq5373 (σ X0) (σ X1)
       grind)
    | exact resolve eq5373 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5373
  have eq5762 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (k X0 X1) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X1))) ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5704 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq5704
    | (have j0 := eq5704 X0 X1
       grind)
    | exact resolve eq5704 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5704
  have eq5785 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X1))) ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5762 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5762
    | (have j0 := eq5762 X0 X1
       grind)
    | exact resolve eq5762 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5762
  have eq5807 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op (τ (σ X0)) X1) ∨ (k X0 X1) ≠ X0 ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5785 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq5785
    | (have j0 := eq5785 X0 X1
       grind)
    | exact resolve eq5785 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5785
  have eq5828 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X0 X1) ≠ X0 ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5807 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5807
    | (have j0 := eq5807 X0 X1
       grind)
    | exact resolve eq5807 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5807
  have eq5845 : ∀ X0 X1 : G, (τ (σ X1)) = (M.op (τ (σ X1)) X0) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5828 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5828
    | (have j0 := eq5828 X0 X1
       grind)
    | exact resolve eq5828 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5828
  have eq5858 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5845 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5845
    | (have j0 := eq5845 X0 X1
       grind)
    | exact resolve eq5845 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5845
  have eq5880 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5858 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq5858
    | (have j0 := eq5858 (σ X0) (σ X1)
       grind)
    | exact resolve eq5858 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5858
  have eq6339 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (τ (σ (k X0 X1))) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) (τ (σ X0))) ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5387 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq5387
    | (have j0 := eq5387 (σ X0) (σ X1)
       grind)
    | exact resolve eq5387 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5387
  have eq6397 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (k X0 X1) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) (τ (σ X0))) ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq6339 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq6339
    | (have j0 := eq6339 X0 X1
       grind)
    | exact resolve eq6339 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6339
  have eq6420 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) (τ (σ X0))) ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq6397 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6397
    | (have j0 := eq6397 X0 X1
       grind)
    | exact resolve eq6397 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6397
  have eq6442 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) X0) ∨ (k X0 X1) ≠ X0 ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq6420 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6420
    | (have j0 := eq6420 X0 X1
       grind)
    | exact resolve eq6420 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6420
  have eq6463 : ∀ X0 X1 : G, (M.op X1 X0) = (τ (σ (k X0 X1))) ∨ (k X0 X1) ≠ X0 ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq6442 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq6442
    | (have j0 := eq6442 X0 X1
       grind)
    | exact resolve eq6442 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6442
  have eq6480 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) ≠ X0 ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq6463 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq6463
    | (have j0 := eq6463 X0 X1
       grind)
    | exact resolve eq6463 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6463
  have eq6493 : ∀ X0 X1 : G, (τ (σ X1)) = (M.op (τ (σ X1)) X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6480 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6480
    | (have j0 := eq6480 X0 X1
       grind)
    | exact resolve eq6480 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6480
  have eq6502 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6493 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6493
    | (have j0 := eq6493 X0 X1
       grind)
    | exact resolve eq6493 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6493
  have eq6524 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6502 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq6502
    | (have j0 := eq6502 (σ X0) (σ X1)
       grind)
    | exact resolve eq6502 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6502
  have eq83142 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq949 x y
       grind)
    | exact superpose eq949 eq16
    | (have j1 := eq949 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq949 x y
       grind)
    | exact resolve eq16 eq949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq949
  have eq83172 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq83142
  have eq83203 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq83172
       grind)
    | exact superpose eq83172 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq83172
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq83172
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq83172
       grind)
    | exact resolve eq12 eq83172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83204 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) X1)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X1 (σ x) X0 (σ y)
       have i₂ := eq83172
       grind)
    | exact superpose eq83172 eq63
    | exact resolve eq63 eq83172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83205 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq83203
  have eq83211 : (M.op (σ x) (σ x)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq83205
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq83205
    | exact resolve eq83205 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83205
  have eq83213 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq14 eq83211
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq83211 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83211
  have eq83275 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq83204 X0 (σ x)
       have i₂ := eq83172
       grind)
    | exact superpose eq83172 eq83204
    | exact resolve eq83204 eq83172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83172 eq83204
  have eq83294 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq83275 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83275
  have eq83317 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq83294 (σ x)
       grind)
    | exact superpose eq83294 eq16
    | exact resolve eq16 eq83294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83294
  have eq83327 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq83317
       have r₂ := eq83213
       grind)
    | exact resolve eq83317 eq83213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83213 eq83317
  have eq83340 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq83327
       grind)
    | exact superpose eq83327 eq16
    | exact resolve eq16 eq83327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83344 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq83327
       grind)
    | exact superpose eq83327 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq83327
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq83327
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq83327
       grind)
    | exact resolve eq12 eq83327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83345 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X1)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X1 (σ y) X0 (σ x)
       have i₂ := eq83327
       grind)
    | exact superpose eq83327 eq63
    | exact resolve eq63 eq83327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83346 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq83344
  have eq83351 : (σ (k y x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq83346
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq83346
    | exact resolve eq83346 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83346
  have eq83353 : (σ (M.op y x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq14 eq83351
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq83351 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83351
  have eq83359 : (τ (σ (M.op y x))) = (k y y) ∨ (σ y) = (σ (M.op y x)) ∨ (σ y) = (σ (M.op y x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq974 y y
       have i₂ := eq83353
       grind)
    | exact superpose eq83353 eq974
    | exact resolve eq974 eq83353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974
  have eq83373 : (τ (σ (M.op y x))) = (k y y) ∨ (σ y) = (σ (M.op y x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq83359
  have eq83383 : (M.op y x) = (k y y) ∨ (σ y) = (σ (M.op y x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq83373
       have i₂ := eq10 (M.op y x)
       grind)
    | exact superpose eq10 eq83373
    | exact resolve eq83373 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83373
  have eq83391 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq83345 X0 (σ y)
       have i₂ := eq83327
       grind)
    | exact superpose eq83327 eq83345
    | exact resolve eq83345 eq83327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83345
  have eq83410 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq83391 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83391
  have eq83434 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq83327
       have i₂ := eq83410 (σ x)
       grind)
    | exact superpose eq83410 eq83327
    | exact resolve eq83327 eq83410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83327
  have eq83436 : (M.op (σ y) (σ x)) = (σ (M.op y x)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq83353
       have i₂ := eq83410 (σ y)
       grind)
    | exact superpose eq83410 eq83353
    | exact resolve eq83353 eq83410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83353 eq83410
  have eq83440 : (M.op (σ y) (σ x)) = (σ (M.op y x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq83436
  have eq83441 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq83434
  have eq83456 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq12 (σ x) (σ x)
       have i₂ := eq83441
       grind)
    | exact superpose eq83441 eq12
    | (have r₁ := eq12 (σ x) (σ x)
       have r₂ := eq83441
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq83441
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq83441
       grind)
    | exact resolve eq12 eq83441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83458 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq83456
  have eq83462 : (σ x) = (σ (k x x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq83458
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq83458
    | exact resolve eq83458 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83458
  have eq83464 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq83462
       have i₂ := eq14 x x
       grind)
    | exact superpose eq14 eq83462
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq83462 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83473 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq10 (k x x)
       have i₂ := eq83462
       grind)
    | exact superpose eq83462 eq10
    | exact resolve eq10 eq83462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83462
  have eq83563 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x x) := by grind
  clear eq83464
  have eq83632 : y = (M.op y x) ∨ x = (M.op x y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq83473
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq83473
    | exact resolve eq83473 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83473
  have eq83637 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op y X1)) ∨ x = (M.op x y) ∨ x = (k x x) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X1 x X0 y
       have i₂ := eq83632
       grind)
    | exact superpose eq83632 eq63
    | exact resolve eq63 eq83632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83681 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ x = (M.op x y) ∨ x = (k x x) ∨ x = (M.op x y) ∨ x = (k x x) := by
    intro X0
    first
    | (have i₁ := eq83637 X0 x
       have i₂ := eq83632
       grind)
    | exact superpose eq83632 eq83637
    | exact resolve eq83637 eq83632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83632 eq83637
  have eq83701 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ x = (M.op x y) ∨ x = (k x x) := by
    intro X0
    first
    | (have j0 := eq83681 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83681
  have eq83720 : (σ x) ≠ (σ (M.op x x)) ∨ x = (M.op x x) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq83340
       have i₂ := eq83701 x
       grind)
    | exact superpose eq83701 eq83340
    | exact resolve eq83340 eq83701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83701
  have eq83724 : (σ x) ≠ (σ (M.op x x)) ∨ x = (M.op x x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq5429 x
       grind)
    | (have r₁ := eq83720
       have r₂ := eq5429 x
       grind)
    | exact resolve eq83720 eq5429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5429 eq83720
  have eq83728 : y = (M.op y x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq83724
       have r₂ := eq83563
       grind)
    | exact resolve eq83724 eq83563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83563 eq83724
  have eq83895 : (σ y) ≠ (σ (M.op y x)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq83440
       grind)
    | exact superpose eq83440 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq83440
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq83440
       grind)
    | exact resolve eq12 eq83440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83440
  have eq83897 : (M.op (σ x) (σ x)) = (σ (k x y)) ∨ (σ y) ≠ (σ (M.op y x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq83895
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq83895
    | exact resolve eq83895 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83895
  have eq83899 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ y) ≠ (σ (M.op y x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq14 eq83897
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq83897 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83897
  have eq83901 : (σ (M.op x y)) = (σ x) ∨ (σ y) ≠ (σ (M.op y x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq83441 eq83899
    | exact resolve eq83899 eq83441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83441 eq83899
  have eq83902 : (σ y) ≠ (σ (M.op y x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq83901
       have r₂ := eq83340
       grind)
    | exact resolve eq83901 eq83340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83340 eq83901
  have eq92070 : (M.op y x) = (k y y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq83383
       have r₂ := eq83902
       grind)
    | exact resolve eq83383 eq83902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83383 eq83902
  have eq92083 : (M.op y x) = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq14 y y
       have i₂ := eq92070
       grind)
    | exact superpose eq92070 eq14
    | (have j0 := eq14 y y
       grind)
    | exact resolve eq14 eq92070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92100 : (M.op y x) = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq92083
  have eq92120 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op (M.op y x) X1)) ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X1 y X0 y
       have i₂ := eq92100
       grind)
    | exact superpose eq92100 eq63
    | exact resolve eq63 eq92100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92100
  have eq92131 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq92120 X0 x
       have i₂ := eq63 x x X0 y
       grind)
    | exact superpose eq63 eq92120
    | exact resolve eq92120 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92120
  have eq92165 : x ≠ (M.op x x) ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq92131
  have eq92186 : y = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq92165
       have r₂ := eq83728
       grind)
    | exact resolve eq92165 eq83728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83728 eq92165
  have eq92203 : y ≠ y ∨ y = (k y y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq12 y y
       have i₂ := eq92186
       grind)
    | exact superpose eq92186 eq12
    | (have r₁ := eq12 y y
       have r₂ := eq92186
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq92186
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq92186
       grind)
    | exact resolve eq12 eq92186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92186
  have eq92205 : y = (k y y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq92203
  have eq92214 : y = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq92205 eq92070
    | exact resolve eq92070 eq92205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92070 eq92205
  have eq92264 : y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq92214
  have eq92273 : y ≠ y ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq92264
       grind)
    | exact superpose eq92264 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq92264
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq92264
       grind)
    | exact resolve eq13 eq92264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92274 : y ≠ y ∨ (k x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq92264
       grind)
    | exact superpose eq92264 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq92264
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq92264
       grind)
    | exact resolve eq12 eq92264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92275 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op y X1)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X1 x X0 y
       have i₂ := eq92264
       grind)
    | exact superpose eq92264 eq63
    | exact resolve eq63 eq92264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92276 : (k x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq92274
  have eq92277 : y ≠ y ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) := by grind
  clear eq92273
  have eq92278 : (M.op x y) = (k y x) ∨ x = (M.op x y) := by grind
  clear eq92277
  have eq92289 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq270 x y
       have i₂ := eq92276
       grind)
    | exact superpose eq92276 eq270
    | (have j0 := eq270 x y
       grind)
    | exact resolve eq270 eq92276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92334 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq92275 X0 x
       have i₂ := eq92264
       grind)
    | exact superpose eq92264 eq92275
    | exact resolve eq92275 eq92264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92275
  have eq92388 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq92334 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92334
  have eq92396 : (k y x) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq92388 eq92278
    | exact resolve eq92278 eq92388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92278
  have eq92405 : ∀ X0 : G, (M.op X0 x) ≠ X0 ∨ (M.op y y) = (k y X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq12 y X0
       have i₂ := eq92388 X0
       grind)
    | exact superpose eq92388 eq12
    | (have j0 := eq12 x X0
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq92388 X0
       grind)
    | exact resolve eq12 eq92388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92457 : y ≠ y ∨ (M.op y y) = (k y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq92405 y
       have i₂ := eq92264
       grind)
    | exact superpose eq92264 eq92405
    | (have j0 := eq92405 y
       grind)
    | (have r₁ := eq92405 y
       have r₂ := eq92264
       grind)
    | exact resolve eq92405 eq92264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92405
  have eq92458 : y ≠ y ∨ (M.op y y) = (k y y) ∨ x = (M.op x y) := by grind
  clear eq92457
  have eq92459 : (M.op y y) = (k y y) ∨ x = (M.op x y) := by grind
  clear eq92458
  have eq92460 : (M.op y x) = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq92388 eq92459
    | exact resolve eq92459 eq92388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92459
  have eq92461 : y = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq92264 eq92460
    | exact resolve eq92460 eq92264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92264 eq92460
  have eq92481 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6524 y y
       have i₂ := eq92461
       grind)
    | exact superpose eq92461 eq6524
    | (have j0 := eq6524 y y
       grind)
    | exact resolve eq6524 eq92461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92461
  have eq92482 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq92481
  have eq92483 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq92482
  have eq434588 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq92289
       grind)
    | exact superpose eq92289 eq16
    | exact resolve eq16 eq92289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92289
  have eq434687 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq92388 eq434588
    | exact resolve eq434588 eq92388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434588
  have eq434688 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq434687
  have eq434722 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq434688
       grind)
    | exact superpose eq434688 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq434688
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq434688
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq434688
       grind)
    | exact resolve eq13 eq434688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434688
  have eq434751 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq434722
  have eq434752 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq434751
  have eq434767 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq434752
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq434752
    | exact resolve eq434752 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434752
  have eq434775 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq92396 eq434767
    | exact resolve eq434767 eq92396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434767
  have eq434787 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq434775
       grind)
    | exact superpose eq434775 eq16
    | exact resolve eq16 eq434775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434775
  have eq434857 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq92388 eq434787
    | exact resolve eq434787 eq92388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434787
  have eq434858 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq434857
  have eq434871 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq434858
       grind)
    | exact superpose eq434858 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq434858
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq434858
       grind)
    | exact resolve eq12 eq434858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq434873 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X1)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X1 (σ y) X0 (σ x)
       have i₂ := eq434858
       grind)
    | exact superpose eq434858 eq63
    | exact resolve eq63 eq434858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq434904 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq434871
  have eq434914 : (σ (k y x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq434904
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq434904
    | exact resolve eq434904 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434904
  have eq434918 : (σ (M.op x x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq92396 eq434914
    | exact resolve eq434914 eq92396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92396 eq434914
  have eq434919 : (σ y) = (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq92483 eq434918
    | exact resolve eq434918 eq92483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434918
  have eq434932 : (τ (σ y)) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq434919
       grind)
    | exact superpose eq434919 eq10
    | exact resolve eq10 eq434919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434919
  have eq435210 : y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq434932
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq434932
    | exact resolve eq434932 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434932
  have eq435226 : y = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq435210 eq92276
    | exact resolve eq92276 eq435210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92276
  have eq436621 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq434873 X0 (σ y)
       have i₂ := eq434858
       grind)
    | exact superpose eq434858 eq434873
    | exact resolve eq434873 eq434858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434858 eq434873
  have eq436963 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq436621 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436621
  have eq437129 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq436963 (σ x)
       grind)
    | exact superpose eq436963 eq16
    | exact resolve eq16 eq436963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq437130 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq92483
       have i₂ := eq436963 (σ y)
       grind)
    | exact superpose eq436963 eq92483
    | exact resolve eq92483 eq436963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92483 eq436963
  have eq437284 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq437130
  have eq437323 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq92388 eq437129
    | exact resolve eq437129 eq92388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92388 eq437129
  have eq437371 : (σ y) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq435210 eq437323
    | exact resolve eq437323 eq435210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435210 eq437323
  have eq437403 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq437284
       grind)
    | exact superpose eq437284 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq437284
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq437284
       grind)
    | exact resolve eq12 eq437284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437284
  have eq437434 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq437403
  have eq437443 : (M.op (σ x) (σ x)) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq437434
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq437434
    | exact resolve eq437434 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437434
  have eq437448 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq435226 eq437443
    | exact resolve eq437443 eq435226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435226 eq437443
  have eq437451 : x = (M.op x y) := by
    first
    | (have r₁ := eq437448
       have r₂ := eq437371
       grind)
    | exact resolve eq437448 eq437371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437371 eq437448
  have eq437454 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq437451
       grind)
    | exact superpose eq437451 eq16
    | exact resolve eq16 eq437451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq437455 : x ≠ x ∨ (k y x) = (M.op y y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq437451
       grind)
    | exact superpose eq437451 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq437451
       grind)
    | exact resolve eq12 eq437451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq437456 : x ≠ x ∨ y = (M.op y x) ∨ (M.op y x) = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq437451
       grind)
    | exact superpose eq437451 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq437451
       grind)
    | exact resolve eq13 eq437451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq437457 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X1 y X0 x
       have i₂ := eq437451
       grind)
    | exact superpose eq437451 eq63
    | exact resolve eq63 eq437451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq437475 : (M.op y x) = (k x y) ∨ y = (M.op y x) := by grind
  clear eq437456
  have eq437476 : (k y x) = (M.op y y) := by grind
  clear eq437455
  have eq437500 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq437457 X0 y
       have i₂ := eq437451
       grind)
    | exact superpose eq437451 eq437457
    | exact resolve eq437457 eq437451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437457
  have eq437607 : x = (M.op x x) := by
    first
    | (have i₁ := eq437451
       have i₂ := eq437500 x
       grind)
    | exact superpose eq437500 eq437451
    | exact resolve eq437451 eq437500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437451
  have eq437608 : (M.op y x) = (k y x) := by
    first
    | (have i₁ := eq437476
       have i₂ := eq437500 y
       grind)
    | exact superpose eq437500 eq437476
    | exact resolve eq437476 eq437500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437476 eq437500
  have eq437707 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq12 x x
       have i₂ := eq437607
       grind)
    | exact superpose eq437607 eq12
    | (have r₁ := eq12 x x
       have r₂ := eq437607
       grind)
    | exact resolve eq12 eq437607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437607
  have eq437725 : x = (k x x) := by grind
  clear eq437707
  have eq437748 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq6524 x x
       have i₂ := eq437725
       grind)
    | exact superpose eq437725 eq6524
    | (have j0 := eq6524 x x
       grind)
    | exact resolve eq6524 eq437725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6524 eq437725
  have eq437760 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq437748
  have eq437761 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq437760
  have eq437795 : (M.op (σ y) (σ x)) = (σ (M.op y x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq270 y x
       have i₂ := eq437608
       grind)
    | exact superpose eq437608 eq270
    | (have j0 := eq270 y x
       grind)
    | exact resolve eq270 eq437608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq437802 : (σ y) ≠ (σ (M.op y x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5880 y x
       have i₂ := eq437608
       grind)
    | exact superpose eq437608 eq5880
    | (have j0 := eq5880 y x
       grind)
    | exact resolve eq5880 eq437608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5880
  have eq437814 : (σ y) ≠ (σ (M.op y x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq437802
       have r₂ := eq437454
       grind)
    | exact resolve eq437802 eq437454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437802
  have eq437815 : (M.op (σ y) (σ x)) = (σ (M.op y x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq437795
       have r₂ := eq437454
       grind)
    | exact resolve eq437795 eq437454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437795
  have eq438254 : (M.op (σ x) (σ y)) = (σ (M.op y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq270 x y
       have i₂ := eq437475
       grind)
    | exact superpose eq437475 eq270
    | (have j0 := eq270 x y
       grind)
    | exact resolve eq270 eq437475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270 eq437475
  have eq438280 : (M.op (σ x) (σ y)) = (σ (M.op y x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq438254
       have r₂ := eq437454
       grind)
    | exact resolve eq438254 eq437454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438254
  have eq440225 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ (M.op y x)) X1)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X1 (σ x) X0 (σ y)
       have i₂ := eq437815
       grind)
    | exact superpose eq437815 eq63
    | exact resolve eq63 eq437815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437815
  have eq477799 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ (M.op y x)) X1)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X1 (σ y) X0 (σ x)
       have i₂ := eq438280
       grind)
    | exact superpose eq438280 eq63
    | exact resolve eq63 eq438280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438280
  have eq477847 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq440225 eq477799
    | exact resolve eq477799 eq440225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440225 eq477799
  have eq477977 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq437454
       have i₂ := eq477847 (σ x)
       grind)
    | exact superpose eq477847 eq437454
    | exact resolve eq437454 eq477847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477847
  have eq478031 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq477977
       have r₂ := eq437761
       grind)
    | exact resolve eq477977 eq437761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477977
  have eq478119 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq478031 eq437814
    | exact resolve eq437814 eq478031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437814 eq478031
  have eq478149 : (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq478119
  have eq478165 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq478149
       grind)
    | exact superpose eq478149 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq478149
       grind)
    | exact resolve eq13 eq478149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq478166 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X1 (σ x) X0 (σ y)
       have i₂ := eq478149
       grind)
    | exact superpose eq478149 eq63
    | exact resolve eq63 eq478149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq478184 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq478165
  have eq478187 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq478184
       have r₂ := eq437454
       grind)
    | exact resolve eq478184 eq437454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478184
  have eq478190 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq478187
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq478187
    | exact resolve eq478187 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478187
  have eq478192 : (M.op (σ x) (σ y)) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq478190
       have i₂ := eq437608
       grind)
    | exact superpose eq437608 eq478190
    | exact resolve eq478190 eq437608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437608 eq478190
  have eq478571 : (σ x) ≠ (σ (M.op y x)) := by
    first
    | (have i₁ := eq437454
       have i₂ := eq478192
       grind)
    | exact superpose eq478192 eq437454
    | exact resolve eq437454 eq478192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437454
  have eq478700 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq478166 X0 (σ x)
       have i₂ := eq478149
       grind)
    | exact superpose eq478149 eq478166
    | exact resolve eq478166 eq478149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478149 eq478166
  have eq478861 : (σ (M.op y x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq478192
       have i₂ := eq478700 (σ x)
       grind)
    | exact superpose eq478700 eq478192
    | exact resolve eq478192 eq478700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478192 eq478700
  have eq479013 : (σ x) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq478861
       have i₂ := eq437761
       grind)
    | exact superpose eq437761 eq478861
    | exact resolve eq478861 eq437761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437761 eq478861
  have eq479032 : False := by grind
  exact eq479032
