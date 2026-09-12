import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation418`: `x = x ◇ (x ◇ (y ◇ (x ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if m(X,X) = m(X,Y) then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pxy_pyy_y_pxy_Equation418 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law418 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law418.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op a b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
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
  have eq46 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq13
    | (have j0 := eq13 X0 X1
       grind)
    | exact resolve eq13 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq46 X0 X1
       have i₂ := eq35 X1
       grind)
    | exact superpose eq35 eq46
    | (have j0 := eq46 X0 X1
       grind)
    | (have r₁ := eq46 X0 X0
       have r₂ := eq35 X0
       grind)
    | exact resolve eq46 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq84 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq85 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) X1) ∨ (τ X0) = (M.op X1 X1) := by
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
  have eq86 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) X1) ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq85 X0 X1
       have i₂ := eq35 (τ X0)
       grind)
    | exact superpose eq35 eq85
    | (have j0 := eq85 X0 X1
       grind)
    | exact resolve eq85 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq87 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq84 X0 X1
       have i₂ := eq35 (σ X0)
       grind)
    | exact superpose eq35 eq84
    | (have j0 := eq84 X0 X1
       grind)
    | exact resolve eq84 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq90 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) X1) ∨ (τ X0) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq86 X0 X1
       have i₂ := eq35 X1
       grind)
    | exact superpose eq35 eq86
    | (have j0 := eq86 X0 X1
       grind)
    | exact resolve eq86 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq91 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq87 X0 X1
       have i₂ := eq35 (σ X1)
       grind)
    | exact superpose eq35 eq87
    | (have j0 := eq87 X0 X1
       grind)
    | exact resolve eq87 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
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
  have eq100 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) (σ X1)) = X0 := by
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
  have eq104 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq100 X0 X1
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq100
    | (have j0 := eq100 X0 X1
       grind)
    | exact resolve eq100 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq108 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 (σ X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq104 X0 X1
       have i₂ := eq35 (σ X1)
       grind)
    | exact superpose eq35 eq104
    | (have j0 := eq104 X0 X1
       grind)
    | exact resolve eq104 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq127 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 ∨ (σ X1) = X0 := by
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
  have eq136 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X1) = (k (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq91 X0 X1
       grind)
    | exact superpose eq91 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq91 X0 X1
       grind)
    | exact resolve eq13 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (M.op (σ X0) (M.op X2 (σ (k X0 X1))))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X2 (σ X1)
       have i₂ := eq91 X0 X1
       grind)
    | exact superpose eq91 eq9
    | (have j1 := eq91 X0 X1
       grind)
    | exact resolve eq9 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq139 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X1) = (k (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq136 X0 X1
       have j1 := eq50 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq136 X0 X1
       have r₂ := eq50 (σ (k X0 X1)) (M.op (σ X0) (σ X0))
       grind)
    | (have r₁ := eq136 X0 X1
       have r₂ := eq50 (M.op (σ X0) (σ X0)) (σ (k X0 X1))
       grind)
    | (have r₁ := eq136 X0 X0
       have r₂ := eq50 (σ X0) (σ X0)
       grind)
    | exact resolve eq136 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq141 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq127 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq127
    | (have j0 := eq127 X0 X1
       grind)
    | exact resolve eq127 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq142 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (k (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq139 X0 X1
       have i₂ := eq35 (σ X0)
       grind)
    | exact superpose eq35 eq139
    | (have j0 := eq139 X0 X1
       grind)
    | exact resolve eq139 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq143 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ X1) ∨ (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq142 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq142
    | (have j0 := eq142 X0 X1
       grind)
    | exact resolve eq142 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq144 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq143 X0 X1
       have i₂ := eq35 (σ X1)
       grind)
    | exact superpose eq35 eq143
    | (have j0 := eq143 X0 X1
       grind)
    | exact resolve eq143 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq145 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq144 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq532 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq141 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq141
    | exact resolve eq141 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq693 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq145 (τ X1) (τ X0)
       have i₂ := eq94 X0 X1
       grind)
    | exact superpose eq94 eq145
    | (have j0 := eq145 (τ X1) (τ (k X0 X1))
       grind)
    | exact resolve eq145 eq94
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
  have eq711 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ X1)) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (σ (τ X1)) := by
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
  have eq712 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (σ (τ X1)) := by
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
  have eq713 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (k X0 X1) = X1 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq712 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq712
    | (have j0 := eq712 X0 X1
       grind)
    | exact resolve eq712 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712
  have eq714 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq713 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq713
    | (have j0 := eq713 X0 X1
       grind)
    | exact resolve eq713 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713
  have eq722 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X1)) ∨ (τ X1) = (τ (k X0 X1)) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq714 (τ X1) (τ X0)
       have i₂ := eq94 X0 X1
       grind)
    | exact superpose eq94 eq714
    | (have j0 := eq714 (τ X1) (τ (k X0 X1))
       grind)
    | exact resolve eq714 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714
  have eq1212 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = X1 ∨ (k (τ X0) X1) = X1 ∨ (τ X0) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq50 (τ X0) X1
       have i₂ := eq90 X0 X1
       grind)
    | exact superpose eq90 eq50
    | (have j0 := eq50 (τ X0) X1
       have j1 := eq90 X0 X1
       grind)
    | (have r₁ := eq50 (τ X0) X1
       have r₂ := eq90 X0 X1
       grind)
    | (have r₁ := eq50 (τ X0) X1
       have r₂ := eq90 X0 (M.op (τ X0) X1)
       grind)
    | exact resolve eq50 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq90
  have eq1224 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = X1 ∨ (k (τ X0) X1) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1212 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1212
  have eq1225 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1224 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1224
  have eq1276 : ∀ X0 X1 : G, (σ (M.op (k (τ X0) X1) (k (τ X0) X1))) = (k (σ (M.op (k (τ X0) X1) (k (τ X0) X1))) (M.op X0 (σ X1))) ∨ (M.op X0 (σ X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq25 (M.op X0 (σ X1))
       have i₂ := eq108 X0 X1
       grind)
    | exact superpose eq108 eq25
    | (have j1 := eq108 X0 X1
       grind)
    | exact resolve eq25 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq1282 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k (σ (k (τ X0) X1)) (M.op X0 (σ X1))) ∨ (M.op X0 (σ X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1276 X0 X1
       have i₂ := eq35 (k (τ X0) X1)
       grind)
    | exact superpose eq35 eq1276
    | (have j0 := eq1276 X0 X1
       grind)
    | exact resolve eq1276 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1276
  have eq1286 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (k X0 (σ X1)) = (k (k X0 (σ X1)) (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1282 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq1282
    | (have j0 := eq1282 X0 X1
       grind)
    | exact resolve eq1282 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1282
  have eq1988 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (M.op X0 (σ (k x y))))) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq137 x y X0
       grind)
    | exact superpose eq137 eq16
    | (have j1 := eq137 x y X0
       grind)
    | exact resolve eq16 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq3596 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1225 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1225
    | exact resolve eq1225 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1225
  have eq3662 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3596 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3596
    | (have j0 := eq3596 X0 X1
       grind)
    | exact resolve eq3596 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3596
  have eq3705 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq3662 X0 X1
       grind)
    | exact superpose eq3662 eq10
    | (have j1 := eq3662 X0 X1
       grind)
    | exact resolve eq10 eq3662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3662
  have eq3763 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3705 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq3705
    | (have j0 := eq3705 X0 X1
       grind)
    | exact resolve eq3705 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3705
  have eq3822 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3763 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3763
    | (have j0 := eq3763 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq3763 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3866 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 X1
       have i₂ := eq3763 (σ X0) X1
       grind)
    | exact superpose eq3763 eq30
    | (have j1 := eq3763 (σ X0) X1
       grind)
    | exact resolve eq30 eq3763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq3763
  have eq6324 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (σ X1) X0
       have i₂ := eq3866 X1 (σ X0)
       grind)
    | exact superpose eq3866 eq23
    | (have j1 := eq3866 X1 (σ X0)
       grind)
    | exact resolve eq23 eq3866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq3866
  have eq6392 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6324 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq6324
    | (have j0 := eq6324 X0 X1
       grind)
    | exact resolve eq6324 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6324
  have eq6428 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6392 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6392
    | (have j0 := eq6392 X0 X1
       grind)
    | exact resolve eq6392 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6392
  have eq6435 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ (k X1 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6428 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6428
    | (have j0 := eq6428 X0 X1
       grind)
    | exact resolve eq6428 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6428
  have eq7184 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (k (τ X0) X1) = X1 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6435 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6435
    | (have j0 := eq6435 X1 (τ X0)
       grind)
    | exact resolve eq6435 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7234 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X1 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq6435 X1 X0
       grind)
    | exact superpose eq6435 eq11
    | (have j1 := eq6435 X1 X0
       grind)
    | exact resolve eq11 eq6435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6435
  have eq7397 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (k (τ X0) X1) = X1 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 (σ X1))
       have i₂ := eq7184 X0 X1
       grind)
    | exact superpose eq7184 eq11
    | (have j1 := eq7184 X0 X1
       grind)
    | exact resolve eq11 eq7184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7184
  have eq7475 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k (τ X0) X1) = X1 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7397 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq7397
    | (have j0 := eq7397 X0 X1
       grind)
    | exact resolve eq7397 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7397
  have eq7496 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (τ X0) = (k (τ X1) (τ X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7475 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7475
    | (have j0 := eq7475 X1 (τ X0)
       grind)
    | exact resolve eq7475 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7475
  have eq7611 : ∀ X0 X1 : G, (τ X0) = (τ (k X1 X0)) ∨ (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7496 X0 X1
       have i₂ := eq94 X0 X1
       grind)
    | exact superpose eq94 eq7496
    | (have j0 := eq7496 X0 X1
       grind)
    | exact resolve eq7496 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq7496
  have eq7709 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) (k X1 X0)) ∨ (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq25 (k X1 X0)
       have i₂ := eq7611 X0 X1
       grind)
    | exact superpose eq7611 eq25
    | (have j1 := eq7611 X0 X1
       grind)
    | exact resolve eq25 eq7611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq7611
  have eq7823 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X0)) (k X1 X0)) ∨ (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7709 X0 X1
       have i₂ := eq35 (τ X0)
       grind)
    | exact superpose eq35 eq7709
    | (have j0 := eq7709 X0 X1
       grind)
    | exact resolve eq7709 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7709
  have eq7839 : ∀ X0 X1 : G, (k X0 (k X1 X0)) = X0 ∨ (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7823 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7823
    | (have j0 := eq7823 X0 X1
       grind)
    | exact resolve eq7823 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7823
  have eq7885 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X1 X0)) ∨ (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq145 X0 (k X1 X0)
       have i₂ := eq7839 X0 X1
       grind)
    | exact superpose eq7839 eq145
    | (have j0 := eq145 X1 X0
       have j1 := eq7839 X0 X1
       grind)
    | (have r₁ := eq145 X0 X1
       have r₂ := eq7839 (σ X0) (σ (k X0 X1))
       grind)
    | (have r₁ := eq145 X0 X1
       have r₂ := eq7839 (σ (k X0 X1)) (σ X0)
       grind)
    | exact resolve eq145 eq7839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145 eq7839
  have eq7971 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ (k X1 X0)) ∨ (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq7885 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7885
  have eq7972 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X0)) ∨ (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq7971 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7971
  have eq8184 : ∀ X0 X1 : G, (k (τ X1) X0) = (M.op (τ X1) X0) ∨ (σ X0) = (k X1 (σ X0)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq7972 X0 (τ X1)
       grind)
    | exact superpose eq7972 eq18
    | (have j1 := eq7972 X0 (τ X1)
       grind)
    | exact resolve eq18 eq7972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq7972
  have eq9512 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7234 x y
       grind)
    | exact superpose eq7234 eq16
    | (have j1 := eq7234 x y
       grind)
    | exact resolve eq16 eq7234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7234
  have eq9707 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq9512
       have i₂ := eq532 y x
       grind)
    | exact superpose eq532 eq9512
    | (have j1 := eq532 y x
       grind)
    | (have r₁ := eq9512
       have r₂ := eq532 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq9512
       have r₂ := eq532 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq9512 eq532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9512
  have eq9716 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq9707
  have eq9902 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9716
       grind)
    | exact superpose eq9716 eq16
    | exact resolve eq16 eq9716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9716
  have eq9903 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq9902
       have i₂ := eq35 (σ x)
       grind)
    | exact superpose eq35 eq9902
    | exact resolve eq9902 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9902
  have eq9904 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq9903
       have i₂ := eq35 x
       grind)
    | exact superpose eq35 eq9903
    | exact resolve eq9903 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9903
  have eq9905 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq9904
  have eq10000 : x = (M.op x y) ∨ x = (M.op x (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq39 x y
       have i₂ := eq9905
       grind)
    | exact superpose eq9905 eq39
    | exact resolve eq39 eq9905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10013 : x ≠ y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  have eq10108 : x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq10000
       have i₂ := eq9905
       grind)
    | exact superpose eq9905 eq10000
    | exact resolve eq10000 eq9905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9905 eq10000
  have eq10128 : x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq10108
  have eq10131 : x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq10128
       have r₂ := eq10013
       grind)
    | exact resolve eq10128 eq10013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10013 eq10128
  have eq10641 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (M.op X0 (σ (k x y))))) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq1988 X0
       have i₂ := eq10131
       grind)
    | exact superpose eq10131 eq1988
    | (have j0 := eq1988 X0
       grind)
    | exact resolve eq1988 eq10131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1988 eq10131
  have eq10647 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (M.op X0 (σ (k x y))))) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq10641 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10641
  have eq10648 : ∀ X0 : G, (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (M.op X0 (σ (k x y))))) := by
    intro X0
    first
    | (have j0 := eq10647 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10647
  have eq12135 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) ∨ (σ (τ X1)) = (k X0 (σ (τ X1))) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 (τ X0)
       have i₂ := eq8184 (τ X1) X0
       grind)
    | exact superpose eq8184 eq19
    | (have j1 := eq8184 (τ X1) X0
       grind)
    | exact resolve eq19 eq8184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq8184
  have eq12187 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (σ (τ X1)) = (k X0 (σ (τ X1))) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12135 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq12135
    | (have j0 := eq12135 X0 X1
       grind)
    | exact resolve eq12135 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12135
  have eq12231 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X0 X1) = X1 ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12187 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq12187
    | (have j0 := eq12187 X0 X1
       grind)
    | exact resolve eq12187 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12187
  have eq12532 : ∀ X0 : G, y = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (M.op X0 (σ (k x y))))) := by
    intro X0
    first
    | (have i₁ := eq10 y
       have i₂ := eq10648 X0
       grind)
    | exact superpose eq10648 eq10
    | (have j1 := eq10648 X0
       grind)
    | exact resolve eq10 eq10648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10648
  have eq12615 : ∀ X0 : G, x = y ∨ (σ x) = (M.op (σ x) (M.op (σ x) (M.op X0 (σ (k x y))))) := by
    intro X0
    first
    | (have i₁ := eq12532 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq12532
    | (have j0 := eq12532 X0
       grind)
    | exact resolve eq12532 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12532
  have eq12617 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (M.op X0 (σ (k x y))))) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq12615 X0
       grind)
    | exact superpose eq12615 eq16
    | (have j1 := eq12615 X0
       grind)
    | exact resolve eq16 eq12615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12615
  have eq12618 : ∀ X0 : G, (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (M.op X0 (σ (k x y))))) := by
    intro X0
    first
    | (have i₁ := eq12617 X0
       have i₂ := eq35 (σ x)
       grind)
    | exact superpose eq35 eq12617
    | (have j0 := eq12617 X0
       grind)
    | exact resolve eq12617 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12617
  have eq12619 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (M.op X0 (σ (k x y))))) := by
    intro X0
    first
    | (have i₁ := eq12618 X0
       have i₂ := eq35 x
       grind)
    | exact superpose eq35 eq12618
    | (have j0 := eq12618 X0
       grind)
    | exact resolve eq12618 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12618
  have eq12620 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) (M.op X0 (σ (k x y))))) := by
    intro X0
    first
    | (have j0 := eq12619 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12619
  have eq12721 : (σ x) = (M.op (σ x) (M.op (σ x) (σ (k x y)))) := by
    first
    | (have i₁ := eq12620 (σ (k x y))
       have i₂ := eq35 (σ (k x y))
       grind)
    | exact superpose eq35 eq12620
    | exact resolve eq12620 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12620
  have eq13184 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k (σ X0) X1) = X1 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12231 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq12231
    | (have j0 := eq12231 (σ X0) X1
       grind)
    | exact resolve eq12231 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12231
  have eq13324 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13184 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13184
    | (have j0 := eq13184 X1 (σ X0)
       grind)
    | exact resolve eq13184 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13184
  have eq13445 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13324 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq13324
    | (have j0 := eq13324 X0 X1
       grind)
    | exact resolve eq13324 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13324
  have eq13450 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ (k X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13445 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq13445
    | (have j0 := eq13445 X0 X1
       grind)
    | exact resolve eq13445 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13445
  have eq13684 : ∀ X0 X1 : G, (σ X1) ≠ (σ (M.op X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq13450 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52841 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3822 x y
       grind)
    | exact superpose eq3822 eq16
    | (have j1 := eq3822 x y
       grind)
    | exact resolve eq16 eq3822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3822
  have eq53315 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) ∨ x = y := by
    first
    | (have i₁ := eq52841
       have i₂ := eq13450 y x
       grind)
    | exact superpose eq13450 eq52841
    | (have j1 := eq13450 y x
       grind)
    | (have r₁ := eq52841
       have r₂ := eq13450 y x
       grind)
    | (have r₁ := eq52841
       have r₂ := eq13450 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq52841
       have r₂ := eq13450 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq52841 eq13450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13450 eq52841
  have eq53320 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) ∨ x = y := by grind
  clear eq53315
  have eq53325 : x = y ∨ (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq13684 x y
       grind)
    | (have r₁ := eq53320
       have r₂ := eq13684 x y
       grind)
    | exact resolve eq53320 eq13684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13684 eq53320
  have eq53327 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq53325
       grind)
    | exact superpose eq53325 eq16
    | exact resolve eq16 eq53325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53325
  have eq53338 : (σ x) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq53327
       have i₂ := eq35 (σ x)
       grind)
    | exact superpose eq35 eq53327
    | exact resolve eq53327 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53327
  have eq53340 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq53338
       have i₂ := eq35 x
       grind)
    | exact superpose eq35 eq53338
    | exact resolve eq53338 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53338
  have eq53341 : (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) := by grind
  clear eq53340
  have eq53479 : y = (τ (σ x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq53341
       grind)
    | exact superpose eq53341 eq10
    | exact resolve eq10 eq53341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53341
  have eq53614 : x = y ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq53479
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq53479
    | exact resolve eq53479 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53479
  have eq53617 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq53614
       grind)
    | exact superpose eq53614 eq16
    | exact resolve eq16 eq53614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53614
  have eq53628 : (σ x) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq53617
       have i₂ := eq35 (σ x)
       grind)
    | exact superpose eq35 eq53617
    | exact resolve eq53617 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53617
  have eq53630 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq53628
       have i₂ := eq35 x
       grind)
    | exact superpose eq35 eq53628
    | exact resolve eq53628 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53628
  have eq53631 : (σ y) = (σ (k x y)) := by grind
  clear eq53630
  have eq53923 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq12721
       have i₂ := eq53631
       grind)
    | exact superpose eq53631 eq12721
    | exact resolve eq12721 eq53631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12721
  have eq53936 : (k x y) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq53631
       grind)
    | exact superpose eq53631 eq10
    | exact resolve eq10 eq53631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54073 : y = (k x y) := by
    first
    | (have i₁ := eq53936
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq53936
    | exact resolve eq53936 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53936
  have eq54099 : x = y ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq532 y x
       have i₂ := eq54073
       grind)
    | exact superpose eq54073 eq532
    | (have j0 := eq532 y x
       grind)
    | exact resolve eq532 eq54073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532 eq54073
  have eq57787 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq54099
       grind)
    | exact superpose eq54099 eq16
    | exact resolve eq16 eq54099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54099
  have eq57807 : (σ x) ≠ (σ (M.op x x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq57787
       have i₂ := eq35 (σ x)
       grind)
    | exact superpose eq35 eq57787
    | exact resolve eq57787 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57787
  have eq57809 : (σ x) ≠ (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq57807
       have i₂ := eq35 x
       grind)
    | exact superpose eq35 eq57807
    | exact resolve eq57807 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57807
  have eq57810 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq57809
  have eq57841 : x = (M.op x y) ∨ x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq39 x y
       have i₂ := eq57810
       grind)
    | exact superpose eq57810 eq39
    | exact resolve eq39 eq57810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq57881 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq58439 : x = y ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq57841
       have i₂ := eq57810
       grind)
    | exact superpose eq57810 eq57841
    | exact resolve eq57841 eq57810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57810 eq57841
  have eq58485 : x = y ∨ x = (M.op x y) := by grind
  clear eq58439
  have eq58492 : x = (M.op x y) := by
    first
    | (have r₁ := eq58485
       have r₂ := eq57881
       grind)
    | exact resolve eq58485 eq57881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57881 eq58485
  have eq102286 : (σ (M.op x y)) ≠ (σ x) ∨ (k (σ x) (σ y)) = (k (k (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1286 (σ x) y
       grind)
    | exact superpose eq1286 eq16
    | (have j1 := eq1286 (σ x) y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1286 (M.op (σ x) (σ y)) (M.op x y)
       grind)
    | exact resolve eq16 eq1286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1286
  have eq102389 : (σ x) ≠ (σ x) ∨ (k (σ x) (σ y)) = (k (k (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq102286
       have i₂ := eq58492
       grind)
    | exact superpose eq58492 eq102286
    | exact resolve eq102286 eq58492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102286
  have eq102390 : (k (σ x) (σ y)) = (k (k (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by grind
  clear eq102389
  have eq102416 : (σ (k x y)) = (k (σ (k x y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq102390
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq102390
    | exact resolve eq102390 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102390
  have eq102430 : (σ y) = (k (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq102416
       have i₂ := eq53631
       grind)
    | exact superpose eq53631 eq102416
    | exact resolve eq102416 eq53631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53631 eq102416
  have eq102510 : (τ (σ y)) ≠ (τ (σ y)) ∨ (τ (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (τ (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq722 (σ y) (M.op (σ x) (σ y))
       have i₂ := eq102430
       grind)
    | exact superpose eq102430 eq722
    | (have j0 := eq722 (σ y) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq722 eq102430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722 eq102430
  have eq102649 : (τ (σ y)) ≠ (τ (σ y)) ∨ (τ (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by grind
  clear eq102510
  have eq102650 : (τ (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by grind
  clear eq102649
  have eq102721 : (σ x) = (σ y) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq102650
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq102650
    | exact resolve eq102650 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102650
  have eq103386 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq102721
       grind)
    | exact superpose eq102721 eq16
    | exact resolve eq16 eq102721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102721
  have eq103597 : (σ (M.op x y)) ≠ (σ x) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq103386
       have i₂ := eq35 (σ x)
       grind)
    | exact superpose eq35 eq103386
    | exact resolve eq103386 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq103386
  have eq103599 : (σ x) ≠ (σ x) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq103597
       have i₂ := eq58492
       grind)
    | exact superpose eq58492 eq103597
    | exact resolve eq103597 eq58492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103597
  have eq103600 : y = (τ (M.op (σ x) (σ y))) := by grind
  clear eq103599
  have eq103679 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 (M.op (σ x) (σ y))
       have i₂ := eq103600
       grind)
    | exact superpose eq103600 eq11
    | exact resolve eq11 eq103600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103600
  have eq104409 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq103679
       grind)
    | exact superpose eq103679 eq16
    | exact resolve eq16 eq103679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104412 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq53923
       have i₂ := eq103679
       grind)
    | exact superpose eq103679 eq53923
    | exact resolve eq53923 eq103679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53923
  have eq104623 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq104409
       have i₂ := eq58492
       grind)
    | exact superpose eq58492 eq104409
    | exact resolve eq104409 eq58492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58492 eq104409
  have eq105247 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq103679
       have i₂ := eq104412
       grind)
    | exact superpose eq104412 eq103679
    | exact resolve eq103679 eq104412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103679 eq104412
  have eq105356 : False := by grind
  exact eq105356

/-- `Equation418`: `x = x ◇ (x ◇ (y ◇ (x ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pyx_y_pxy_Equation418 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law418 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law418.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) ≠ X0 := by
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
  have eq22 : ∀ X0 : G, (M.op X0 X0) = X0 := by
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
  have eq25 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) X1
       have i₂ := eq22 (M.op X0 X1)
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  have eq35 : ∀ X0 : G, (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq34 X0
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq34
    | exact resolve eq34 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq67 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq76 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq87 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (M.op (τ X1) (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq88 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq93 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq88 X0 X1
       have i₂ := eq22 (σ X1)
       grind)
    | exact superpose eq22 eq88
    | (have j0 := eq88 X0 X1
       grind)
    | exact resolve eq88 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq94 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq87 X0 X1
       have i₂ := eq22 (τ X1)
       grind)
    | exact superpose eq22 eq87
    | (have j0 := eq87 X0 X1
       grind)
    | exact resolve eq87 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq96 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq67 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq67
    | exact resolve eq67 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq76 X0 X1
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq76
    | (have j1 := eq14 (σ X0) X1
       grind)
    | exact resolve eq76 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq126 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) X1) ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq118 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq118
    | (have j0 := eq118 X0 X1
       grind)
    | exact resolve eq118 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq129 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq93 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq93
    | exact resolve eq93 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq143 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq129 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq129
    | (have j0 := eq129 X0 X1
       grind)
    | exact resolve eq129 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq502 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq143 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq143
    | exact resolve eq143 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq627 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq94 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq94
    | exact resolve eq94 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq662 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq627 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq627
    | (have j0 := eq627 X0 X1
       grind)
    | exact resolve eq627 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq627
  have eq4181 : (σ (M.op x y)) ≠ (σ x) ∨ (k x (τ (σ y))) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq126 x (σ y)
       grind)
    | exact superpose eq126 eq16
    | (have j1 := eq126 x (σ y)
       grind)
    | (have r₁ := eq16
       have r₂ := eq126 (M.op x y) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq16 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4183 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (k (σ X0) X1) = X1 ∨ (σ X0) = (M.op X1 X1) ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq126 X0 X1
       grind)
    | exact superpose eq126 eq13
    | (have j0 := eq13 (σ X0) X1
       have j1 := eq126 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) X1
       have r₂ := eq126 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) X1
       have r₂ := eq126 X0 (M.op (σ X0) X1)
       grind)
    | exact resolve eq13 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq4202 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (σ X0) = (M.op X1 X1) ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq4183 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4183
  have eq4209 : ∀ X0 X1 : G, (σ X0) = X1 ∨ (k (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4202 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq4202
    | (have j0 := eq4202 X0 X1
       grind)
    | exact resolve eq4202 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4202
  have eq4210 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq4209 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4209
  have eq4211 : (σ (M.op x y)) ≠ (σ x) ∨ (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4181
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq4181
    | exact resolve eq4181 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4181
  have eq4668 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ X0 = X1 ∨ (k (τ X0) (τ X1)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4210 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4210
    | exact resolve eq4210 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4715 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (σ X0) = (σ X1) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq67 (σ X1) X0
       have i₂ := eq4210 X1 (σ X0)
       grind)
    | exact superpose eq4210 eq67
    | (have j1 := eq4210 X0 (σ X1)
       grind)
    | exact resolve eq67 eq4210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq4210
  have eq4777 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (σ X0) = (σ X1) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4715 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq4715
    | (have j0 := eq4715 X0 X1
       grind)
    | exact resolve eq4715 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4715
  have eq4786 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4668 X0 X1
       have i₂ := eq96 X1 X0
       grind)
    | exact superpose eq96 eq4668
    | (have j0 := eq4668 X0 X1
       grind)
    | exact resolve eq4668 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq4668
  have eq4809 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (σ X0) = (σ X1) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4777 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4777
    | (have j0 := eq4777 X0 X1
       grind)
    | exact resolve eq4777 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4777
  have eq4816 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ (k X1 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4809 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4809
    | (have j0 := eq4809 X0 X1
       grind)
    | exact resolve eq4809 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4809
  have eq4889 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq4786 X0 X1
       grind)
    | exact superpose eq4786 eq11
    | (have j1 := eq4786 X0 X1
       grind)
    | exact resolve eq11 eq4786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4786
  have eq4997 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4889 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq4889
    | (have j0 := eq4889 X0 X1
       grind)
    | exact resolve eq4889 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4889
  have eq5069 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq4997 (τ X0) X1
       grind)
    | exact superpose eq4997 eq18
    | (have j1 := eq4997 (τ X0) X1
       grind)
    | exact resolve eq18 eq4997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq4997
  have eq5964 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X1 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq4816 X1 X0
       grind)
    | exact superpose eq4816 eq11
    | (have j1 := eq4816 X1 X0
       grind)
    | exact resolve eq11 eq4816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4816
  have eq6887 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5964 x y
       grind)
    | exact superpose eq5964 eq16
    | (have j1 := eq5964 x y
       grind)
    | exact resolve eq16 eq5964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5964
  have eq7002 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6887
       have i₂ := eq502 y x
       grind)
    | exact superpose eq502 eq6887
    | (have j1 := eq502 y (M.op x y)
       grind)
    | (have r₁ := eq6887
       have r₂ := eq502 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq6887
       have r₂ := eq502 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq6887 eq502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502 eq6887
  have eq7007 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq7002
  have eq7035 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7007
       grind)
    | exact superpose eq7007 eq16
    | exact resolve eq16 eq7007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7007
  have eq7036 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7035
       have i₂ := eq22 (σ x)
       grind)
    | exact superpose eq22 eq7035
    | exact resolve eq7035 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7035
  have eq7037 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7036
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq7036
    | exact resolve eq7036 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7036
  have eq7038 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq7037
  have eq7277 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq25 x y
       have i₂ := eq7038
       grind)
    | exact superpose eq7038 eq25
    | exact resolve eq25 eq7038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7287 : x ≠ y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  have eq7451 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7277
       have i₂ := eq7038
       grind)
    | exact superpose eq7038 eq7277
    | exact resolve eq7277 eq7038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7038 eq7277
  have eq7470 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq7451
  have eq7473 : x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq7470
       have r₂ := eq7287
       grind)
    | exact resolve eq7470 eq7287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7287 eq7470
  have eq8479 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5069 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5069
    | exact resolve eq5069 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5069
  have eq8603 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8479 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq8479
    | (have j0 := eq8479 X0 X1
       grind)
    | exact resolve eq8479 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8479
  have eq38231 : (σ x) ≠ (σ x) ∨ (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4211
       have i₂ := eq7473
       grind)
    | exact superpose eq7473 eq4211
    | exact resolve eq4211 eq7473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4211 eq7473
  have eq38237 : (σ x) ≠ (σ x) ∨ (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by grind
  clear eq38231
  have eq38238 : (σ x) = (σ y) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq38237
  have eq38246 : y = (τ (σ x)) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq38238
       grind)
    | exact superpose eq38238 eq10
    | exact resolve eq10 eq38238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38238
  have eq38353 : x = y ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq38246
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq38246
    | exact resolve eq38246 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38246
  have eq38647 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq38353
       grind)
    | exact superpose eq38353 eq16
    | exact resolve eq16 eq38353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38353
  have eq38648 : (σ x) ≠ (σ (M.op x x)) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq38647
       have i₂ := eq22 (σ x)
       grind)
    | exact superpose eq22 eq38647
    | exact resolve eq38647 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38647
  have eq38649 : (σ x) ≠ (σ x) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq38648
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq38648
    | exact resolve eq38648 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38648
  have eq38650 : (k x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq38649
  have eq38678 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq11 (M.op (σ x) (σ y))
       have i₂ := eq38650
       grind)
    | exact superpose eq38650 eq11
    | exact resolve eq11 eq38650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38650
  have eq39096 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq38678
       grind)
    | exact superpose eq38678 eq16
    | exact resolve eq16 eq38678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39126 : (σ x) = (M.op (σ x) (M.op (σ x) (σ (k x y)))) := by
    first
    | (have i₁ := eq25 (σ x) (σ y)
       have i₂ := eq38678
       grind)
    | exact superpose eq38678 eq25
    | exact resolve eq25 eq38678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq39239 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq39096
       have i₂ := eq8603 x y
       grind)
    | exact superpose eq8603 eq39096
    | (have j1 := eq8603 x y
       grind)
    | (have r₁ := eq39096
       have r₂ := eq8603 x y
       grind)
    | (have r₁ := eq39096
       have r₂ := eq8603 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq39096
       have r₂ := eq8603 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq39096 eq8603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8603
  have eq39240 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39096
       have i₂ := eq662 y x
       grind)
    | exact superpose eq662 eq39096
    | (have j1 := eq662 x y
       grind)
    | (have r₁ := eq39096
       have r₂ := eq662 y x
       grind)
    | (have r₁ := eq39096
       have r₂ := eq662 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq39096
       have r₂ := eq662 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq39096 eq662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662
  have eq39241 : x = y ∨ x = (M.op x y) := by grind
  clear eq39240
  have eq39242 : x = y ∨ y = (k x y) := by grind
  clear eq39239
  have eq39523 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39096
       have i₂ := eq39241
       grind)
    | exact superpose eq39241 eq39096
    | exact resolve eq39096 eq39241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39241
  have eq39524 : (σ x) ≠ (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39523
       have i₂ := eq35 x
       grind)
    | exact superpose eq35 eq39523
    | exact resolve eq39523 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39523
  have eq39528 : (σ x) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39524
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq39524
    | exact resolve eq39524 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39524
  have eq39529 : x = (M.op x y) := by grind
  clear eq39528
  have eq39912 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq39096
       have i₂ := eq39242
       grind)
    | exact superpose eq39242 eq39096
    | exact resolve eq39096 eq39242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39242
  have eq39916 : (σ x) ≠ (σ (M.op x x)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq39912
       have i₂ := eq35 x
       grind)
    | exact superpose eq35 eq39912
    | exact resolve eq39912 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq39912
  have eq39920 : (σ x) ≠ (σ x) ∨ y = (k x y) := by
    first
    | (have i₁ := eq39916
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq39916
    | exact resolve eq39916 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq39916
  have eq39921 : y = (k x y) := by grind
  clear eq39920
  have eq40379 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq39096
       have i₂ := eq39921
       grind)
    | exact superpose eq39921 eq39096
    | exact resolve eq39096 eq39921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39096
  have eq40419 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq40379
       have i₂ := eq39529
       grind)
    | exact superpose eq39529 eq40379
    | exact resolve eq40379 eq39529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39529 eq40379
  have eq41211 : (σ x) = (M.op (σ x) (σ (k x (k x y)))) ∨ (σ x) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ (k x y))) := by
    first
    | (have i₁ := eq39126
       have i₂ := eq93 x (k x y)
       grind)
    | exact superpose eq93 eq39126
    | (have j1 := eq93 x (k x y)
       grind)
    | exact resolve eq39126 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq39126
  have eq41275 : (σ x) = (M.op (σ x) (σ (k x y))) ∨ (σ x) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ (k x y))) := by
    first
    | (have i₁ := eq41211
       have i₂ := eq39921
       grind)
    | exact superpose eq39921 eq41211
    | exact resolve eq41211 eq39921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41211
  have eq41276 : (σ x) = (M.op (σ x) (σ (k x y))) ∨ (σ x) = (σ (k x y)) := by grind
  clear eq41275
  have eq41292 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq41276
       have i₂ := eq39921
       grind)
    | exact superpose eq39921 eq41276
    | exact resolve eq41276 eq39921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41276
  have eq41304 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq41292
       have i₂ := eq38678
       grind)
    | exact superpose eq38678 eq41292
    | exact resolve eq41292 eq38678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38678 eq41292
  have eq41305 : (σ x) = (σ (k x y)) := by grind
  clear eq41304
  have eq41312 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq41305
       have i₂ := eq39921
       grind)
    | exact superpose eq39921 eq41305
    | exact resolve eq41305 eq39921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39921 eq41305
  have eq41318 : False := by grind
  exact eq41318

/-- `Equation418`: `x = x ◇ (x ◇ (y ◇ (x ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then m(X,Y) else m(Y,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_pxy_pyy_Equation418 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) Law418 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law418.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyy_x_pyx_y_pxy_Equation418 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law418 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law418.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq64 : ∀ X0 : G, (M.op X0 X0) = X0 := by
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
  have eq92 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq64 X0
       grind)
    | exact resolve eq12 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq93 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq92 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq96 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq93 (σ X0) (σ X1)
       grind)
    | exact superpose eq93 eq15
    | exact resolve eq15 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq96 X0 X1
       have i₂ := eq93 X0 X1
       grind)
    | exact superpose eq93 eq96
    | exact resolve eq96 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq96
  have eq249 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq107 x y
       grind)
    | exact superpose eq107 eq16
    | (have r₁ := eq16
       have r₂ := eq107 x y
       grind)
    | exact resolve eq16 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq257 : False := by grind
  exact eq257

/-- `Equation418`: `x = x ◇ (x ◇ (y ◇ (x ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then X else if m(X,X) = m(X,Y) then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_x_y_pxy_Equation418 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law418 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law418.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
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
  have eq26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq34 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq40 : ∀ X0 : G, (M.op X0 X0) = X0 := by
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
  have eq43 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) X1
       have i₂ := eq40 (M.op X0 X1)
       grind)
    | exact superpose eq40 eq9
    | exact resolve eq9 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq13
    | (have j0 := eq13 X0 X1
       grind)
    | exact resolve eq13 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq26
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq89 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq92 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq89 X0 X1
       have i₂ := eq40 (σ X0)
       grind)
    | exact superpose eq40 eq89
    | (have j0 := eq89 X0 X1
       grind)
    | exact resolve eq89 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq93 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq88 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq88
    | (have j0 := eq88 X0 X1
       grind)
    | exact resolve eq88 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq101 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 X1
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq34
    | (have j1 := eq14 (σ X0) X1
       grind)
    | exact resolve eq34 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq109 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) X1) ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq101 X0 X1
       have i₂ := eq40 (σ X0)
       grind)
    | exact superpose eq40 eq101
    | (have j0 := eq101 X0 X1
       grind)
    | exact resolve eq101 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq128 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 ∨ (σ X1) = X0 := by
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
  have eq143 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq128 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq128
    | (have j0 := eq128 X0 X1
       grind)
    | exact resolve eq128 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq475 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq143 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq143
    | exact resolve eq143 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq605 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq93 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq93
    | exact resolve eq93 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq640 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq605 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq605
    | (have j0 := eq605 X0 X1
       grind)
    | exact resolve eq605 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605
  have eq4069 : (σ (M.op x y)) ≠ (σ x) ∨ (k x (τ (σ y))) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq109 x (σ y)
       grind)
    | exact superpose eq109 eq16
    | (have j1 := eq109 x (σ y)
       grind)
    | (have r₁ := eq16
       have r₂ := eq109 (M.op x y) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq16 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4076 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (k (σ X0) X1) = X1 ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq52 (σ X0) X1
       have i₂ := eq109 X0 X1
       grind)
    | exact superpose eq109 eq52
    | (have j0 := eq52 (σ X0) X1
       have j1 := eq109 X0 X1
       grind)
    | (have r₁ := eq52 (σ X0) X1
       have r₂ := eq109 X0 X1
       grind)
    | (have r₁ := eq52 (σ X0) X1
       have r₂ := eq109 X0 (M.op (σ X0) X1)
       grind)
    | exact resolve eq52 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq109
  have eq4091 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (k (σ X0) X1) = X1 ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq4076 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4076
  have eq4092 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq4091 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4091
  have eq4100 : (σ (M.op x y)) ≠ (σ x) ∨ (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4069
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq4069
    | exact resolve eq4069 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4069
  have eq4550 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ X0 = X1 ∨ (k (τ X0) (τ X1)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4092 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4092
    | exact resolve eq4092 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4597 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (σ X0) = (σ X1) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq26 (σ X1) X0
       have i₂ := eq4092 X1 (σ X0)
       grind)
    | exact superpose eq4092 eq26
    | (have j1 := eq4092 X0 (σ X1)
       grind)
    | exact resolve eq26 eq4092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq4092
  have eq4661 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (σ X0) = (σ X1) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4597 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq4597
    | (have j0 := eq4597 X0 X1
       grind)
    | exact resolve eq4597 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4597
  have eq4672 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4550 X0 X1
       have i₂ := eq76 X1 X0
       grind)
    | exact superpose eq76 eq4550
    | (have j0 := eq4550 X0 X1
       grind)
    | exact resolve eq4550 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq4550
  have eq4695 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (σ X0) = (σ X1) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4661 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4661
    | (have j0 := eq4661 X0 X1
       grind)
    | exact resolve eq4661 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4661
  have eq4702 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ (k X1 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4695 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4695
    | (have j0 := eq4695 X0 X1
       grind)
    | exact resolve eq4695 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4695
  have eq4775 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq4672 X0 X1
       grind)
    | exact superpose eq4672 eq11
    | (have j1 := eq4672 X0 X1
       grind)
    | exact resolve eq11 eq4672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4672
  have eq4883 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4775 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq4775
    | (have j0 := eq4775 X0 X1
       grind)
    | exact resolve eq4775 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4775
  have eq4953 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq4883 (τ X0) X1
       grind)
    | exact superpose eq4883 eq18
    | (have j1 := eq4883 (τ X0) X1
       grind)
    | exact resolve eq18 eq4883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq4883
  have eq5503 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X1 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq4702 X1 X0
       grind)
    | exact superpose eq4702 eq11
    | (have j1 := eq4702 X1 X0
       grind)
    | exact resolve eq11 eq4702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4702
  have eq6525 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5503 x y
       grind)
    | exact superpose eq5503 eq16
    | (have j1 := eq5503 x y
       grind)
    | exact resolve eq16 eq5503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5503
  have eq6589 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq6525
       have i₂ := eq475 y x
       grind)
    | exact superpose eq475 eq6525
    | (have j1 := eq475 y x
       grind)
    | (have r₁ := eq6525
       have r₂ := eq475 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq6525
       have r₂ := eq475 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq6525 eq475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475 eq6525
  have eq6594 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq6589
  have eq6700 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6594
       grind)
    | exact superpose eq6594 eq16
    | exact resolve eq16 eq6594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6594
  have eq6701 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq6700
       have i₂ := eq40 (σ x)
       grind)
    | exact superpose eq40 eq6700
    | exact resolve eq6700 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6700
  have eq6702 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq6701
       have i₂ := eq40 x
       grind)
    | exact superpose eq40 eq6701
    | exact resolve eq6701 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6701
  have eq6703 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq6702
  have eq6707 : x = (M.op x y) ∨ x = (M.op x (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq43 x y
       have i₂ := eq6703
       grind)
    | exact superpose eq6703 eq43
    | exact resolve eq43 eq6703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6717 : x ≠ y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  have eq6729 : x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq6707
       have i₂ := eq6703
       grind)
    | exact superpose eq6703 eq6707
    | exact resolve eq6707 eq6703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6703 eq6707
  have eq6747 : x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq6729
  have eq6750 : x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq6747
       have r₂ := eq6717
       grind)
    | exact resolve eq6747 eq6717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6717 eq6747
  have eq7840 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4953 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4953
    | exact resolve eq4953 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4953
  have eq7957 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7840 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq7840
    | (have j0 := eq7840 X0 X1
       grind)
    | exact resolve eq7840 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7840
  have eq36949 : (σ x) ≠ (σ x) ∨ (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4100
       have i₂ := eq6750
       grind)
    | exact superpose eq6750 eq4100
    | exact resolve eq4100 eq6750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4100 eq6750
  have eq36955 : (σ x) ≠ (σ x) ∨ (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by grind
  clear eq36949
  have eq36956 : (σ x) = (σ y) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq36955
  have eq37229 : y = (τ (σ x)) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq36956
       grind)
    | exact superpose eq36956 eq10
    | exact resolve eq10 eq36956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36956
  have eq37331 : x = y ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq37229
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq37229
    | exact resolve eq37229 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37229
  have eq37333 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq37331
       grind)
    | exact superpose eq37331 eq16
    | exact resolve eq16 eq37331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37331
  have eq37334 : (σ x) ≠ (σ (M.op x x)) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq37333
       have i₂ := eq40 (σ x)
       grind)
    | exact superpose eq40 eq37333
    | exact resolve eq37333 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37333
  have eq37335 : (σ x) ≠ (σ x) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq37334
       have i₂ := eq40 x
       grind)
    | exact superpose eq40 eq37334
    | exact resolve eq37334 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37334
  have eq37336 : (k x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq37335
  have eq37637 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq11 (M.op (σ x) (σ y))
       have i₂ := eq37336
       grind)
    | exact superpose eq37336 eq11
    | exact resolve eq11 eq37336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37336
  have eq37775 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq37637
       grind)
    | exact superpose eq37637 eq16
    | exact resolve eq16 eq37637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37802 : (σ x) = (M.op (σ x) (M.op (σ x) (σ (k x y)))) := by
    first
    | (have i₁ := eq43 (σ x) (σ y)
       have i₂ := eq37637
       grind)
    | exact superpose eq37637 eq43
    | exact resolve eq43 eq37637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq38184 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq37775
       have i₂ := eq7957 x y
       grind)
    | exact superpose eq7957 eq37775
    | (have j1 := eq7957 x y
       grind)
    | (have r₁ := eq37775
       have r₂ := eq7957 x y
       grind)
    | (have r₁ := eq37775
       have r₂ := eq7957 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq37775
       have r₂ := eq7957 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq37775 eq7957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7957
  have eq38185 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq37775
       have i₂ := eq640 y x
       grind)
    | exact superpose eq640 eq37775
    | (have j1 := eq640 y x
       grind)
    | (have r₁ := eq37775
       have r₂ := eq640 y x
       grind)
    | (have r₁ := eq37775
       have r₂ := eq640 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq37775
       have r₂ := eq640 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq37775 eq640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640
  have eq38186 : x = y ∨ x = (M.op x y) := by grind
  clear eq38185
  have eq38187 : x = y ∨ y = (k x y) := by grind
  clear eq38184
  have eq38196 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq37775
       have i₂ := eq38186
       grind)
    | exact superpose eq38186 eq37775
    | exact resolve eq37775 eq38186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38186
  have eq38197 : (σ x) ≠ (σ (M.op x x)) ∨ x = (M.op x y) := by grind
  clear eq38196
  have eq38201 : (σ x) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq38197
       have i₂ := eq40 x
       grind)
    | exact superpose eq40 eq38197
    | exact resolve eq38197 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38197
  have eq38202 : x = (M.op x y) := by grind
  clear eq38201
  have eq38851 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq37775
       have i₂ := eq38187
       grind)
    | exact superpose eq38187 eq37775
    | exact resolve eq37775 eq38187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38187
  have eq38855 : (σ x) ≠ (σ (M.op x x)) ∨ y = (k x y) := by grind
  clear eq38851
  have eq38859 : (σ x) ≠ (σ x) ∨ y = (k x y) := by
    first
    | (have i₁ := eq38855
       have i₂ := eq40 x
       grind)
    | exact superpose eq40 eq38855
    | exact resolve eq38855 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq38855
  have eq38860 : y = (k x y) := by grind
  clear eq38859
  have eq38881 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq37775
       have i₂ := eq38860
       grind)
    | exact superpose eq38860 eq37775
    | exact resolve eq37775 eq38860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37775
  have eq38923 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq38881
       have i₂ := eq38202
       grind)
    | exact superpose eq38202 eq38881
    | exact resolve eq38881 eq38202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38202 eq38881
  have eq40138 : (σ x) = (M.op (σ x) (σ (k x (k x y)))) ∨ (σ x) = (M.op (σ x) (σ (k x y))) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq37802
       have i₂ := eq92 x (k x y)
       grind)
    | exact superpose eq92 eq37802
    | (have j1 := eq92 x (k x y)
       grind)
    | exact resolve eq37802 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq37802
  have eq40197 : (σ x) = (M.op (σ x) (σ (k x y))) ∨ (σ x) = (M.op (σ x) (σ (k x y))) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq40138
       have i₂ := eq38860
       grind)
    | exact superpose eq38860 eq40138
    | exact resolve eq40138 eq38860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40138
  have eq40198 : (σ x) = (M.op (σ x) (σ (k x y))) ∨ (σ x) = (σ (k x y)) := by grind
  clear eq40197
  have eq40214 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq40198
       have i₂ := eq38860
       grind)
    | exact superpose eq38860 eq40198
    | exact resolve eq40198 eq38860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40198
  have eq40226 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq40214
       have i₂ := eq37637
       grind)
    | exact superpose eq37637 eq40214
    | exact resolve eq40214 eq37637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37637 eq40214
  have eq40227 : (σ x) = (σ (k x y)) := by grind
  clear eq40226
  have eq40234 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq40227
       have i₂ := eq38860
       grind)
    | exact superpose eq38860 eq40227
    | exact resolve eq40227 eq38860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38860 eq40227
  have eq40240 : False := by grind
  exact eq40240

/-- `Equation418`: `x = x ◇ (x ◇ (y ◇ (x ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then X else if m(X,Y) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_x_pxy_pyx_Equation418 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law418 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law418.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq76 : ∀ X0 : G, (M.op X0 X0) = X0 := by
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
  have eq79 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) X1
       have i₂ := eq76 (M.op X0 X1)
       grind)
    | exact superpose eq76 eq9
    | exact resolve eq9 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq345 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X1 ∨ X0 = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq79 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq79 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq79
    | (have j1 := eq14 (M.op X1 (M.op X1 (M.op X0 X0))) X1
       grind)
    | exact resolve eq79 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq354 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq76 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq76 X1
       have i₂ := eq14 X1 X1
       grind)
    | exact superpose eq14 eq76
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq76 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq359 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = X1 ∨ X0 = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq345 X0 X1
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq345
    | (have j0 := eq345 X0 X1
       grind)
    | exact resolve eq345 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345
  have eq500 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq359 X0 X1
       have i₂ := eq354 X1 X0
       grind)
    | exact superpose eq354 eq359
    | (have j0 := eq359 X0 X1
       have j1 := eq354 (M.op X1 X0) X1
       grind)
    | exact resolve eq359 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359
  have eq518 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq500 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500
  have eq531 : ∀ X0 X1 : G, X0 = X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq354 X0 X1
       have i₂ := eq518 X1 X0
       grind)
    | exact superpose eq518 eq354
    | (have j0 := eq354 X0 X1
       have j1 := eq518 X0 X1
       grind)
    | exact resolve eq354 eq518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354 eq518
  have eq543 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq531 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531
  have eq562 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq543 X1 (τ X0)
       grind)
    | exact superpose eq543 eq19
    | (have j1 := eq543 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq567 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq543 (σ X1) (σ X0)
       grind)
    | exact superpose eq543 eq15
    | (have j1 := eq543 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543
  have eq681 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq562 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq562
    | exact resolve eq562 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq728 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq681 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq681
    | (have j0 := eq681 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq681 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681
  have eq905 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq567 x y
       grind)
    | exact superpose eq567 eq16
    | (have j1 := eq567 x y
       grind)
    | exact resolve eq16 eq567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567
  have eq944 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq905
       have i₂ := eq728 x y
       grind)
    | exact superpose eq728 eq905
    | (have j1 := eq728 (σ x) (σ y)
       grind)
    | (have r₁ := eq905
       have r₂ := eq728 x y
       grind)
    | (have r₁ := eq905
       have r₂ := eq728 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq905
       have r₂ := eq728 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq905 eq728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728 eq905
  have eq945 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq944
  have eq950 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq945
       grind)
    | exact superpose eq945 eq16
    | exact resolve eq16 eq945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq945
  have eq951 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq950
       have i₂ := eq76 (σ x)
       grind)
    | exact superpose eq76 eq950
    | exact resolve eq950 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq950
  have eq952 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq951
       have i₂ := eq76 x
       grind)
    | exact superpose eq76 eq951
    | exact resolve eq951 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq951
  have eq953 : (σ x) = (σ y) := by grind
  clear eq952
  have eq954 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq953
       grind)
    | exact superpose eq953 eq16
    | exact resolve eq16 eq953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq955 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq953
       grind)
    | exact superpose eq953 eq10
    | exact resolve eq10 eq953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq953
  have eq992 : x = y := by
    first
    | (have i₁ := eq955
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq955
    | exact resolve eq955 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq955
  have eq993 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq954
       have i₂ := eq76 (σ x)
       grind)
    | exact superpose eq76 eq954
    | exact resolve eq954 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq954
  have eq994 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq993
       have i₂ := eq992
       grind)
    | exact superpose eq992 eq993
    | exact resolve eq993 eq992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq992 eq993
  have eq995 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq994
       have i₂ := eq76 x
       grind)
    | exact superpose eq76 eq994
    | exact resolve eq994 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq994
  have eq996 : False := by grind
  exact eq996

/-- `Equation418`: `x = x ◇ (x ◇ (y ◇ (x ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_y_pxy_Equation418 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law418 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law418.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = b :=
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
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
  have eq31 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq33 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 X1))) = X0 := by
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
  clear eq26
  have eq81 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq31
    | (have j0 := eq31 X0 X1
       have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq31 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq670 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq81 x y
       grind)
    | exact superpose eq81 eq16
    | (have j1 := eq81 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq81 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq81 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq81 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq688 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq670
  have eq803 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq688
       grind)
    | exact superpose eq688 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq688
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq688
       grind)
    | exact resolve eq13 eq688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688
  have eq811 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq803
  have eq812 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq811
  have eq815 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq812
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq812
    | exact resolve eq812 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq812
  have eq4168 : (k x y) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq815
       grind)
    | exact superpose eq815 eq10
    | exact resolve eq10 eq815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq815
  have eq4201 : y = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq4168
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq4168
    | exact resolve eq4168 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4168
  have eq4203 : y = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq4201
       have r₂ := eq13 x y
       grind)
    | exact resolve eq4201 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4201
  have eq6512 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq4203
       grind)
    | exact superpose eq4203 eq14
    | (have j0 := eq14 x y
       grind)
    | exact resolve eq14 eq4203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6513 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq31 x y
       have i₂ := eq4203
       grind)
    | exact superpose eq4203 eq31
    | (have j0 := eq31 x y
       grind)
    | exact resolve eq31 eq4203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq4203
  have eq6521 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq6513
  have eq6522 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq6512
  have eq8904 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq33 x y
       have i₂ := eq6522
       grind)
    | exact superpose eq6522 eq33
    | exact resolve eq33 eq6522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16553 : x = (M.op x y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq8904
       have i₂ := eq6522
       grind)
    | exact superpose eq6522 eq8904
    | exact resolve eq8904 eq6522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6522 eq8904
  have eq16583 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq16553
  have eq115072 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq33 (σ x) (σ y)
       have i₂ := eq6521
       grind)
    | exact superpose eq6521 eq33
    | exact resolve eq33 eq6521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq569196 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq115072
       have i₂ := eq6521
       grind)
    | exact superpose eq6521 eq115072
    | exact resolve eq115072 eq6521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6521 eq115072
  have eq569317 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq569196
  have eq594147 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq569317
       grind)
    | exact superpose eq569317 eq16
    | exact resolve eq16 eq569317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569317
  have eq622677 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq594147
       have i₂ := eq16583
       grind)
    | exact superpose eq16583 eq594147
    | exact resolve eq594147 eq16583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16583 eq594147
  have eq622682 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq622677
  have eq622683 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq622682
  have eq652506 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq622683
       grind)
    | exact superpose eq622683 eq10
    | exact resolve eq10 eq622683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622683
  have eq653299 : x = y ∨ x = y := by
    first
    | (have i₁ := eq652506
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq652506
    | exact resolve eq652506 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652506
  have eq653300 : x = y := by grind
  clear eq653299
  have eq683571 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq653300
       grind)
    | exact superpose eq653300 eq16
    | exact resolve eq16 eq653300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653300
  have eq683572 : False := by grind
  exact eq683572

/-- `Equation418`: `x = x ◇ (x ◇ (y ◇ (x ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxx_x_pyx_Equation418 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law418 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law418.models_iff G M).mp hM
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
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
  clear eq18
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
  have eq120 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) X1
       have i₂ := eq110 (M.op X0 X1)
       grind)
    | exact superpose eq110 eq9
    | exact resolve eq9 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq164 : ∀ X0 X1 : G, (M.op (τ X0) X1) = X1 ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq779 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (τ X1) = X0 ∨ (k X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op (τ X1) X0)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (τ X1)
       have i₂ := eq164 X1 X0
       grind)
    | exact superpose eq164 eq13
    | (have j0 := eq13 (τ X1) X0
       have j1 := eq164 X1 X0
       grind)
    | (have r₁ := eq13 X1 (τ X0)
       have r₂ := eq164 X0 X1
       grind)
    | (have r₁ := eq13 (τ X0) X1
       have r₂ := eq164 X0 (M.op X1 (τ X0))
       grind)
    | exact resolve eq13 eq164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164
  have eq795 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (τ X1) = X0 ∨ (k X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq779 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779
  have eq796 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op (τ X1) X0)) ∨ (k X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq795 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq795
  have eq2350 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq796 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq796
    | exact resolve eq796 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq796
  have eq2398 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2350 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2350
    | (have j0 := eq2350 X0 X1
       grind)
    | exact resolve eq2350 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2350
  have eq2435 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X1))) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq2398 X0 X1
       grind)
    | exact superpose eq2398 eq10
    | (have j1 := eq2398 X0 X1
       grind)
    | exact resolve eq10 eq2398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2398
  have eq2475 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2435 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq2435
    | (have j0 := eq2435 X0 X1
       grind)
    | exact resolve eq2435 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2435
  have eq2491 : ∀ X0 X1 : G, (k X1 (σ X0)) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 X0
       have i₂ := eq2475 (σ X0) X1
       grind)
    | exact superpose eq2475 eq28
    | (have j1 := eq2475 (σ X0) X1
       grind)
    | exact resolve eq28 eq2475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2475
  have eq4836 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 (σ X1)
       have i₂ := eq2491 X1 (σ X0)
       grind)
    | exact superpose eq2491 eq37
    | (have j1 := eq2491 X1 (σ X0)
       grind)
    | exact resolve eq37 eq2491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq2491
  have eq4901 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4836 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq4836
    | (have j0 := eq4836 X0 X1
       grind)
    | exact resolve eq4836 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4836
  have eq4937 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4901 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4901
    | (have j0 := eq4901 X0 X1
       grind)
    | exact resolve eq4901 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4901
  have eq4951 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X1) (σ X0))) ∨ (k X0 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4937 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4937
    | (have j0 := eq4937 X0 X1
       grind)
    | exact resolve eq4937 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4937
  have eq5165 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (k X0 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X1) (σ X0))
       have i₂ := eq4951 X0 X1
       grind)
    | exact superpose eq4951 eq11
    | (have j1 := eq4951 X0 X1
       grind)
    | exact resolve eq11 eq4951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4951
  have eq6085 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5165 y x
       grind)
    | exact superpose eq5165 eq16
    | (have j1 := eq5165 y x
       grind)
    | exact resolve eq16 eq5165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5165
  have eq6132 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq6085
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq6085
    | (have j1 := eq14 y x
       grind)
    | (have r₁ := eq6085
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq6085
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq6085 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6085
  have eq6138 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq6132
  have eq6139 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq6138
  have eq6160 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6139
       grind)
    | exact superpose eq6139 eq16
    | exact resolve eq16 eq6139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6139
  have eq6161 : y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq6160
       have r₂ := eq22 x
       grind)
    | exact resolve eq6160 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6160
  have eq6165 : x = (M.op x (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq120 x y
       have i₂ := eq6161
       grind)
    | exact superpose eq6161 eq120
    | exact resolve eq120 eq6161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq6174 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq6165
       have i₂ := eq6161
       grind)
    | exact superpose eq6161 eq6165
    | exact resolve eq6165 eq6161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6165
  have eq6185 : x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq6174
  have eq6193 : x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq6161
       have i₂ := eq6185
       grind)
    | exact superpose eq6185 eq6161
    | exact resolve eq6161 eq6185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6161 eq6185
  have eq6201 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq6193
  have eq6207 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6201
       grind)
    | exact superpose eq6201 eq16
    | exact resolve eq16 eq6201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6201
  have eq6208 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq6207
       have r₂ := eq22 x
       grind)
    | exact resolve eq6207 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq6207
  have eq6209 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6208
       grind)
    | exact superpose eq6208 eq16
    | exact resolve eq16 eq6208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6210 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq6208
       grind)
    | exact superpose eq6208 eq10
    | exact resolve eq10 eq6208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6208
  have eq6260 : x = y := by
    first
    | (have i₁ := eq6210
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq6210
    | exact resolve eq6210 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6210
  have eq6261 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq6209
       have i₂ := eq110 (σ x)
       grind)
    | exact superpose eq110 eq6209
    | exact resolve eq6209 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6209
  have eq6265 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq6261
       have i₂ := eq6260
       grind)
    | exact superpose eq6260 eq6261
    | exact resolve eq6261 eq6260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6260 eq6261
  have eq6268 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq6265
       have i₂ := eq110 x
       grind)
    | exact superpose eq110 eq6265
    | exact resolve eq6265 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq6265
  have eq6269 : False := by grind
  exact eq6269
