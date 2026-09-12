import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_pyy_pxy_Equation909 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law909 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0))) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
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
  have eq42 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq9 (σ X0) (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq46 X0
       have i₂ := eq22 (M.op X0 X0)
       grind)
    | exact superpose eq22 eq46
    | exact resolve eq46 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq48 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq47 X0
       have i₂ := eq42 X0 X0
       grind)
    | exact superpose eq42 eq47
    | exact resolve eq47 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq70 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
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
  have eq99 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq122 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq9 (τ X0) (τ X0)
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq9
    | exact resolve eq9 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq122 X0
       have i₂ := eq70 (M.op X0 X0)
       grind)
    | exact superpose eq70 eq122
    | exact resolve eq122 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq122
  have eq125 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq123 X0
       have i₂ := eq42 X0 X0
       grind)
    | exact superpose eq42 eq123
    | exact resolve eq123 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq126 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op (M.op X1 X0) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq42 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq42
    | exact resolve eq42 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) = (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq42 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq42 X0 X1
       grind)
    | exact superpose eq42 eq42
    | exact resolve eq42 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0
       have i₂ := eq42 X1 X0
       grind)
    | exact superpose eq42 eq9
    | exact resolve eq9 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) = (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq127 X0 X1
       have i₂ := eq42 (M.op X1 X1) X0
       grind)
    | exact superpose eq42 eq127
    | exact resolve eq127 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq136 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X0) (M.op (M.op X1 X0) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq126 X0 X1
       have i₂ := eq42 (M.op X1 X0) (M.op X1 X0)
       grind)
    | exact superpose eq42 eq126
    | exact resolve eq126 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq140 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) = (M.op X0 (M.op X1 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq135 X0 X1
       have i₂ := eq42 X1 X1
       grind)
    | exact superpose eq42 eq135
    | exact resolve eq135 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq141 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq136 X0 X1
       have i₂ := eq42 X0 X1
       grind)
    | exact superpose eq42 eq136
    | exact resolve eq136 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq142 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X1 (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq141 X0 X1
       have i₂ := eq140 X1 X0
       grind)
    | exact superpose eq140 eq141
    | exact resolve eq141 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140 eq141
  have eq143 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op X2 (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq130 X2 (M.op X0 X1)
       have i₂ := eq42 X1 X0
       grind)
    | exact superpose eq42 eq130
    | exact resolve eq130 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq144 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (M.op X1 (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq130 X1 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq130
    | exact resolve eq130 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq146 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq130 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq130 (M.op X0 X0) X0
       grind)
    | exact superpose eq130 eq130
    | exact resolve eq130 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq199 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq99 x y
       grind)
    | exact superpose eq99 eq16
    | (have j1 := eq99 x y
       grind)
    | exact resolve eq16 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq279 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq142 (M.op X0 X0) X1
       have i₂ := eq130 (M.op X0 X0) X0
       grind)
    | exact superpose eq130 eq142
    | exact resolve eq142 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq281 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (M.op X1 (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq142 (σ (M.op X0 X0)) X1
       have i₂ := eq144 X0 (σ (M.op X0 X0))
       grind)
    | exact superpose eq144 eq142
    | exact resolve eq142 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq295 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op X1 (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq281 X0 X1
       have i₂ := eq22 (M.op X0 X0)
       grind)
    | exact superpose eq22 eq281
    | exact resolve eq281 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq297 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq279 X0 X1
       have i₂ := eq42 X0 X0
       grind)
    | exact superpose eq42 eq279
    | exact resolve eq279 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279
  have eq302 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op X1 (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq295 X0 X1
       have i₂ := eq42 X0 X0
       grind)
    | exact superpose eq42 eq295
    | exact resolve eq295 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295
  have eq307 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq297 X1 X2
       have i₂ := eq297 X1 X0
       grind)
    | (have i₁ := eq297 X0 X1
       have i₂ := eq297 X0 X0
       grind)
    | exact superpose eq297 eq297
    | exact resolve eq297 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq318 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq130 X1 X1
       have i₂ := eq297 X1 X0
       grind)
    | (have i₁ := eq130 X0 X0
       have i₂ := eq297 X0 X0
       grind)
    | exact superpose eq297 eq130
    | exact resolve eq130 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq319 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X2 (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq142 X1 X2
       have i₂ := eq297 X1 X0
       grind)
    | (have i₁ := eq142 X0 X1
       have i₂ := eq297 X0 X0
       grind)
    | exact superpose eq297 eq142
    | exact resolve eq142 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq320 : ∀ X0 X1 : G, (τ X1) = (M.op (τ X1) (τ (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq125 X1
       have i₂ := eq297 X1 X0
       grind)
    | (have i₁ := eq125 X0
       have i₂ := eq297 X0 X0
       grind)
    | exact superpose eq297 eq125
    | exact resolve eq125 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq321 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq48 X1
       have i₂ := eq297 X1 X0
       grind)
    | (have i₁ := eq48 X0
       have i₂ := eq297 X0 X0
       grind)
    | exact superpose eq297 eq48
    | exact resolve eq48 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq297
  have eq754 : ∀ X0 X1 : G, (M.op X0 (τ (M.op X1 (M.op X1 (σ X0))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq320 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq320
    | exact resolve eq320 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320
  have eq924 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0)))) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq143 (M.op (M.op X0 X0) (M.op X0 X0)) X0 X1
       have i₂ := eq146 (M.op X0 X0)
       grind)
    | exact superpose eq146 eq143
    | exact resolve eq143 eq146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143 eq146
  have eq967 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 (M.op X0 X0)))) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq924 X0 X1
       have i₂ := eq42 X0 X0
       grind)
    | exact superpose eq42 eq924
    | exact resolve eq924 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq924
  have eq975 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq967 X0 x
       have i₂ := eq142 X0 x
       grind)
    | exact superpose eq142 eq967
    | exact resolve eq967 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq967
  have eq1022 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 (M.op X0 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq975 X1
       have i₂ := eq307 X1 X1 X0
       grind)
    | (have i₁ := eq975 X1
       have i₂ := eq307 X0 X1 X1
       grind)
    | exact superpose eq307 eq975
    | exact resolve eq975 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq975
  have eq1083 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X1 X0)) (M.op X1 (M.op X1 X0))) = (M.op (M.op X0 X0) (M.op X1 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1022 X0 (M.op X1 (M.op X1 X0))
       have i₂ := eq318 X1 X0
       grind)
    | exact superpose eq318 eq1022
    | exact resolve eq1022 eq318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1022
  have eq1165 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0))) = (M.op (M.op X0 X0) (M.op X1 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1083 X0 X1
       have i₂ := eq42 (M.op X1 X0) X1
       grind)
    | exact superpose eq42 eq1083
    | exact resolve eq1083 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1083
  have eq1189 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1165 X0 X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq1165
    | exact resolve eq1165 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1165
  have eq1387 : ∀ X0 X1 : G, (σ (M.op X1 (M.op X1 X0))) = (M.op (M.op (σ (M.op X1 (M.op X1 X0))) (σ (M.op X1 (M.op X1 X0)))) (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1189 (σ (M.op X1 (M.op X1 X0))) (σ X0)
       have i₂ := eq321 X1 X0
       grind)
    | exact superpose eq321 eq1189
    | exact resolve eq1189 eq321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321 eq1189
  have eq1459 : ∀ X0 X1 : G, (σ (M.op X1 (M.op X1 X0))) = (M.op (M.op (σ (M.op X1 (M.op X1 X0))) (σ (M.op X1 (M.op X1 X0)))) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1387 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq1387
    | exact resolve eq1387 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1387
  have eq1492 : ∀ X0 X1 : G, (σ (M.op X1 (M.op X1 X0))) = (M.op (σ (M.op (M.op X1 (M.op X1 X0)) (M.op X1 (M.op X1 X0)))) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1459 X0 X1
       have i₂ := eq22 (M.op X1 (M.op X1 X0))
       grind)
    | exact superpose eq22 eq1459
    | exact resolve eq1459 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1459
  have eq1514 : ∀ X0 X1 : G, (σ (M.op X1 (M.op X1 X0))) = (M.op (σ (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0)))) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1492 X0 X1
       have i₂ := eq42 (M.op X1 X0) X1
       grind)
    | exact superpose eq42 eq1492
    | exact resolve eq1492 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq1492
  have eq1527 : ∀ X0 X1 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X1 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1514 X0 X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq1514
    | exact resolve eq1514 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1514
  have eq1859 : ∀ X0 X1 X2 : G, (σ (M.op X0 (M.op X0 X1))) = (M.op X2 (M.op X2 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq302 X1 X2
       have i₂ := eq307 X1 X1 X0
       grind)
    | (have i₁ := eq302 X1 X2
       have i₂ := eq307 X0 X1 X1
       grind)
    | exact superpose eq307 eq302
    | exact resolve eq302 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302
  have eq2052 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X1 (M.op X0 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq319 X1 X2 X1
       have i₂ := eq307 X1 (M.op X1 X2) X0
       grind)
    | (have i₁ := eq319 X1 X2 X1
       have i₂ := eq307 X0 (M.op X1 X2) X1
       grind)
    | exact superpose eq307 eq319
    | exact resolve eq319 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307 eq319
  have eq2913 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X1)) = (τ (M.op X0 (M.op X0 (σ X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (M.op X2 (M.op X2 X1))
       have i₂ := eq1859 X2 X1 X0
       grind)
    | exact superpose eq1859 eq10
    | exact resolve eq10 eq1859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1859
  have eq3276 : ∀ X0 X1 X2 : G, (σ (M.op X2 X2)) = (M.op X0 (M.op X1 (M.op X1 (M.op X0 (σ X2))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 X2
       have i₂ := eq2052 X1 X0 (σ X2)
       grind)
    | exact superpose eq2052 eq22
    | exact resolve eq22 eq2052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4758 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq199
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq199
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq199
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq199
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq199 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq4759 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq4758
  have eq5596 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X1)) = (τ (τ (M.op X0 (M.op X0 (σ (σ X1)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2913 x X1 X2
       have i₂ := eq2913 X0 (σ X1) x
       grind)
    | exact superpose eq2913 eq2913
    | exact resolve eq2913 eq2913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5654 : ∀ X0 X1 : G, (M.op X1 (τ (τ (M.op X0 (M.op X0 (σ (σ X1))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq754 X1 x
       have i₂ := eq2913 X0 (σ X1) x
       grind)
    | exact superpose eq2913 eq754
    | exact resolve eq754 eq2913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq754 eq2913
  have eq45199 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (τ (M.op X0 (M.op X1 (M.op X1 (M.op X0 (σ X2)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (M.op X2 X2)
       have i₂ := eq3276 X0 X1 X2
       grind)
    | exact superpose eq3276 eq10
    | exact resolve eq10 eq3276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3276
  have eq58238 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4759
       grind)
    | exact superpose eq4759 eq16
    | exact resolve eq16 eq4759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4759
  have eq58239 : y = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq58238
       have r₂ := eq22 x
       grind)
    | exact resolve eq58238 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58238
  have eq77806 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X1 (τ (τ (M.op X0 (M.op X0 (σ (σ (M.op X1 X2)))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2052 x X1 X2
       have i₂ := eq5596 X0 (M.op X1 X2) x
       grind)
    | exact superpose eq5596 eq2052
    | exact resolve eq2052 eq5596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2052 eq5596
  have eq1788821 : ∀ X0 : G, (M.op x x) = (M.op y (τ (τ (M.op X0 (M.op X0 (σ (σ y))))))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq77806 X0 y x
       have i₂ := eq58239
       grind)
    | exact superpose eq58239 eq77806
    | exact resolve eq77806 eq58239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58239 eq77806
  have eq1788925 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq1788821 x
       have i₂ := eq5654 x y
       grind)
    | exact superpose eq5654 eq1788821
    | exact resolve eq1788821 eq5654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5654 eq1788821
  have eq3158287 : y = (τ (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1788925
       grind)
    | exact superpose eq1788925 eq10
    | exact resolve eq10 eq1788925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1788925
  have eq3159105 : x = y ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq3158287
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3158287
    | exact resolve eq3158287 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3158287
  have eq3159280 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3159105
       grind)
    | exact superpose eq3159105 eq16
    | exact resolve eq16 eq3159105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3159105
  have eq3159281 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq3159280
       have r₂ := eq22 x
       grind)
    | exact resolve eq3159280 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq3159280
  have eq3161362 : ∀ X0 : G, (M.op x x) = (τ (M.op (σ y) (M.op X0 (M.op X0 (σ y))))) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq45199 (σ y) X0 x
       have i₂ := eq3159281
       grind)
    | exact superpose eq3159281 eq45199
    | exact resolve eq45199 eq3159281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45199 eq3159281
  have eq3162292 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq3161362 x
       have i₂ := eq318 x (σ y)
       grind)
    | exact superpose eq318 eq3161362
    | exact resolve eq3161362 eq318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318 eq3161362
  have eq3162731 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq3162292
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq3162292
    | exact resolve eq3162292 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3162292
  have eq3162732 : y = (M.op x x) := by grind
  clear eq3162731
  have eq3163404 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1527 x x
       have i₂ := eq3162732
       grind)
    | exact superpose eq3162732 eq1527
    | exact resolve eq1527 eq3162732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1527 eq3162732
  have eq3163888 : False := by grind
  exact eq3163888

/-- `Equation947`: `x = y ◇ ((z ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,Y) else if m(Y,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyx_y_pyy_pxy_pyx_Equation947 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law947 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law947.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b b :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X0) (M.op X1 X0))) = X0 := by
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
  have eq50 : ∀ X0 : G, y = (M.op X0 (M.op (M.op x y) (M.op X0 y))) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y X0 x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op X2 X0)) = (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X3 X0) (M.op X2 X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X3 X0) (M.op X2 X0)) X1 X2
       have i₂ := eq14 X0 X2 X3
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
  have eq65 : x ≠ (M.op x y) ∨ (k x y) = (M.op y y) := by
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
  have eq66 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq75 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq79 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq11 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq74
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq74
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq74 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq16
    | exact resolve eq16 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq93
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq93
    | exact resolve eq93 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq99
    | exact resolve eq99 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
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
  have eq102 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq75
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq75 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq16
    | exact resolve eq16 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq102
  have eq213 : y = (M.op x (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq50
    | (have j0 := eq50 x
       grind)
    | exact resolve eq50 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq222 : (σ y) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq26 eq51
    | (have j0 := eq51 (σ x)
       grind)
    | exact resolve eq51 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq257 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq442 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq257 X0 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq257
    | (have j0 := eq257 X0 y
       grind)
    | exact resolve eq257 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257
  have eq490 : (k (k x y) y) = (τ (k (k (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq59 eq442
    | exact resolve eq442 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442
  have eq652 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X2 X0)) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X0 X2 X2 X1
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq830 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq77 X0 X1
       grind)
    | exact superpose eq77 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq77 X1 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq77 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq77 X0 X1
       grind)
    | exact resolve eq12 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq838 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq77 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq841 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq830 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830
  have eq843 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq841 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq841 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq841 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq841 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq841
  have eq853 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq843 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq843
    | (have j0 := eq843 X0 X1
       grind)
    | exact resolve eq843 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843
  have eq1057 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 y)) = (M.op X0 (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq652 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq652
    | (have j0 := eq652 y x X0
       grind)
    | exact resolve eq652 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1060 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) = (M.op X0 (M.op (σ y) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq652
    | (have j0 := eq652 (σ y) (σ x) X0
       grind)
    | exact resolve eq652 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1079 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 x
       have i₂ := eq652 X1 x X0
       grind)
    | exact superpose eq652 eq14
    | exact resolve eq14 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1142 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq1079 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq1079 (M.op X0 X0) X0
       grind)
    | exact superpose eq1079 eq1079
    | exact resolve eq1079 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1143 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1079 (M.op X1 X0) X0
       have i₂ := eq652 X0 X1 X0
       grind)
    | exact superpose eq652 eq1079
    | exact resolve eq1079 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1148 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X1 X1 X0 X0
       have i₂ := eq1079 X1 (M.op X0 X1)
       grind)
    | exact superpose eq1079 eq52
    | exact resolve eq52 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1162 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) (M.op X1 (M.op X0 X0)) X1
       have i₂ := eq1079 (M.op X1 (M.op X0 X0)) X0
       grind)
    | exact superpose eq1079 eq14
    | exact resolve eq14 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1169 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1148 X0 X1
       have i₂ := eq652 X1 X0 X0
       grind)
    | exact superpose eq652 eq1148
    | exact resolve eq1148 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1148
  have eq1177 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq13 (M.op X0 X0) X0
       have i₂ := eq1142 X0
       grind)
    | exact superpose eq1142 eq13
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X0
       have r₂ := eq1142 X0
       grind)
    | exact resolve eq13 eq1142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1142
  have eq1193 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq1177 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1177
  have eq1212 : (M.op (M.op x y) (M.op x y)) = (M.op x (M.op y y)) := by
    first
    | (have i₁ := eq1057 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1057
    | (have j0 := eq1057 x
       grind)
    | exact resolve eq1057 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1216 : y = (M.op (M.op x y) (M.op y (M.op y y))) := by
    first
    | exact superpose eq1057 eq1079
    | exact resolve eq1079 eq1057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1057
  have eq1358 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq26 eq1060
    | (have j0 := eq1060 (σ x)
       grind)
    | exact resolve eq1060 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1362 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq1060 eq1079
    | exact resolve eq1079 eq1060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1060
  have eq1593 : (M.op (M.op x y) (M.op x y)) = (M.op y (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))))) := by
    first
    | exact superpose eq213 eq1143
    | exact resolve eq1143 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1595 : (M.op y y) = (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op y y) (M.op (M.op y y) (M.op y y)))) := by
    first
    | (have i₁ := eq1143 (M.op y y) x
       have i₂ := eq1212
       grind)
    | exact superpose eq1212 eq1143
    | exact resolve eq1143 eq1212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1599 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) := by
    first
    | exact superpose eq222 eq1143
    | exact resolve eq1143 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1601 : (M.op (σ y) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ y) (σ y)) (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))))) := by
    first
    | exact superpose eq1358 eq1143
    | exact resolve eq1143 eq1358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1628 : (M.op (σ y) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | (have i₁ := eq1601
       have i₂ := eq1079 (M.op sF3 sF3) sF3
       grind)
    | exact superpose eq1079 eq1601
    | exact resolve eq1601 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1601
  have eq1630 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1599
       have i₂ := eq1079 (M.op sF4 sF4) sF4
       grind)
    | exact superpose eq1079 eq1599
    | exact resolve eq1599 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1599
  have eq1633 : (M.op y y) = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq1595
       have i₂ := eq1079 (M.op y y) y
       grind)
    | exact superpose eq1079 eq1595
    | exact resolve eq1595 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1595
  have eq1635 : (M.op y (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1593
       have i₂ := eq1079 (M.op sF0 sF0) sF0
       grind)
    | exact superpose eq1079 eq1593
    | exact resolve eq1593 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1593
  have eq1664 : (σ y) = (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1630 eq222
    | exact resolve eq222 eq1630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq1732 : y = (M.op x (M.op y (M.op x y))) := by
    first
    | exact superpose eq1635 eq213
    | exact resolve eq213 eq1635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq1734 : (M.op y (M.op x y)) = (k (M.op y (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq1635 eq1193
    | exact resolve eq1193 eq1635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1738 : (M.op x y) ≠ (M.op y (M.op x y)) ∨ (M.op y (M.op x y)) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq1635 eq13
    | exact resolve eq13 eq1635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1838 : (M.op (σ y) (σ y)) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq1630 eq1628
    | exact resolve eq1628 eq1630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1628
  have eq1839 : (M.op y y) = (M.op (M.op y (M.op x y)) y) := by
    first
    | exact superpose eq1635 eq1633
    | exact resolve eq1633 eq1635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1633
  have eq2422 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X1 X0) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1169 (M.op X1 X0) (M.op X0 (M.op X0 X0))
       have i₂ := eq1143 X0 X1
       grind)
    | exact superpose eq1143 eq1169
    | exact resolve eq1169 eq1143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1143
  have eq2430 : (M.op (M.op y (M.op y y)) y) = (M.op (M.op x y) (M.op (M.op y (M.op y y)) (M.op y (M.op y y)))) := by
    first
    | exact superpose eq1216 eq1169
    | exact resolve eq1169 eq1216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1216
  have eq2438 : (M.op (M.op (σ y) (M.op (σ y) (σ y))) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) (M.op (σ y) (σ y))) (M.op (σ y) (M.op (σ y) (σ y))))) := by
    first
    | exact superpose eq1362 eq1169
    | exact resolve eq1169 eq1362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1362
  have eq2442 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1079 X1 X0
       have i₂ := eq1169 X1 X0
       grind)
    | (have i₁ := eq1079 X1 X1
       have i₂ := eq1169 X1 X1
       grind)
    | exact superpose eq1169 eq1079
    | exact resolve eq1079 eq1169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2515 : (M.op (M.op (σ y) (M.op (σ y) (σ y))) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))))) := by
    first
    | (have i₁ := eq2438
       have i₂ := eq652 (M.op sF3 sF3) sF3 sF3
       grind)
    | exact superpose eq652 eq2438
    | exact resolve eq2438 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2438
  have eq2523 : (M.op (M.op y (M.op y y)) y) = (M.op (M.op x y) (M.op y (M.op (M.op y y) (M.op y y)))) := by
    first
    | (have i₁ := eq2430
       have i₂ := eq652 (M.op y y) y y
       grind)
    | exact superpose eq652 eq2430
    | exact resolve eq2430 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2430
  have eq2530 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X1 X0) (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq2422 X0 X1
       have i₂ := eq652 (M.op X0 X0) X0 X0
       grind)
    | exact superpose eq652 eq2422
    | exact resolve eq2422 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652 eq2422
  have eq2559 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ y) (M.op (σ y) (σ y))) (σ y)) := by
    first
    | (have i₁ := eq2515
       have i₂ := eq14 sF3 sF3 sF3
       grind)
    | exact superpose eq14 eq2515
    | exact resolve eq2515 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2515
  have eq2565 : (M.op (M.op x y) y) = (M.op (M.op y (M.op y y)) y) := by
    first
    | (have i₁ := eq2523
       have i₂ := eq14 y y y
       grind)
    | exact superpose eq14 eq2523
    | exact resolve eq2523 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2523
  have eq2570 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2530 X0 X1
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq2530
    | exact resolve eq2530 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2530
  have eq2585 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq2559
       have i₂ := eq1162 sF3 sF3
       grind)
    | exact superpose eq1162 eq2559
    | exact resolve eq2559 eq1162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2559
  have eq2591 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq2565
       have i₂ := eq1162 y y
       grind)
    | exact superpose eq1162 eq2565
    | exact resolve eq2565 eq1162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2565
  have eq2596 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2570 X0 X1
       have i₂ := eq1162 X0 X0
       grind)
    | exact superpose eq1162 eq2570
    | exact resolve eq2570 eq1162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1162 eq2570
  have eq5721 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq79 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq79
    | (have j0 := eq79 y
       grind)
    | exact resolve eq79 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq5747 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq5721
  have eq5753 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq5747
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq5747
    | exact resolve eq5747 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq5747
  have eq5773 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq5753
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq5753 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5753
  have eq5788 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq5773 eq107
    | exact resolve eq107 eq5773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq16701 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq101 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16702 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq16701
    | exact resolve eq16701 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16701
  have eq16713 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq16702
       have r₂ := eq27
       grind)
    | exact resolve eq16702 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16702
  have eq16715 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq16713
    | exact resolve eq16713 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16713
  have eq16717 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq16715 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq16715
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq16715
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq16715
       grind)
    | exact resolve eq12 eq16715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16729 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq16715 eq2442
    | exact resolve eq2442 eq16715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16715
  have eq16732 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq16717
  have eq16733 : (σ x) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq16729
       have i₂ := eq1169 sF2 sF3
       grind)
    | exact superpose eq1169 eq16729
    | exact resolve eq16729 eq1169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16729
  have eq16736 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq16732
    | exact resolve eq16732 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16732
  have eq16737 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq16736
  have eq16738 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1358 eq16733
    | exact resolve eq16733 eq1358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16733
  have eq16739 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq16737
    | exact resolve eq16737 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16737
  have eq16740 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1630 eq16738
    | exact resolve eq16738 eq1630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16738
  have eq16745 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq16739 eq59
    | exact resolve eq59 eq16739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16739
  have eq16758 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq16740 eq1664
    | exact resolve eq1664 eq16740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16764 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq16740 eq1838
    | exact resolve eq1838 eq16740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1838 eq16740
  have eq16805 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq16764
    | exact resolve eq16764 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16764
  have eq17121 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq16758 eq1193
    | exact resolve eq1193 eq16758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16758
  have eq17206 : (k y y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq16805 eq5788
    | exact resolve eq5788 eq16805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16805
  have eq17299 : (τ (σ y)) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq17121 eq98
    | exact resolve eq98 eq17121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq17300 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq17121 eq101
    | exact resolve eq101 eq17121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq17121
  have eq17314 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq17300
  have eq17323 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq17299
    | exact resolve eq17299 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17299
  have eq17518 : y ≠ y ∨ x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq17314
       grind)
    | exact superpose eq17314 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq17314
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq17314
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq17314
       grind)
    | exact resolve eq12 eq17314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17530 : x = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2442 x y
       have i₂ := eq17314
       grind)
    | exact superpose eq17314 eq2442
    | exact resolve eq2442 eq17314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17314
  have eq17533 : x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq17518
  have eq17534 : x = (M.op x (M.op y y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17530
       have i₂ := eq1169 x y
       grind)
    | exact superpose eq1169 eq17530
    | exact resolve eq17530 eq1169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17530
  have eq17537 : x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17533
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17533
    | exact resolve eq17533 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17533
  have eq17538 : x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq17537
  have eq17539 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17534
       have i₂ := eq1212
       grind)
    | exact superpose eq1212 eq17534
    | exact resolve eq17534 eq1212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17534
  have eq17540 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17538
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17538
    | exact resolve eq17538 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17538
  have eq17541 : x = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1635 eq17539
    | exact resolve eq17539 eq1635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17539
  have eq17543 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq17540
       grind)
    | exact superpose eq17540 eq44
    | exact resolve eq44 eq17540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq17540
  have eq17567 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq17543
    | exact resolve eq17543 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17543
  have eq17589 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17541 eq1732
    | exact resolve eq1732 eq17541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17541
  have eq17679 : y = (k y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1193 x
       have i₂ := eq17589
       grind)
    | exact superpose eq17589 eq1193
    | exact resolve eq1193 eq17589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17589
  have eq17889 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq74
       have i₂ := eq17679
       grind)
    | exact superpose eq17679 eq74
    | exact resolve eq74 eq17679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq17679
  have eq17913 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17889
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq17889
    | exact resolve eq17889 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17889
  have eq19067 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17913 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq17913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17913
  have eq19071 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq19067
    | exact resolve eq19067 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19067
  have eq19083 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq19071
    | exact resolve eq19071 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19071
  have eq19084 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq19083
  have eq22205 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq17323
       grind)
    | exact superpose eq17323 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq17323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17323
  have eq22215 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq22205
  have eq22224 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq22215
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq22215
    | exact resolve eq22215 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22215
  have eq22239 : x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq22224
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq22224
    | exact resolve eq22224 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22224
  have eq22240 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq22239
  have eq22280 : y ≠ y ∨ x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq22240
       grind)
    | exact superpose eq22240 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq22240
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq22240
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq22240
       grind)
    | exact resolve eq12 eq22240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22292 : x = (M.op y (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2442 x y
       have i₂ := eq22240
       grind)
    | exact superpose eq22240 eq2442
    | exact resolve eq2442 eq22240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22240
  have eq22295 : x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq22280
  have eq22296 : x = (M.op x (M.op y y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq22292
       have i₂ := eq1169 x y
       grind)
    | exact superpose eq1169 eq22292
    | exact resolve eq22292 eq1169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22292
  have eq22299 : x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq22295
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq22295
    | exact resolve eq22295 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22295
  have eq22300 : x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq22299
  have eq22301 : x = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq22296
       have i₂ := eq1212
       grind)
    | exact superpose eq1212 eq22296
    | exact resolve eq22296 eq1212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22296
  have eq22302 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq22300
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq22300
    | exact resolve eq22300 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22300
  have eq22303 : x = (M.op y (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1635 eq22301
    | exact resolve eq22301 eq1635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22301
  have eq23477 : (σ y) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq853 x y
       have i₂ := eq22302
       grind)
    | exact superpose eq22302 eq853
    | (have j0 := eq853 x y
       grind)
    | exact resolve eq853 eq22302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22302
  have eq23478 : (σ y) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq23477
    | exact resolve eq23477 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23477
  have eq23494 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq23478
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq23478
    | exact resolve eq23478 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23478
  have eq23505 : (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq23494
    | exact resolve eq23494 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23494
  have eq23514 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq23505
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq23505
    | exact resolve eq23505 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23505
  have eq23523 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq23514
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq23514
    | exact resolve eq23514 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23514
  have eq23532 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq23523
    | exact resolve eq23523 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23523
  have eq23541 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq23532
       have r₂ := eq27
       grind)
    | exact resolve eq23532 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23532
  have eq23556 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq23541
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq23541
    | exact resolve eq23541 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23541
  have eq23561 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq23556
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq23556
    | exact resolve eq23556 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23556
  have eq23562 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq23561
    | exact resolve eq23561 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23561
  have eq23563 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq23562
  have eq23570 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22303 eq1839
    | exact resolve eq1839 eq22303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1839 eq22303
  have eq23610 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq23570
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq23570
    | exact resolve eq23570 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23570
  have eq31371 : (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq5773 eq108
    | exact resolve eq108 eq5773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq5773
  have eq33014 : (M.op y x) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq16745
       grind)
    | exact superpose eq16745 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq16745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16745
  have eq33024 : (M.op y x) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq33014
  have eq33039 : x = (M.op x y) ∨ (M.op y x) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq33024
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq33024
    | exact resolve eq33024 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33024
  have eq33040 : (M.op y x) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq33039
  have eq33120 : y ≠ (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq33040
  have eq33435 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq19084 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq19084
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq19084
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq19084
       grind)
    | exact resolve eq12 eq19084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19084
  have eq33451 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq33435
  have eq33455 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq33451
    | exact resolve eq33451 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33451
  have eq33456 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq33455
  have eq33458 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq33456
    | exact resolve eq33456 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33456
  have eq34198 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq33458 eq17567
    | exact resolve eq17567 eq33458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17567 eq33458
  have eq34211 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq34198
  have eq34215 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq34211
       have r₂ := eq27
       grind)
    | exact resolve eq34211 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34211
  have eq34232 : (σ y) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq34215 eq1664
    | exact resolve eq1664 eq34215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34263 : (σ x) ≠ (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  have eq34277 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1358 eq34232
    | exact resolve eq34232 eq1358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1358 eq34232
  have eq34283 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1630 eq34277
    | exact resolve eq34277 eq1630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1630 eq34277
  have eq34529 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq34215 eq34283
    | exact resolve eq34283 eq34215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34215 eq34283
  have eq34575 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq34529
  have eq34597 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq34575
       have r₂ := eq34263
       grind)
    | exact resolve eq34575 eq34263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34263 eq34575
  have eq35249 : (τ (σ y)) = (k y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq34597 eq5788
    | exact resolve eq5788 eq34597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34597
  have eq35337 : y = (k y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29 eq35249
    | exact resolve eq35249 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq35249
  have eq35810 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq35337
       grind)
    | exact superpose eq35337 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq35337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35337
  have eq35832 : y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq35810
  have eq36694 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq23610
       have i₂ := eq35832
       grind)
    | exact superpose eq35832 eq23610
    | exact resolve eq23610 eq35832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23610 eq35832
  have eq36757 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq36694
  have eq36778 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq36757
       have r₂ := eq23563
       grind)
    | exact resolve eq36757 eq23563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23563 eq36757
  have eq36807 : (σ x) ≠ (σ x) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq36778 eq66
    | (have r₁ := eq66
       have r₂ := eq36778
       grind)
    | exact resolve eq66 eq36778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq36817 : (σ y) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq36778 eq1664
    | exact resolve eq1664 eq36778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1664 eq36778
  have eq36843 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq36807
  have eq37679 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq36817 eq2442
    | exact resolve eq2442 eq36817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36817
  have eq37729 : (τ (σ x)) = (k y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq37679 eq5788
    | exact resolve eq5788 eq37679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37679
  have eq37814 : x = (k y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq37729
    | exact resolve eq37729 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq37729
  have eq38010 : (k x y) = (τ (M.op (σ y) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq36843 eq59
    | exact resolve eq59 eq36843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq38015 : (k (k x y) y) = (τ (k (M.op (σ y) (σ y)) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq36843 eq490
    | exact resolve eq490 eq36843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490 eq36843
  have eq38044 : (τ (M.op (σ y) (σ y))) = (k (k x y) y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq38015
       have i₂ := eq1193 sF3
       grind)
    | exact superpose eq1193 eq38015
    | exact resolve eq38015 eq1193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38015
  have eq38049 : (k x y) = (k y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5788 eq38010
    | exact resolve eq38010 eq5788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38010
  have eq38051 : (k y y) = (k (k x y) y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5788 eq38044
    | exact resolve eq38044 eq5788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5788 eq38044
  have eq39528 : (k x y) = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq38049
       grind)
    | exact superpose eq38049 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq38049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38049
  have eq39545 : (k x y) = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq39528
  have eq39566 : (k x y) = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq39545
       have r₂ := eq65
       grind)
    | exact resolve eq39545 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq39545
  have eq59565 : (k y y) = (k (M.op y y) y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq38051
       have i₂ := eq39566
       grind)
    | exact superpose eq39566 eq38051
    | exact resolve eq38051 eq39566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38051 eq39566
  have eq59582 : (k y y) = (k (M.op y y) y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y y) := by grind
  clear eq59565
  have eq59598 : (M.op y y) = (k y y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq59582
       have i₂ := eq1193 y
       grind)
    | exact superpose eq1193 eq59582
    | exact resolve eq59582 eq1193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59582
  have eq59610 : (M.op y y) = (k y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq59598
       have r₂ := eq13 x y
       grind)
    | (have r₁ := eq59598
       have r₂ := eq13 y y
       grind)
    | exact resolve eq59598 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59598
  have eq59677 : x = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq37814
       have i₂ := eq59610
       grind)
    | exact superpose eq59610 eq37814
    | exact resolve eq37814 eq59610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37814 eq59610
  have eq59704 : x = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq59677
  have eq61216 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2596 y y
       have i₂ := eq59704
       grind)
    | exact superpose eq59704 eq2596
    | exact resolve eq2596 eq59704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59704
  have eq61230 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq61216
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq61216
    | exact resolve eq61216 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61216
  have eq61231 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq61230
  have eq61239 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq61231 eq20
    | exact resolve eq20 eq61231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61302 : y = (M.op x (M.op y y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq61231 eq1732
    | exact resolve eq1732 eq61231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1732
  have eq61361 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq61378 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq61302
       have i₂ := eq1212
       grind)
    | exact superpose eq1212 eq61302
    | exact resolve eq61302 eq1212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1212 eq61302
  have eq61433 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq61239
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq61239
    | exact resolve eq61239 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61239
  have eq61440 : y = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1635 eq61378
    | exact resolve eq61378 eq1635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1635 eq61378
  have eq61470 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq61433 eq26
    | exact resolve eq26 eq61433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61540 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq61433 eq2585
    | exact resolve eq2585 eq61433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2585
  have eq61855 : y = (k y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq61440 eq1734
    | exact resolve eq1734 eq61440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1734
  have eq61858 : y ≠ (M.op x y) ∨ y = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq61440 eq1738
    | exact resolve eq1738 eq61440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1738 eq61440
  have eq61947 : y = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq61858
       have r₂ := eq61231
       grind)
    | exact resolve eq61858 eq61231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61858
  have eq61976 : y = (k y y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq61231 eq61855
    | exact resolve eq61855 eq61231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61231 eq61855
  have eq62015 : y = (k y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq61976
       have r₂ := eq61361
       grind)
    | exact resolve eq61976 eq61361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61361 eq61976
  have eq62080 : (σ y) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq61947 eq838
    | (have j0 := eq838 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq838 eq61947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq838 eq61947
  have eq62083 : (σ y) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq62080
  have eq62094 : (σ y) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq62083
    | exact resolve eq62083 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62083
  have eq62116 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq62094
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq62094
    | exact resolve eq62094 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62094
  have eq62130 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq62116
       have r₂ := eq61433
       grind)
    | exact resolve eq62116 eq61433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62116
  have eq62140 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq62130
    | exact resolve eq62130 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62130
  have eq63378 : y = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17206
       have i₂ := eq62015
       grind)
    | exact superpose eq62015 eq17206
    | exact resolve eq17206 eq62015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17206 eq62015
  have eq63432 : y = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq63378
  have eq63453 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq63432
       have r₂ := eq33120
       grind)
    | exact resolve eq63432 eq33120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33120 eq63432
  have eq63699 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (M.op X0 (σ (M.op x y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq62140 eq1079
    | exact resolve eq1079 eq62140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1079 eq62140
  have eq73863 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq61540 eq63699
    | exact resolve eq63699 eq61540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61540 eq63699
  have eq73935 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by grind
  clear eq73863
  have eq73983 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq73935
       have i₂ := eq1169 sF4 sF1
       grind)
    | exact superpose eq1169 eq73935
    | exact resolve eq73935 eq1169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1169 eq73935
  have eq76936 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq73983 eq2442
    | exact resolve eq2442 eq73983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2442 eq73983
  have eq109446 : y ≠ y ∨ x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq63453
       grind)
    | exact superpose eq63453 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq63453
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq63453
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq63453
       grind)
    | exact resolve eq12 eq63453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63453
  have eq109467 : x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq109446
  have eq109491 : x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq109467
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq109467
    | exact resolve eq109467 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109467
  have eq109492 : x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq109491
  have eq109494 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq109492
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq109492
    | exact resolve eq109492 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109492
  have eq111175 : (σ y) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq853 x y
       have i₂ := eq109494
       grind)
    | exact superpose eq109494 eq853
    | (have j0 := eq853 x y
       grind)
    | exact resolve eq853 eq109494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109494
  have eq111188 : (σ y) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq111175
    | exact resolve eq111175 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111175
  have eq111207 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq111188
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq111188
    | exact resolve eq111188 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111188
  have eq111218 : (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq111207
       have r₂ := eq61433
       grind)
    | exact resolve eq111207 eq61433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61433 eq111207
  have eq111227 : (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq111218
    | exact resolve eq111218 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111218
  have eq111236 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq111227
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq111227
    | exact resolve eq111227 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111227
  have eq111245 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq111236
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq111236
    | exact resolve eq111236 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111236
  have eq111254 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq111245
    | exact resolve eq111245 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111245
  have eq111267 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq111254
       have r₂ := eq27
       grind)
    | exact resolve eq111254 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111254
  have eq111276 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq111267
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq111267
    | exact resolve eq111267 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111267
  have eq111277 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq111276
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq111276
    | exact resolve eq111276 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111276
  have eq111278 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq111277
    | exact resolve eq111277 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111277
  have eq111279 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq111278
  have eq111413 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq111279 eq76936
    | exact resolve eq76936 eq111279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76936 eq111279
  have eq111458 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq111413
  have eq111566 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq111458 eq61470
    | exact resolve eq61470 eq111458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61470 eq111458
  have eq111602 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq111566
  have eq111614 : x = (M.op x y) := by
    first
    | (have r₁ := eq111602
       have r₂ := eq27
       grind)
    | exact resolve eq111602 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111602
  have eq111622 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq111614 eq20
    | exact resolve eq20 eq111614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq111731 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq111614 eq2591
    | exact resolve eq2591 eq111614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2591
  have eq111792 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq111731
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq111731
    | exact resolve eq111731 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq111731
  have eq111876 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq111622
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq111622
    | exact resolve eq111622 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111622
  have eq111882 : x = (M.op y y) := by
    first
    | exact superpose eq111614 eq111792
    | exact resolve eq111792 eq111614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111614 eq111792
  have eq111907 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq111876 eq26
    | exact resolve eq26 eq111876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112257 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq31371
       have i₂ := eq111882
       grind)
    | exact superpose eq111882 eq31371
    | exact resolve eq31371 eq111882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31371
  have eq112299 : x = (k x y) := by
    first
    | (have i₁ := eq1193 y
       have i₂ := eq111882
       grind)
    | exact superpose eq111882 eq1193
    | exact resolve eq1193 eq111882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1193 eq111882
  have eq112365 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq112257
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq112257
    | exact resolve eq112257 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112257
  have eq112377 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq111876 eq112365
    | exact resolve eq112365 eq111876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112365
  have eq112508 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq853 x y
       have i₂ := eq112299
       grind)
    | exact superpose eq112299 eq853
    | (have j0 := eq853 x y
       grind)
    | exact resolve eq853 eq112299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq853 eq112299
  have eq112509 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq112508
  have eq112516 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq112509
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq112509
    | exact resolve eq112509 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112509
  have eq112536 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq112516
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq112516
    | exact resolve eq112516 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112516
  have eq112554 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq111876 eq112536
    | exact resolve eq112536 eq111876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112536
  have eq112571 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq112554
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq112554
    | exact resolve eq112554 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112554
  have eq112582 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq112571
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq112571
    | exact resolve eq112571 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112571
  have eq112590 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq26 eq112582
    | exact resolve eq112582 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq112582
  have eq112598 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq111876 eq112590
    | exact resolve eq112590 eq111876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112590
  have eq112606 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have r₁ := eq112598
       have r₂ := eq27
       grind)
    | exact resolve eq112598 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112598
  have eq114823 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq112377 eq2596
    | exact resolve eq2596 eq112377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2596 eq112377
  have eq114831 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq111907 eq114823
    | exact resolve eq114823 eq111907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111907 eq114823
  have eq114846 : x = y := by
    first
    | (have r₁ := eq114831
       have r₂ := eq27
       grind)
    | exact resolve eq114831 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq114831
  have eq114860 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq114846
       grind)
    | exact superpose eq114846 eq24
    | exact resolve eq24 eq114846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq114846
  have eq115351 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq114860
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq114860
    | exact resolve eq114860 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq114860
  have eq115472 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq111876 eq115351
    | exact resolve eq115351 eq111876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111876 eq115351
  have eq115549 : False := by grind
  exact eq115549

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(Y,Y) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pyx_y_pyy_x_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
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
  have eq50 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
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
  have eq51 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
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
  have eq53 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
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
  have eq63 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq63 (σ X0)
       grind)
    | exact superpose eq63 eq10
    | exact resolve eq10 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq63 sF2
       grind)
    | exact superpose eq63 eq49
    | exact resolve eq49 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq68 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq67
       have i₂ := eq63 x
       grind)
    | exact superpose eq63 eq67
    | exact resolve eq67 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq70 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq65 X0
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq65
    | exact resolve eq65 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq97 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq98 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq102 : (σ (k y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq98
       have i₂ := eq63 sF3
       grind)
    | exact superpose eq63 eq98
    | exact resolve eq98 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq104 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq102
       have i₂ := eq63 y
       grind)
    | exact superpose eq63 eq102
    | exact resolve eq102 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq106 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq97
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq97
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq97 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq106
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq106
    | exact resolve eq106 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq20 eq112
    | exact resolve eq112 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq114 : x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq113
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq113
    | exact resolve eq113 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
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
  have eq143 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq104
       grind)
    | exact superpose eq104 eq16
    | exact resolve eq16 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq235 : (M.op y (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq50 (M.op sF0 sF0)
       have i₂ := eq14 sF0 sF0 sF0
       grind)
    | exact superpose eq14 eq50
    | exact resolve eq50 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq237 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq242 : (M.op x y) = (M.op y (M.op (M.op x y) (M.op y (M.op x y)))) := by
    first
    | exact superpose eq235 eq50
    | exact resolve eq50 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq313 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (τ X0)
       have i₂ := eq63 (τ X0)
       grind)
    | exact superpose eq63 eq34
    | exact resolve eq34 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq324 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq313 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq313
    | exact resolve eq313 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313
  have eq327 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq324 X0
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq324
    | exact resolve eq324 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq324
  have eq441 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 X0 X0
       have i₂ := eq53 X0 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq445 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op X1 X0)
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq51
    | exact resolve eq51 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq446 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op y (M.op (M.op x y) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq50 (M.op X1 X0)
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq50
    | exact resolve eq50 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq555 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq52 X3 x (M.op (M.op x x) (M.op X0 X0)) X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq588 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq53 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
       have i₂ := eq52 X0 x x X3
       grind)
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq595 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq50 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq52 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq52 eq50
    | exact resolve eq50 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq596 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) X2 X3
       have i₂ := eq52 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq597 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq596 X0 X1 X2 X3
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq596
    | exact resolve eq596 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596
  have eq598 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq595 X0 X1
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq595
    | exact resolve eq595 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq595
  have eq634 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ (M.op X0 X0)) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0) (σ X0)
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq14
    | exact resolve eq14 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq640 : ∀ X0 X1 X2 : G, (σ X0) = (M.op X1 (M.op (M.op X2 X1) (σ (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (σ X0) X1 X2
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq14
    | exact resolve eq14 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq891 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq327 X0
       grind)
    | exact superpose eq327 eq16
    | exact resolve eq16 eq327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327
  have eq1047 : ∀ X0 : G, (τ X0) = (M.op y (M.op (M.op x y) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq50 (τ X0)
       have i₂ := eq891 X0
       grind)
    | exact superpose eq891 eq50
    | exact resolve eq50 eq891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq891
  have eq1221 : (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) = (M.op y (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq237 eq50
    | exact resolve eq50 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237
  have eq1236 : (M.op (M.op x y) (M.op y (M.op x y))) = (M.op y (M.op y (M.op x y))) := by
    first
    | exact superpose eq235 eq1221
    | exact resolve eq1221 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1221
  have eq1769 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq555 X0 X0 X0
       grind)
    | exact superpose eq555 eq14
    | exact resolve eq14 eq555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1770 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq50 (M.op X0 (M.op X0 X0))
       have i₂ := eq555 X0 X0 X0
       grind)
    | exact superpose eq555 eq50
    | exact resolve eq50 eq555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1771 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq51 (M.op X0 (M.op X0 X0))
       have i₂ := eq555 X0 X0 X0
       grind)
    | exact superpose eq555 eq51
    | exact resolve eq51 eq555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq1781 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq588 (M.op x (M.op x x)) x
       have i₂ := eq555 x x x
       grind)
    | exact superpose eq555 eq588
    | exact resolve eq588 eq555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555 eq588
  have eq1846 : (M.op x y) = (M.op y (M.op y (M.op y (M.op x y)))) := by
    first
    | exact superpose eq1236 eq242
    | exact resolve eq242 eq1236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242 eq1236
  have eq2051 : ∀ X0 : G, (M.op X0 (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq441 X0
       have i₂ := eq1770 X0
       grind)
    | exact superpose eq1770 eq441
    | exact resolve eq441 eq1770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2078 : (M.op (M.op x y) y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op y (M.op y y)))) := by
    first
    | exact superpose eq1770 eq445
    | exact resolve eq445 eq1770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1770
  have eq2088 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq445 eq2078
    | exact resolve eq2078 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2078
  have eq2124 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | exact superpose eq50 eq2051
    | exact resolve eq2051 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq2051
  have eq2398 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ y) (σ y))))) := by
    first
    | exact superpose eq1771 eq445
    | exact resolve eq445 eq1771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1771
  have eq2408 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq445 eq2398
    | exact resolve eq2398 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445 eq2398
  have eq2752 : y = (M.op (M.op x y) (M.op y (M.op y y))) := by
    first
    | (have i₁ := eq1781 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1781
    | (have j0 := eq1781 y x
       grind)
    | exact resolve eq1781 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5818 : ∀ X0 X1 X2 X3 : G, (M.op y (M.op (M.op x y) (M.op X0 X1))) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq597 X0 X1 X2 X3
       have i₂ := eq598 X0 X1
       grind)
    | exact superpose eq598 eq597
    | exact resolve eq597 eq598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597 eq598
  have eq5904 : ∀ X0 X1 X2 : G, (M.op y (M.op (M.op x y) X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5818 X0 (M.op X0 (M.op X0 X0)) X2 x
       have i₂ := eq441 X0
       grind)
    | exact superpose eq441 eq5818
    | exact resolve eq5818 eq441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441 eq5818
  have eq17074 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq115 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17075 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq17074
    | exact resolve eq17074 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17074
  have eq17083 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq17075
       have r₂ := eq27
       grind)
    | exact resolve eq17075 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17075
  have eq17086 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq17083
    | exact resolve eq17083 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17083
  have eq17089 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq17086
    | exact resolve eq17086 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17086
  have eq17092 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq17089 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq17089
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq17089
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq17089
       grind)
    | exact resolve eq13 eq17089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17089
  have eq17131 : (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq17092
       have r₂ := eq26
       grind)
    | exact resolve eq17092 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17092
  have eq17328 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq17131 eq115
    | exact resolve eq115 eq17131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq17131
  have eq17333 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq17328
  have eq17350 : (τ (σ (M.op x y))) = (M.op x x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17333 eq68
    | exact resolve eq68 eq17333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq17380 : (τ (σ x)) = (M.op y (M.op (M.op x y) (τ (σ (M.op x y))))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17333 eq1047
    | exact resolve eq1047 eq17333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1047 eq17333
  have eq17429 : (τ (σ x)) = (M.op y (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq17380
    | exact resolve eq17380 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17380
  have eq17433 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq17350
    | exact resolve eq17350 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq17350
  have eq17437 : (τ (σ x)) = (M.op y (M.op y (M.op x y))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq235 eq17429
    | exact resolve eq17429 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235 eq17429
  have eq17441 : x = (M.op y (M.op y (M.op x y))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq17437
    | exact resolve eq17437 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17437
  have eq18452 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17441 eq1846
    | exact resolve eq1846 eq17441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1846 eq17441
  have eq18486 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq18452
  have eq18645 : x = (M.op (M.op x y) (M.op x (M.op x x))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1781 x y
       have i₂ := eq18486
       grind)
    | exact superpose eq18486 eq1781
    | exact resolve eq1781 eq18486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1781
  have eq19158 : (M.op y x) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18645 eq446
    | exact resolve eq446 eq18645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446 eq18645
  have eq19225 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17433
       have i₂ := eq19158
       grind)
    | exact superpose eq19158 eq17433
    | exact resolve eq17433 eq19158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17433 eq19158
  have eq19258 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq19225
  have eq20635 : ∀ X0 : G, (M.op (σ x) (M.op (σ (M.op x y)) (M.op X0 X0))) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq634 x X0
       have i₂ := eq19258
       grind)
    | exact superpose eq19258 eq634
    | exact resolve eq634 eq19258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634 eq19258
  have eq20725 : ∀ X0 : G, (M.op (σ x) (M.op (σ (M.op x y)) (M.op X0 X0))) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq20 eq20635
    | (have j0 := eq20635 X0
       grind)
    | exact resolve eq20635 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20635
  have eq20768 : ∀ X0 : G, (M.op (σ x) (M.op (σ (M.op x y)) (M.op X0 X0))) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq20725 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq20725
    | (have j0 := eq20725 X0
       grind)
    | exact resolve eq20725 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20725
  have eq21598 : ∀ X0 : G, (σ X0) = (M.op x (M.op (M.op x y) (σ (M.op X0 X0)))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq640 X0 x y
       have i₂ := eq18486
       grind)
    | exact superpose eq18486 eq640
    | exact resolve eq640 eq18486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640
  have eq27594 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op x (M.op (M.op x y) X0)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1769 X0 x y
       have i₂ := eq18486
       grind)
    | exact superpose eq18486 eq1769
    | exact resolve eq1769 eq18486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1769
  have eq29224 : ∀ X0 : G, (M.op y (M.op (M.op x y) X0)) = (M.op x (M.op (M.op x y) X0)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq5904 X0 x y
       have i₂ := eq18486
       grind)
    | exact superpose eq18486 eq5904
    | exact resolve eq5904 eq18486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5904 eq18486
  have eq43899 : (σ (M.op x y)) = (M.op (σ x) (M.op x (M.op (M.op x y) (σ (M.op x y))))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20768 sF1
       have i₂ := eq27594 sF1
       grind)
    | exact superpose eq27594 eq20768
    | exact resolve eq20768 eq27594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20768 eq27594
  have eq43961 : (σ (M.op x y)) = (M.op (σ x) (M.op x (M.op (M.op x y) (σ (M.op x y))))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq43899
  have eq45688 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2752 eq29224
    | exact resolve eq29224 eq2752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2752 eq29224
  have eq45875 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45688
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq45688
    | exact resolve eq45688 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45688
  have eq45976 : (σ y) = (M.op x (M.op (M.op x y) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq21598 y
       have i₂ := eq45875
       grind)
    | exact superpose eq45875 eq21598
    | exact resolve eq21598 eq45875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21598 eq45875
  have eq46021 : (σ y) = (M.op x (M.op (M.op x y) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq45976
  have eq46044 : (σ y) = (M.op x (M.op (M.op x y) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq46021
    | exact resolve eq46021 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46021
  have eq46092 : (σ y) = (M.op x (M.op (M.op x y) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq46044
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq46044
    | exact resolve eq46044 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq46044
  have eq51879 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq46092 eq43961
    | exact resolve eq43961 eq46092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43961 eq46092
  have eq51927 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq51879
  have eq51939 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq51927
    | exact resolve eq51927 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51927
  have eq51941 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq51939
       have r₂ := eq27
       grind)
    | exact resolve eq51939 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51939
  have eq51986 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq51941 eq2408
    | exact resolve eq2408 eq51941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2408
  have eq51995 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq51986
    | exact resolve eq51986 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51986
  have eq52007 : (M.op y y) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq51995 eq143
    | exact resolve eq143 eq51995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143 eq51995
  have eq52300 : (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2124 y
       have i₂ := eq52007
       grind)
    | exact superpose eq52007 eq2124
    | exact resolve eq2124 eq52007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52007
  have eq52745 : (τ (σ x)) = (M.op (τ (σ x)) y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq51941 eq52300
    | exact resolve eq52300 eq51941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51941 eq52300
  have eq52793 : (τ (σ x)) = (M.op (τ (σ x)) y) ∨ x = (M.op x y) := by grind
  clear eq52745
  have eq52805 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq52793
    | exact resolve eq52793 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq52793
  have eq52812 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq52805
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52805
    | exact resolve eq52805 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52805
  have eq52813 : x = (M.op x y) := by grind
  clear eq52812
  have eq52816 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq52813 eq20
    | exact resolve eq20 eq52813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq52914 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq52813 eq2088
    | exact resolve eq2088 eq52813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2088
  have eq52938 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq52914
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52914
    | exact resolve eq52914 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq52914
  have eq52997 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq52816
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq52816
    | exact resolve eq52816 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52816
  have eq52998 : x = (M.op y y) := by
    first
    | exact superpose eq52813 eq52938
    | exact resolve eq52938 eq52813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52813 eq52938
  have eq53025 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq52997 eq26
    | exact resolve eq26 eq52997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq53277 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq104
       have i₂ := eq52998
       grind)
    | exact superpose eq52998 eq104
    | exact resolve eq104 eq52998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq52998
  have eq53497 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq53277
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq53277
    | exact resolve eq53277 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq53277
  have eq53530 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq52997 eq53497
    | exact resolve eq53497 eq52997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52997 eq53497
  have eq53711 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq53530 eq2124
    | exact resolve eq2124 eq53530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2124 eq53530
  have eq53784 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq53025 eq53711
    | exact resolve eq53711 eq53025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53025 eq53711
  have eq53832 : False := by grind
  exact eq53832

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(X,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxx_y_pyx_pyy_pxy_Equation960 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
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
  have eq51 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
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
  have eq52 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
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
  have eq54 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
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
  have eq73 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq74 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq77 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ x) (σ X0)
       grind)
    | exact resolve eq11 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq78 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
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
  have eq83 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq45
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq45 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : (k (σ x) (σ (M.op x y))) = (σ (M.op x (M.op x y))) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq46
       have i₂ := eq11 x sF0
       grind)
    | exact superpose eq11 eq46
    | (have j1 := eq11 x (M.op x y)
       grind)
    | exact resolve eq46 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq91 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq83
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq83
    | exact resolve eq83 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq93 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq91
    | exact resolve eq91 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq94 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq101 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq74
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq74 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq16
    | exact resolve eq16 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq101
  have eq135 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ X0) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
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
  have eq158 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq135 eq16
    | exact resolve eq16 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq480 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k X0 (M.op X0 X0)) ∨ (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    grind
  have eq481 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 X0 X0
       have i₂ := eq54 X0 X0
       grind)
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq485 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (M.op X1 X0)
       have i₂ := eq54 X1 X0
       grind)
    | exact superpose eq54 eq52
    | exact resolve eq52 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq540 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq53 X3 x (M.op (M.op x x) (M.op X0 X0)) X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq576 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq54 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
       have i₂ := eq53 X0 x x X3
       grind)
    | exact superpose eq53 eq54
    | exact resolve eq54 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq54
  have eq1813 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq51 (M.op X0 (M.op X0 X0))
       have i₂ := eq540 X0 X0 X0
       grind)
    | exact superpose eq540 eq51
    | exact resolve eq51 eq540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1814 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq52 (M.op X0 (M.op X0 X0))
       have i₂ := eq540 X0 X0 X0
       grind)
    | exact superpose eq540 eq52
    | exact resolve eq52 eq540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1960 : ∀ X0 : G, (M.op X0 (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq481 X0
       have i₂ := eq1813 X0
       grind)
    | exact superpose eq1813 eq481
    | exact resolve eq481 eq1813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481
  have eq1989 : (M.op (M.op x y) y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op y (M.op y y)))) := by
    first
    | exact superpose eq1813 eq485
    | exact resolve eq485 eq1813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1813
  have eq2001 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq485 eq1989
    | exact resolve eq1989 eq485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1989
  have eq2038 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | exact superpose eq51 eq1960
    | exact resolve eq1960 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq1960
  have eq2082 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq13 (M.op X0 X0) X0
       have i₂ := eq2038 X0
       grind)
    | exact superpose eq2038 eq13
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X0
       have r₂ := eq2038 X0
       grind)
    | exact resolve eq13 eq2038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2103 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq2082 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2082
  have eq2196 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ y) (σ y))))) := by
    first
    | exact superpose eq1814 eq485
    | exact resolve eq485 eq1814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1814
  have eq2208 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq485 eq2196
    | exact resolve eq2196 eq485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485 eq2196
  have eq8230 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq77 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq77
    | (have j0 := eq77 x
       grind)
    | exact resolve eq77 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq8256 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq8230
  have eq8263 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq8256
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq8256
    | exact resolve eq8256 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8256
  have eq8280 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq8263
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq8263 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8263
  have eq8412 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq78 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq78
    | (have j0 := eq78 y
       grind)
    | exact resolve eq78 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq8437 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq8412
  have eq8443 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq8437
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq8437
    | exact resolve eq8437 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq8437
  have eq8466 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq8443
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq8443 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8443
  have eq8491 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq8466 eq106
    | exact resolve eq106 eq8466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq8737 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq136
    | (have j0 := eq136 (M.op x y)
       grind)
    | exact resolve eq136 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq8761 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq8737
  have eq8766 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq135 eq8761
    | exact resolve eq8761 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135 eq8761
  have eq8794 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq8766
       have r₂ := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq8766 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8766
  have eq8831 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq8794 eq158
    | exact resolve eq158 eq8794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq24831 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq94 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24832 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq24831
    | exact resolve eq24831 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24831
  have eq24843 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq24832
       have r₂ := eq28
       grind)
    | exact resolve eq24832 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24832
  have eq24845 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq24843
    | exact resolve eq24843 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24843
  have eq25393 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq24845 eq480
    | exact resolve eq480 eq24845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24845
  have eq25556 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq25393
    | exact resolve eq25393 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25393
  have eq25588 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq25556
    | exact resolve eq25556 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25556
  have eq25589 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq25588
  have eq26468 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq25589 eq94
    | exact resolve eq94 eq25589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq25589
  have eq26480 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq26468
  have eq26482 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq26480
       have r₂ := eq28
       grind)
    | exact resolve eq26480 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26480
  have eq26504 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq480 x
       have i₂ := eq26482
       grind)
    | exact superpose eq26482 eq480
    | exact resolve eq480 eq26482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480
  have eq26545 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2103 x
       have i₂ := eq26482
       grind)
    | exact superpose eq26482 eq2103
    | exact resolve eq2103 eq26482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26482
  have eq26629 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq26545
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq26545
    | exact resolve eq26545 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26545
  have eq26673 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq26504
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq26504
    | exact resolve eq26504 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26504
  have eq26709 : x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq26673
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq26673
    | exact resolve eq26673 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26673
  have eq26710 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq26709
  have eq27593 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq26629
       grind)
    | exact superpose eq26629 eq73
    | exact resolve eq73 eq26629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq26629
  have eq27615 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq27593
    | exact resolve eq27593 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27593
  have eq27717 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq26710
       grind)
    | exact superpose eq26710 eq45
    | exact resolve eq45 eq26710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq26710
  have eq27739 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq27717
    | exact resolve eq27717 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27717
  have eq29010 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27739 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq27739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27739
  have eq29013 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq29010
    | exact resolve eq29010 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29010
  have eq29024 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq29013
       have r₂ := eq28
       grind)
    | exact resolve eq29013 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29013
  have eq29026 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq29024
    | exact resolve eq29024 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29024
  have eq29027 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq29026
  have eq29528 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29027 eq2103
    | exact resolve eq2103 eq29027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2103 eq29027
  have eq29609 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq29528
    | exact resolve eq29528 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29528
  have eq30058 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29609 eq27615
    | exact resolve eq27615 eq29609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27615 eq29609
  have eq30065 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq30058
  have eq30067 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq30065
       have r₂ := eq28
       grind)
    | exact resolve eq30065 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30065
  have eq30070 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (M.op X0 X0))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq30067 eq52
    | exact resolve eq52 eq30067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq30102 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30067 eq2208
    | exact resolve eq2208 eq30067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2208
  have eq30111 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq30102
    | exact resolve eq30102 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30102
  have eq35533 : (σ y) = (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30111 eq30070
    | exact resolve eq30070 eq30111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30070 eq30111
  have eq35600 : (σ y) = (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by grind
  clear eq35533
  have eq35646 : (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30067 eq35600
    | exact resolve eq35600 eq30067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30067 eq35600
  have eq35707 : (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by grind
  clear eq35646
  have eq35959 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (M.op (σ y) (σ y))) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq35707 eq540
    | exact resolve eq540 eq35707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540 eq35707
  have eq36034 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq35959 x
       have i₂ := eq576 sF3 x
       grind)
    | exact superpose eq576 eq35959
    | exact resolve eq35959 eq576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576 eq35959
  have eq36046 : (τ (σ x)) = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq36034 eq8491
    | exact resolve eq8491 eq36034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36034
  have eq36224 : x = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq36046
    | exact resolve eq36046 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq36046
  have eq36930 : x = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq36224
       grind)
    | exact superpose eq36224 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq36224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36931 : y = (M.op y y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq36930
  have eq39202 : (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq8466 eq107
    | exact resolve eq107 eq8466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq8466
  have eq121592 : y ≠ y ∨ y = (k y y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq36931
       grind)
    | exact superpose eq36931 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq36931
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq36931
       grind)
    | exact resolve eq13 eq36931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121680 : x ≠ y ∨ x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq36931
  have eq121684 : y = (k y y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq121592
  have eq144495 : x = y ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq36224
       have i₂ := eq121684
       grind)
    | exact superpose eq121684 eq36224
    | exact resolve eq36224 eq121684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36224 eq121684
  have eq144540 : x = y ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq144495
  have eq144570 : x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq144540
       have r₂ := eq121680
       grind)
    | exact resolve eq144540 eq121680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121680 eq144540
  have eq144763 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2038 y
       have i₂ := eq144570
       grind)
    | exact superpose eq144570 eq2038
    | exact resolve eq2038 eq144570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144570
  have eq144938 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq144763
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq144763
    | exact resolve eq144763 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144763
  have eq144939 : x = (M.op x y) := by grind
  clear eq144938
  have eq144986 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq144939 eq21
    | exact resolve eq21 eq144939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq145090 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq144939 eq2001
    | exact resolve eq2001 eq144939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2001
  have eq145162 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq145090
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq145090
    | exact resolve eq145090 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq145090
  have eq145224 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq144986
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq144986
    | exact resolve eq144986 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144986
  have eq145230 : x = (M.op y y) := by
    first
    | exact superpose eq144939 eq145162
    | exact resolve eq145162 eq144939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145162
  have eq145293 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq145224 eq27
    | exact resolve eq27 eq145224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq145763 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq39202
       have i₂ := eq145230
       grind)
    | exact superpose eq145230 eq39202
    | exact resolve eq39202 eq145230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39202
  have eq145900 : x ≠ y ∨ x = (k y y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq145230
       grind)
    | exact superpose eq145230 eq13
    | exact resolve eq13 eq145230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145230
  have eq146101 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq145763
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq145763
    | exact resolve eq145763 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145763
  have eq146139 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq145224 eq146101
    | exact resolve eq146101 eq145224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146101
  have eq146541 : (k (σ x) (σ (M.op x y))) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x (M.op x y)) := by
    first
    | exact superpose eq144939 eq84
    | exact resolve eq84 eq144939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq146542 : (σ (M.op x x)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x (M.op x y)) := by
    first
    | exact superpose eq145224 eq146541
    | exact resolve eq146541 eq145224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146541
  have eq146543 : (σ (M.op x x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x (M.op x y)) := by
    first
    | exact superpose eq8794 eq146542
    | exact resolve eq146542 eq8794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8794 eq146542
  have eq146544 : x = (M.op x x) ∨ (σ (M.op x x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x (M.op x y)) := by
    first
    | exact superpose eq144939 eq146543
    | exact resolve eq146543 eq144939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146543
  have eq146545 : x = (M.op x x) ∨ x = (M.op x x) ∨ (σ (M.op x x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq144939 eq146544
    | exact resolve eq146544 eq144939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146544
  have eq146546 : (σ (M.op x x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by grind
  clear eq146545
  have eq146803 : (M.op x x) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq146546
       grind)
    | exact superpose eq146546 eq16
    | exact resolve eq16 eq146546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146546
  have eq146909 : (M.op x x) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq8831 eq146803
    | exact resolve eq146803 eq8831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8831 eq146803
  have eq146930 : (k x x) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq144939 eq146909
    | exact resolve eq146909 eq144939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146909
  have eq146951 : (k x x) = (M.op x x) := by
    first
    | (have j1 := eq13 x x
       grind)
    | (have r₁ := eq146930
       have r₂ := eq13 x x
       grind)
    | exact resolve eq146930 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146930
  have eq146963 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq146951
       grind)
    | exact superpose eq146951 eq44
    | exact resolve eq44 eq146951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq147030 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | exact superpose eq8280 eq146963
    | exact resolve eq146963 eq8280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8280 eq146963
  have eq147054 : (σ (M.op x x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq145224 eq147030
    | exact resolve eq147030 eq145224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147030
  have eq153677 : (τ (σ (M.op x y))) = (k y y) ∨ x = y := by
    first
    | exact superpose eq146139 eq8491
    | exact resolve eq8491 eq146139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8491
  have eq153832 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq146139 eq2038
    | exact resolve eq2038 eq146139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2038 eq146139
  have eq154027 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq145293 eq153832
    | exact resolve eq153832 eq145293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153832
  have eq154073 : (M.op x y) = (k y y) ∨ x = y := by
    first
    | exact superpose eq31 eq153677
    | exact resolve eq153677 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq153677
  have eq154104 : x = y := by
    first
    | (have r₁ := eq154027
       have r₂ := eq28
       grind)
    | exact resolve eq154027 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154027
  have eq154134 : x = (k y y) ∨ x = y := by
    first
    | exact superpose eq144939 eq154073
    | exact resolve eq154073 eq144939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144939 eq154073
  have eq154165 : x = (k y y) := by
    first
    | (have r₁ := eq154134
       have r₂ := eq145900
       grind)
    | exact resolve eq154134 eq145900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145900 eq154134
  have eq154193 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq154104
       grind)
    | exact superpose eq154104 eq25
    | exact resolve eq25 eq154104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq154609 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq154193
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq154193
    | exact resolve eq154193 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154193
  have eq154694 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq145224 eq154609
    | exact resolve eq154609 eq145224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154609
  have eq155337 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq154694 eq145293
    | exact resolve eq145293 eq154694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145293 eq154694
  have eq155633 : x = (k x x) := by
    first
    | (have i₁ := eq154165
       have i₂ := eq154104
       grind)
    | exact superpose eq154104 eq154165
    | exact resolve eq154165 eq154104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154104 eq154165
  have eq155634 : x = (M.op x x) := by
    first
    | (have i₁ := eq155633
       have i₂ := eq146951
       grind)
    | exact superpose eq146951 eq155633
    | exact resolve eq155633 eq146951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146951 eq155633
  have eq155641 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq147054
       have i₂ := eq155634
       grind)
    | exact superpose eq155634 eq147054
    | exact resolve eq147054 eq155634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147054 eq155634
  have eq155971 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq155641
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq155641
    | exact resolve eq155641 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq155641
  have eq156042 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq145224 eq155971
    | exact resolve eq155971 eq145224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145224 eq155971
  have eq156686 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq156042 eq155337
    | exact resolve eq155337 eq156042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155337 eq156042
  have eq156687 : False := by grind
  exact eq156687

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,X) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyx_y_pxx_x_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b a ≠ b ∨ k a b = a :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
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
  have eq50 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
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
  have eq51 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
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
  have eq53 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
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
  have eq65 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (M.op X1 X1) = (k X1 (M.op (M.op X2 X1) (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 (M.op (M.op X2 X1) (M.op X0 X0))
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 (M.op (M.op X2 X1) (M.op X0 X0))
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op X2 X0) (M.op X0 X0))
       have r₂ := eq14 X0 X0 X2
       grind)
    | exact resolve eq13 eq14
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
  have eq76 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq16
    | exact resolve eq16 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq16
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq95 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq11 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
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
  have eq102 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
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
  have eq109 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq102
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
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
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq113
    | exact resolve eq113 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
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
  have eq186 : (σ (k (k y y) y)) = (k (k (σ y) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq40 (k y y)
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq40
    | exact resolve eq40 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq293 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq428 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq293 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq293
    | exact resolve eq293 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq443 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq293 X0 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq293
    | (have j0 := eq293 X0 x
       grind)
    | exact resolve eq293 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293
  have eq479 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 X0 X0
       have i₂ := eq53 X0 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq483 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op X1 X0)
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq51
    | exact resolve eq51 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq654 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq52 X3 x (M.op (M.op x x) (M.op X0 X0)) X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq687 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq53 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
       have i₂ := eq52 X0 x x X3
       grind)
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq769 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (M.op (M.op X1 X0) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq65 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq893 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq93 X0 X1
       grind)
    | exact superpose eq93 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq93 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq93 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq93 X0 X1
       grind)
    | exact resolve eq13 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq921 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq893 X0 X1
       have j1 := eq13 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq893 X0 X1
       have r₂ := eq13 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq893 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq893 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq893
  have eq931 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq921 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq921
    | (have j0 := eq921 X0 X1
       grind)
    | exact resolve eq921 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921
  have eq1585 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq50 (M.op X0 (M.op X0 X0))
       have i₂ := eq654 X0 X0 X0
       grind)
    | exact superpose eq654 eq50
    | exact resolve eq50 eq654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1586 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq51 (M.op X0 (M.op X0 X0))
       have i₂ := eq654 X0 X0 X0
       grind)
    | exact superpose eq654 eq51
    | exact resolve eq51 eq654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1597 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq687 (M.op x (M.op x x)) x
       have i₂ := eq654 x x x
       grind)
    | exact superpose eq654 eq687
    | exact resolve eq687 eq654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1751 : ∀ X0 : G, (M.op X0 (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq479 X0
       have i₂ := eq1585 X0
       grind)
    | exact superpose eq1585 eq479
    | exact resolve eq479 eq1585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1779 : (M.op (M.op x y) y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op y (M.op y y)))) := by
    first
    | exact superpose eq1585 eq483
    | exact resolve eq483 eq1585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1791 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq483 eq1779
    | exact resolve eq1779 eq483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1779
  have eq1826 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | exact superpose eq50 eq1751
    | exact resolve eq1751 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq1751
  have eq1985 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ y) (σ y))))) := by
    first
    | exact superpose eq1586 eq483
    | exact resolve eq483 eq1586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1586
  have eq1997 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq483 eq1985
    | exact resolve eq1985 eq483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483 eq1985
  have eq2399 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = (k (M.op X0 (M.op X0 X0)) (M.op X0 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq769 (M.op X0 (M.op X0 X0)) X0
       have i₂ := eq479 X0
       grind)
    | exact superpose eq479 eq769
    | exact resolve eq769 eq479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479 eq769
  have eq2522 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) = (k (M.op X0 (M.op X0 X0)) (M.op X0 (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq2399 X0
       have i₂ := eq53 X0 (M.op X0 X0)
       grind)
    | exact superpose eq53 eq2399
    | exact resolve eq2399 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2399
  have eq2542 : ∀ X0 : G, (k (M.op X0 (M.op X0 X0)) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq2522 X0
       have i₂ := eq1597 X0 X0
       grind)
    | exact superpose eq1597 eq2522
    | exact resolve eq2522 eq1597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1597 eq2522
  have eq2571 : ∀ X0 : G, (k (M.op y (M.op (M.op x y) X0)) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq2542 X0
       have i₂ := eq1585 X0
       grind)
    | exact superpose eq1585 eq2542
    | exact resolve eq2542 eq1585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2575 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op (M.op X0 (M.op X0 X0)) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq2542 (M.op x (M.op x x))
       have i₂ := eq654 x x x
       grind)
    | exact superpose eq654 eq2542
    | exact resolve eq2542 eq654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2542
  have eq2590 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq2575 X0
       have i₂ := eq687 X0 X0
       grind)
    | exact superpose eq687 eq2575
    | exact resolve eq2575 eq687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2575
  have eq6584 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq95 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq95
    | (have j0 := eq95 y
       grind)
    | exact resolve eq95 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq6611 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq6584
  have eq6618 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq6611
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq6611
    | exact resolve eq6611 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq6611
  have eq6629 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq6618
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq6618 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6618
  have eq6636 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq6629 eq87
    | exact resolve eq87 eq6629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq11825 : (σ (k (k y y) y)) = (k (M.op (σ y) (σ y)) (σ y)) := by
    first
    | exact superpose eq6629 eq186
    | exact resolve eq186 eq6629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq11826 : (σ (k (k y y) y)) = (M.op (σ y) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq11825
       have i₂ := eq2590 sF3
       grind)
    | exact superpose eq2590 eq11825
    | exact resolve eq11825 eq2590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2590 eq11825
  have eq11827 : (σ (k (k y y) y)) = (M.op y (M.op (M.op x y) (σ y))) := by
    first
    | (have i₁ := eq11826
       have i₂ := eq1585 sF3
       grind)
    | exact superpose eq1585 eq11826
    | exact resolve eq11826 eq1585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11826
  have eq17320 : (σ (M.op y y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq6629 eq109
    | exact resolve eq109 eq6629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq6629
  have eq17458 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq115 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17459 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq17458
    | exact resolve eq17458 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17458
  have eq17466 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq17459
       have r₂ := eq27
       grind)
    | exact resolve eq17459 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17459
  have eq17468 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq17466
    | exact resolve eq17466 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17466
  have eq17471 : (σ y) ≠ (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq17468 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq17468
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq17468
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq17468
       grind)
    | exact resolve eq13 eq17468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17474 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq17468 eq53
    | exact resolve eq53 eq17468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17468
  have eq17505 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq17471
  have eq17516 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq17474
    | exact resolve eq17474 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17474
  have eq22120 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq17505 eq115
    | exact resolve eq115 eq17505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq17505
  have eq22129 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq22120
  have eq22135 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22129 eq17516
    | exact resolve eq17516 eq22129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17516 eq22129
  have eq22212 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq22135
  have eq22224 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq22212
       have r₂ := eq27
       grind)
    | exact resolve eq22212 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22212
  have eq22334 : y ≠ y ∨ (k y x) = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq22224
       grind)
    | exact superpose eq22224 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq22224
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq22224
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq22224
       grind)
    | exact resolve eq13 eq22224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22337 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq53 y x
       have i₂ := eq22224
       grind)
    | exact superpose eq22224 eq53
    | exact resolve eq53 eq22224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22224
  have eq22368 : (k y x) = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq22334
  have eq22381 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq22337
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq22337
    | exact resolve eq22337 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22337
  have eq22491 : (k (σ y) (σ x)) = (σ (M.op y y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq22368
       grind)
    | exact superpose eq22368 eq72
    | exact resolve eq72 eq22368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq22368
  have eq23295 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq22491
       have i₂ := eq22381
       grind)
    | exact superpose eq22381 eq22491
    | exact resolve eq22491 eq22381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22381 eq22491
  have eq23347 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq23295
  have eq23354 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq23347
    | exact resolve eq23347 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23347
  have eq23368 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23354 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq23354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23371 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq23368
    | exact resolve eq23368 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23368
  have eq23378 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq23371
       have r₂ := eq27
       grind)
    | exact resolve eq23371 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23371
  have eq23380 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq23378
    | exact resolve eq23378 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23378
  have eq23381 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq23380
  have eq23559 : (σ y) ≠ (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23381 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq23381
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq23381
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq23381
       grind)
    | exact resolve eq13 eq23381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23562 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23381 eq53
    | exact resolve eq53 eq23381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23381
  have eq23593 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq23559
  have eq23604 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq23562
    | exact resolve eq23562 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23562
  have eq23782 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23593 eq23354
    | exact resolve eq23354 eq23593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23354 eq23593
  have eq23789 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq23782
  have eq23801 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23789 eq23604
    | exact resolve eq23604 eq23789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23604 eq23789
  have eq23876 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq23801
  have eq23889 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq23876
       have r₂ := eq27
       grind)
    | exact resolve eq23876 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23876
  have eq23895 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23889 eq27
    | exact resolve eq27 eq23889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23896 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (M.op X0 X0))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq23889 eq51
    | exact resolve eq51 eq23889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq23898 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23889 eq76
    | (have r₁ := eq76
       have r₂ := eq23889
       grind)
    | exact resolve eq76 eq23889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq23928 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23889 eq1997
    | exact resolve eq1997 eq23889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1997
  have eq23936 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq23898
  have eq23939 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq23928
    | exact resolve eq23928 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23928
  have eq23948 : (k y y) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23939 eq6636
    | exact resolve eq6636 eq23939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23986 : (σ y) = (k (M.op y (M.op (M.op x y) (σ y))) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23939 eq2571
    | exact resolve eq2571 eq23939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2571
  have eq24055 : (M.op y (M.op (M.op x y) (σ y))) = (σ (k (τ (M.op (σ x) (σ y))) y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11827
       have i₂ := eq23948
       grind)
    | exact superpose eq23948 eq11827
    | exact resolve eq11827 eq23948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11827
  have eq24084 : (M.op y (M.op (M.op x y) (σ y))) = (k (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24055
       have i₂ := eq34 sF4 y
       grind)
    | exact superpose eq34 eq24055
    | exact resolve eq24055 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq24055
  have eq24100 : (k (M.op (σ x) (σ y)) (σ y)) = (M.op y (M.op (M.op x y) (σ y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24084
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq24084
    | exact resolve eq24084 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24084
  have eq26278 : (σ y) = (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23939 eq23896
    | exact resolve eq23896 eq23939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23896 eq23939
  have eq26330 : (σ y) = (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by grind
  clear eq26278
  have eq26362 : (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23889 eq26330
    | exact resolve eq26330 eq23889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23889 eq26330
  have eq26401 : (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by grind
  clear eq26362
  have eq26645 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (M.op (σ y) (σ y))) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26401 eq654
    | exact resolve eq654 eq26401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654 eq26401
  have eq26697 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq26645 x
       have i₂ := eq687 sF3 x
       grind)
    | exact superpose eq687 eq26645
    | exact resolve eq26645 eq687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687 eq26645
  have eq26714 : (τ (σ x)) = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26697 eq6636
    | exact resolve eq6636 eq26697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26759 : (M.op (σ y) (σ x)) = (M.op y (M.op (M.op x y) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26697 eq1585
    | exact resolve eq1585 eq26697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1585
  have eq26832 : x = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq26714
    | exact resolve eq26714 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq26714
  have eq27397 : x = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq23948
       have i₂ := eq26832
       grind)
    | exact superpose eq26832 eq23948
    | exact resolve eq23948 eq26832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23948
  have eq27409 : x = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq26832
       grind)
    | exact superpose eq26832 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq26832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27410 : y = (M.op y y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq27409
  have eq27414 : x = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq27397
  have eq27483 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq27414 eq428
    | exact resolve eq428 eq27414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428 eq27414
  have eq27502 : ∀ X0 : G, (τ (k X0 (σ x))) = (τ (k X0 (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq27483 X0
       have i₂ := eq443 X0
       grind)
    | exact superpose eq443 eq27483
    | exact resolve eq27483 eq443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443 eq27483
  have eq31235 : (σ y) = (k (k (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24100 eq23986
    | exact resolve eq23986 eq24100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23986
  have eq31290 : (σ y) = (k (k (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq31235
  have eq35491 : (M.op (σ y) (σ x)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26759 eq24100
    | exact resolve eq24100 eq26759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24100 eq26759
  have eq35545 : (M.op (σ y) (σ x)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq35491
  have eq40741 : (τ (σ y)) = (τ (k (k (M.op (σ x) (σ y)) (σ y)) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31290 eq27502
    | exact resolve eq27502 eq31290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27502 eq31290
  have eq40831 : (τ (σ y)) = (τ (k (k (M.op (σ x) (σ y)) (σ y)) (σ x))) ∨ x = (M.op x y) := by grind
  clear eq40741
  have eq40888 : y = (τ (k (k (M.op (σ x) (σ y)) (σ y)) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq40831
    | exact resolve eq40831 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40831
  have eq40902 : y = (τ (k (M.op (σ y) (σ x)) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq35545 eq40888
    | exact resolve eq40888 eq35545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35545 eq40888
  have eq40963 : y = (τ (k (M.op (σ y) (σ x)) (σ x))) ∨ x = (M.op x y) := by grind
  clear eq40902
  have eq76606 : (τ (σ y)) = (k y x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23936 eq82
    | exact resolve eq82 eq23936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23936
  have eq76635 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq76606
    | exact resolve eq76606 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq76606
  have eq76670 : y = (τ (k (σ y) (σ x))) ∨ x = (M.op x y) ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq76635 eq40963
    | exact resolve eq40963 eq76635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40963 eq76635
  have eq76766 : y = (τ (k (σ y) (σ x))) ∨ x = (M.op x y) ∨ y = (k y x) := by grind
  clear eq76670
  have eq76828 : y = (k y x) ∨ x = (M.op x y) ∨ y = (k y x) := by
    first
    | exact superpose eq82 eq76766
    | exact resolve eq76766 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq76766
  have eq76829 : y = (k y x) ∨ x = (M.op x y) := by grind
  clear eq76828
  have eq77531 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq76829
       grind)
    | exact superpose eq76829 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq76829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76829
  have eq77536 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq77531
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq77531
    | exact resolve eq77531 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77531
  have eq77550 : x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq77536
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq77536
    | exact resolve eq77536 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77536
  have eq77551 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq77550
  have eq77608 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq53 y x
       have i₂ := eq77551
       grind)
    | exact superpose eq77551 eq53
    | exact resolve eq53 eq77551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq77551
  have eq77698 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq77608
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq77608
    | exact resolve eq77608 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77608
  have eq77860 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17320
       have i₂ := eq77698
       grind)
    | exact superpose eq77698 eq17320
    | exact resolve eq17320 eq77698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77698
  have eq77996 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq77860
  have eq78040 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq77996
    | exact resolve eq77996 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77996
  have eq78378 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq78040 eq26697
    | exact resolve eq26697 eq78040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26697 eq78040
  have eq78564 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq78378
  have eq78605 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq78564
       have r₂ := eq23895
       grind)
    | exact resolve eq78564 eq23895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23895 eq78564
  have eq78829 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq78605
  have eq1786116 : y ≠ y ∨ y = (k y y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq27410
       grind)
    | exact superpose eq27410 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq27410
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq27410
       grind)
    | exact resolve eq13 eq27410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27410
  have eq1786479 : y = (k y y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq1786116
  have eq1791841 : x = y ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq26832
       have i₂ := eq1786479
       grind)
    | exact superpose eq1786479 eq26832
    | exact resolve eq26832 eq1786479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26832 eq1786479
  have eq1792074 : x = y ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq1791841
  have eq1792218 : x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1792074
       have r₂ := eq78829
       grind)
    | exact resolve eq1792074 eq78829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78829 eq1792074
  have eq1792509 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1826 y
       have i₂ := eq1792218
       grind)
    | exact superpose eq1792218 eq1826
    | exact resolve eq1826 eq1792218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1792218
  have eq1793251 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1792509
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1792509
    | exact resolve eq1792509 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1792509
  have eq1793252 : x = (M.op x y) := by grind
  clear eq1793251
  have eq1795845 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1793252 eq20
    | exact resolve eq20 eq1793252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1795948 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq1793252 eq1791
    | exact resolve eq1791 eq1793252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1791
  have eq1796416 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq1795948
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1795948
    | exact resolve eq1795948 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1795948
  have eq1796471 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1795845
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1795845
    | exact resolve eq1795845 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1795845
  have eq1796481 : x = (M.op y y) := by
    first
    | exact superpose eq1793252 eq1796416
    | exact resolve eq1796416 eq1793252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1796416
  have eq1796497 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1796471 eq26
    | exact resolve eq26 eq1796471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1797761 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq17320
       have i₂ := eq1796481
       grind)
    | exact superpose eq1796481 eq17320
    | exact resolve eq17320 eq1796481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17320
  have eq1798028 : x ≠ y ∨ x = (k y y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq1796481
       grind)
    | exact superpose eq1796481 eq13
    | exact resolve eq13 eq1796481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1796481
  have eq1798815 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq1797761
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1797761
    | exact resolve eq1797761 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1797761
  have eq1798951 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1796471 eq1798815
    | exact resolve eq1798815 eq1796471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1798815
  have eq1871778 : (τ (σ (M.op x y))) = (k y y) ∨ x = y := by
    first
    | exact superpose eq1798951 eq6636
    | exact resolve eq6636 eq1798951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6636
  have eq1871960 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1798951 eq1826
    | exact resolve eq1826 eq1798951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1826 eq1798951
  have eq1872898 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1796497 eq1871960
    | exact resolve eq1871960 eq1796497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1871960
  have eq1872937 : (M.op x y) = (k y y) ∨ x = y := by
    first
    | exact superpose eq30 eq1871778
    | exact resolve eq1871778 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1871778
  have eq1873048 : x = y := by
    first
    | (have r₁ := eq1872898
       have r₂ := eq27
       grind)
    | exact resolve eq1872898 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1872898
  have eq1873072 : x = (k y y) ∨ x = y := by
    first
    | exact superpose eq1793252 eq1872937
    | exact resolve eq1872937 eq1793252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1793252 eq1872937
  have eq1873144 : x = (k y y) := by
    first
    | (have r₁ := eq1873072
       have r₂ := eq1798028
       grind)
    | exact resolve eq1873072 eq1798028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1798028 eq1873072
  have eq1879402 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1873048
       grind)
    | exact superpose eq1873048 eq24
    | exact resolve eq24 eq1873048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq1880512 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1879402
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1879402
    | exact resolve eq1879402 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1879402
  have eq1880708 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1796471 eq1880512
    | exact resolve eq1880512 eq1796471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1880512
  have eq1882011 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1880708 eq1796497
    | exact resolve eq1796497 eq1880708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1796497 eq1880708
  have eq1882357 : x = (k x x) := by
    first
    | (have i₁ := eq1873144
       have i₂ := eq1873048
       grind)
    | exact superpose eq1873048 eq1873144
    | exact resolve eq1873144 eq1873048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1873048 eq1873144
  have eq1882511 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq931 x x
       have i₂ := eq1882357
       grind)
    | exact superpose eq1882357 eq931
    | (have j0 := eq931 x x
       grind)
    | exact resolve eq931 eq1882357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq931 eq1882357
  have eq1882578 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1882511
  have eq1882579 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1882578
  have eq1882609 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1882579
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1882579
    | exact resolve eq1882579 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1882579
  have eq1882759 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1796471 eq1882609
    | exact resolve eq1882609 eq1796471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1796471 eq1882609
  have eq1895972 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1882759 eq1882011
    | exact resolve eq1882011 eq1882759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1882011 eq1882759
  have eq1895973 : False := by grind
  exact eq1895973

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxx_pyx_pyx_pxx_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
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
    | (have r₁ := eq22 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq22 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq27 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
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
  have eq28 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
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
  have eq37 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq38 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq39 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq27 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq42 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq38 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq38 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq46 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq28 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq28 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq28 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq47 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq39 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq39 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq39 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq50 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq46 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq46
    | (have j0 := eq46 X0 X1
       grind)
    | exact resolve eq46 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq51 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq47 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq47
    | (have j0 := eq47 X0 X1
       grind)
    | exact resolve eq47 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq47
  have eq53 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       have j1 := eq50 X0 X1
       grind)
    | (have r₁ := eq51 X0 X1
       have r₂ := eq50 X0 X1
       grind)
    | exact resolve eq51 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq51
  have eq116 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq120 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq116 X0 X1
       have j1 := eq53 X1 X0
       grind)
    | (have r₁ := eq116 X1 X1
       have r₂ := eq53 X1 X1
       grind)
    | (have r₁ := eq116 X1 X0
       have r₂ := eq53 X0 X1
       grind)
    | exact resolve eq116 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq116
  have eq261 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq120 (σ X1) (σ X0)
       grind)
    | exact superpose eq120 eq15
    | exact resolve eq15 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq268 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq261 X0 X1
       have i₂ := eq120 X1 X0
       grind)
    | exact superpose eq120 eq261
    | exact resolve eq261 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq261
  have eq270 : False := by grind
  exact eq270

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_x_pyx_x_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq75 : y ≠ (M.op x y) ∨ x = (M.op y x) ∨ y = (k y x) := by
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
  have eq76 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
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
  have eq97 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq93 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq93
    | (have j0 := eq93 (σ X0) (σ X1)
       grind)
    | exact resolve eq93 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq93 y x
       grind)
    | exact superpose eq93 eq72
    | (have j1 := eq93 y x
       grind)
    | exact resolve eq72 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
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
  have eq118 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq116
    | exact resolve eq116 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq119 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq118
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq118
    | exact resolve eq118 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq122 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq119 eq93
    | (have j0 := eq93 (σ y) (σ x)
       grind)
    | exact resolve eq93 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq123 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq122
    | exact resolve eq122 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq126 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq123
       have r₂ := eq27
       grind)
    | exact resolve eq123 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq128 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq126
    | exact resolve eq126 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq130 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq128 eq27
    | exact resolve eq27 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  clear eq37
  have eq149 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq138 eq16
    | exact resolve eq16 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq462 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq128 eq76
    | (have r₁ := eq76
       have r₂ := eq128
       grind)
    | exact resolve eq76 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq128
  have eq463 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq462
  have eq466 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq463 eq119
    | exact resolve eq119 eq463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463
  have eq470 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq466
  have eq475 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq470
       have r₂ := eq130
       grind)
    | exact resolve eq470 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq470
  have eq480 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq475 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq475
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq475
       grind)
    | exact resolve eq13 eq475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475
  have eq482 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq480
  have eq485 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq482
    | exact resolve eq482 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482
  have eq581 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq485 eq119
    | exact resolve eq119 eq485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq485
  have eq584 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq581
  have eq588 : y = (M.op x y) := by
    first
    | (have r₁ := eq584
       have r₂ := eq27
       grind)
    | exact resolve eq584 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584
  have eq590 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq588 eq20
    | exact resolve eq20 eq588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq595 : y ≠ y ∨ x = (M.op y x) ∨ y = (k y x) := by
    first
    | exact superpose eq588 eq75
    | (have r₁ := eq75
       have r₂ := eq588
       grind)
    | exact resolve eq75 eq588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq599 : x = (M.op y x) ∨ y = (k y x) := by grind
  clear eq595
  have eq606 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq590
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq590
    | exact resolve eq590 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590
  have eq636 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq97
    | (have j0 := eq97 (M.op x y) X0
       grind)
    | exact resolve eq97 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq97
  have eq657 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq588 eq636
    | (have j0 := eq636 X0
       grind)
    | exact resolve eq636 eq588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636
  have eq673 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq606 eq26
    | exact resolve eq26 eq606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq875 : (σ (k y x)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq657 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq657
    | (have j0 := eq657 x
       grind)
    | exact resolve eq657 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq657
  have eq890 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq673 eq875
    | exact resolve eq875 eq673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq875
  have eq904 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq890
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq890
    | exact resolve eq890 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq890
  have eq915 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq606 eq904
    | exact resolve eq904 eq606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq904
  have eq921 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq673 eq915
    | exact resolve eq915 eq673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673 eq915
  have eq922 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have r₁ := eq921
       have r₂ := eq27
       grind)
    | exact resolve eq921 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921
  have eq924 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) x) := by
    first
    | exact superpose eq922 eq149
    | exact resolve eq149 eq922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149 eq922
  have eq926 : (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq588 eq924
    | exact resolve eq924 eq588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq924
  have eq1099 : x = (M.op y x) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq599
       have i₂ := eq926
       grind)
    | exact superpose eq926 eq599
    | exact resolve eq599 eq926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599
  have eq1102 : x ≠ x ∨ (M.op x y) = (k y x) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq1099
       grind)
    | exact superpose eq1099 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1099
       grind)
    | exact resolve eq13 eq1099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1099
  have eq1107 : (M.op x y) = (k y x) ∨ y = (τ (M.op (σ x) (σ y))) := by grind
  clear eq1102
  have eq1109 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1107
       have i₂ := eq926
       grind)
    | exact superpose eq926 eq1107
    | exact resolve eq1107 eq926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq926 eq1107
  have eq1112 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1109
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1109
    | exact resolve eq1109 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1109
  have eq1113 : y = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq588 eq1112
    | exact resolve eq1112 eq588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588 eq1112
  have eq1114 : y = (τ (M.op (σ x) (σ y))) := by grind
  clear eq1113
  have eq1118 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1114 eq15
    | exact resolve eq15 eq1114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1114
  have eq1119 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1118
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1118
    | exact resolve eq1118 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1118
  have eq1120 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq606 eq1119
    | exact resolve eq1119 eq606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606 eq1119
  have eq1121 : False := by grind
  exact eq1121

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,X) else if m(X,X) = m(X,Y) then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxx_pxy_pxx_y_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a ≠ M.op a b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
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
  have eq50 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
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
  have eq51 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
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
  have eq53 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
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
  have eq64 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq66 sF2
       grind)
    | exact superpose eq66 eq49
    | exact resolve eq49 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq71 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq70
       have i₂ := eq66 x
       grind)
    | exact superpose eq66 eq70
    | exact resolve eq70 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq70
  have eq101 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq110 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq101
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq101
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq101 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq110
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq110
    | exact resolve eq110 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq116
    | exact resolve eq116 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq118 : (M.op y y) = (M.op y x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
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
  have eq237 : (M.op (M.op x y) (M.op x y)) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq50 (M.op sF0 sF0)
       have i₂ := eq14 sF0 sF0 sF0
       grind)
    | exact superpose eq14 eq50
    | exact resolve eq50 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq251 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq51 (M.op sF4 sF4)
       have i₂ := eq14 sF4 sF4 sF4
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq254 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq261 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (M.op X1 X0) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq251 eq14
    | exact resolve eq14 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq523 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op x y) (M.op X0 X0)) X0) := by
    intro X0
    first
    | exact superpose eq50 eq53
    | exact resolve eq53 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq532 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 X0 X0
       have i₂ := eq53 X0 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq536 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op y (M.op (M.op x y) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq50 (M.op X1 X0)
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq50
    | exact resolve eq50 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq539 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 X0) X2 X3
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq573 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq52 X3 x (M.op (M.op x x) (M.op X0 X0)) X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq596 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 X4 X2 X3 (M.op X1 X0)
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq597 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 X4 X2 X3 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq52 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq606 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq53 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
       have i₂ := eq52 X0 x x X3
       grind)
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq612 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) X2 X3
       have i₂ := eq52 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq613 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq50 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq52 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq52 eq50
    | exact resolve eq50 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq618 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq613 X0 X1
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq613
    | exact resolve eq613 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613
  have eq619 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq612 X0 X1 X2 X3
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq612
    | exact resolve eq612 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612
  have eq628 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq597 X0 X1 X2 X3 X4
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq597
    | exact resolve eq597 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597
  have eq1564 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq251 eq254
    | exact resolve eq254 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1603 : (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq254 eq50
    | exact resolve eq50 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1604 : (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq254 eq51
    | exact resolve eq51 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq1631 : (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq251 eq1604
    | exact resolve eq1604 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1604
  have eq1632 : (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq251 eq1603
    | exact resolve eq1603 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1603
  have eq2005 : (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) = (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1631 eq1632
    | exact resolve eq1632 eq1631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1632
  have eq2007 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op (M.op X0 (M.op X0 X0)) (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq573 X1 (M.op X0 (M.op X0 X0)) X2
       have i₂ := eq573 X0 X0 X0
       grind)
    | exact superpose eq573 eq573
    | exact resolve eq573 eq573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2010 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq254 eq573
    | exact resolve eq573 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254
  have eq2028 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq573 X1 X2 (M.op X0 (M.op X0 X0))
       have i₂ := eq573 X0 X0 X0
       grind)
    | exact superpose eq573 eq573
    | exact resolve eq573 eq573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2060 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq573 X0 X0 X0
       grind)
    | exact superpose eq573 eq14
    | exact resolve eq14 eq573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2061 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq50 (M.op X0 (M.op X0 X0))
       have i₂ := eq573 X0 X0 X0
       grind)
    | exact superpose eq573 eq50
    | exact resolve eq50 eq573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2069 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq523 (M.op x (M.op x x))
       have i₂ := eq573 x x x
       grind)
    | exact superpose eq573 eq523
    | exact resolve eq523 eq573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523
  have eq2072 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq606 (M.op x (M.op x x)) x
       have i₂ := eq573 x x x
       grind)
    | exact superpose eq573 eq606
    | exact resolve eq606 eq573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606
  have eq2111 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq251 eq2010
    | exact resolve eq2010 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2010
  have eq2128 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq1631 eq2111
    | exact resolve eq2111 eq1631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2111
  have eq2292 : ∀ X0 : G, (M.op X0 (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq532 X0
       have i₂ := eq2061 X0
       grind)
    | exact superpose eq2061 eq532
    | exact resolve eq532 eq2061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2368 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | exact superpose eq50 eq2292
    | exact resolve eq2292 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq2292
  have eq2601 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) = (M.op X0 (M.op (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) (M.op (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) (M.op (M.op X1 (M.op x y)) (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq2069 (M.op (M.op x sF0) (M.op X0 X0))
       have i₂ := eq14 X0 sF0 x
       grind)
    | exact superpose eq14 eq2069
    | exact resolve eq2069 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2069
  have eq2648 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) = (M.op X0 (M.op y (M.op (M.op x y) (M.op (M.op X1 (M.op x y)) (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq2601 X0 X1
       have i₂ := eq2061 (M.op (M.op X1 sF0) (M.op X0 X0))
       grind)
    | exact superpose eq2061 eq2601
    | exact resolve eq2601 eq2061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2601
  have eq2665 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) = (M.op X0 (M.op y X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2648 X0 x
       have i₂ := eq14 X0 sF0 x
       grind)
    | exact superpose eq14 eq2648
    | exact resolve eq2648 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2648
  have eq2790 : y = (M.op (M.op x y) (M.op y (M.op y y))) := by
    first
    | (have i₁ := eq2072 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2072
    | (have j0 := eq2072 y x
       grind)
    | exact resolve eq2072 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2804 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq26 eq2072
    | (have j0 := eq2072 (σ y) (σ x)
       grind)
    | exact resolve eq2072 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2833 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2072 X0 X1
       have i₂ := eq2061 X0
       grind)
    | exact superpose eq2061 eq2072
    | exact resolve eq2072 eq2061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2871 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op y (M.op (M.op x y) (σ y)))) := by
    first
    | (have i₁ := eq2804
       have i₂ := eq2061 sF3
       grind)
    | exact superpose eq2061 eq2804
    | exact resolve eq2804 eq2061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2804
  have eq5426 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op y (M.op (M.op x y) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq539 X1 X0 X1 X0
       have i₂ := eq618 X0 X1
       grind)
    | exact superpose eq618 eq539
    | exact resolve eq539 eq618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539
  have eq5435 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op X0 X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq536 (M.op X0 X1) X1
       have i₂ := eq618 X0 X1
       grind)
    | exact superpose eq618 eq536
    | exact resolve eq536 eq618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6427 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq619 X0 X1 X2 X3
       have i₂ := eq618 X0 X1
       grind)
    | exact superpose eq618 eq619
    | exact resolve eq619 eq618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619
  have eq6429 : ∀ X0 X1 X2 : G, (M.op y (M.op (M.op x y) (M.op X1 X2))) = (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6427 X1 X2 (M.op X0 (M.op X0 X0)) X0
       have i₂ := eq532 X0
       grind)
    | exact superpose eq532 eq6427
    | exact resolve eq6427 eq532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6604 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X1 (M.op X0 X0)))) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq6427 X1 (M.op X0 X0) (M.op X1 X1) x
       have i₂ := eq573 x X1 X0
       grind)
    | exact superpose eq573 eq6427
    | exact resolve eq6427 eq573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573
  have eq6629 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op y (M.op (M.op x y) (M.op (M.op X3 (M.op X2 X1)) (M.op X0 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6427 (M.op X3 (M.op X2 X1)) (M.op X0 X0) X1 X2
       have i₂ := eq14 X0 (M.op X2 X1) X3
       grind)
    | exact superpose eq14 eq6427
    | exact resolve eq6427 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6684 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X2 (M.op y (M.op (M.op x y) (M.op X0 (M.op X1 X2))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 (M.op X1 X2)) X2 X1
       have i₂ := eq6427 X0 (M.op X1 X2) (M.op X1 X2) X0
       grind)
    | exact superpose eq6427 eq14
    | exact resolve eq14 eq6427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6427
  have eq7151 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq628 X0 X1 X2 X3 X4
       have i₂ := eq618 X0 X1
       grind)
    | exact superpose eq618 eq628
    | exact resolve eq628 eq618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618 eq628
  have eq7346 : ∀ X0 X1 X2 X3 : G, (M.op y (M.op (M.op x y) X0)) = (M.op (M.op (M.op X1 X2) (M.op X3 X3)) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq7151 X0 (M.op X0 (M.op X0 X0)) X2 X3 x
       have i₂ := eq532 X0
       grind)
    | exact superpose eq532 eq7151
    | exact resolve eq7151 eq532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7151
  have eq29509 : ∀ X0 : G, (M.op (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq1631 eq1564
    | exact resolve eq1564 eq1631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1564
  have eq29510 : ∀ X0 : G, (M.op (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq2005 eq29509
    | exact resolve eq29509 eq2005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29509
  have eq30926 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq596 X0 (M.op X1 X0) X2 X3 X4
       have i₂ := eq2060 X0 X0 X1
       grind)
    | exact superpose eq2060 eq596
    | exact resolve eq596 eq2060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2060
  have eq31027 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq30926 X0 X1 x x x
       have i₂ := eq596 X0 X0 x x x
       grind)
    | exact superpose eq596 eq30926
    | exact resolve eq30926 eq596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596 eq30926
  have eq45332 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op y (M.op y y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq2007 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2007
    | (have j0 := eq2007 y x X0
       grind)
    | exact resolve eq2007 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2007
  have eq46173 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op y X0))) = X0 := by
    intro X0
    first
    | exact superpose eq2665 eq14
    | exact resolve eq14 eq2665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2665
  have eq47420 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 (M.op (M.op X2 X0) (M.op X2 X0))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2028 (M.op X0 (M.op X0 X0)) X1 (M.op X2 X0)
       have i₂ := eq2072 X0 X2
       grind)
    | exact superpose eq2072 eq2028
    | exact resolve eq2028 eq2072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2072
  have eq47516 : ∀ X0 : G, (M.op y (M.op y y)) = (M.op (M.op X0 (M.op x x)) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq2028 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2028
    | (have j0 := eq2028 y X0 x
       grind)
    | exact resolve eq2028 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47544 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) (σ y))) = (M.op (M.op X0 (M.op (σ x) (σ x))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq2028
    | (have j0 := eq2028 (σ y) X0 (σ x)
       grind)
    | exact resolve eq2028 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47592 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 (M.op X1 X1)) (M.op X1 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq532 X2
       have i₂ := eq2028 X2 X0 X1
       grind)
    | exact superpose eq2028 eq532
    | exact resolve eq532 eq2028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532
  have eq48137 : ∀ X0 : G, (M.op y (M.op (M.op x y) (σ y))) = (M.op (M.op X0 (M.op (σ x) (σ x))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq47544 X0
       have i₂ := eq2061 sF3
       grind)
    | exact superpose eq2061 eq47544
    | exact resolve eq47544 eq2061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47544
  have eq48260 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 (M.op X0 (M.op X2 X0))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq47420 X0 X1 X2
       have i₂ := eq53 X2 X0
       grind)
    | exact superpose eq53 eq47420
    | exact resolve eq47420 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47420
  have eq48540 : ∀ X0 X1 X2 : G, (M.op y (M.op (M.op x y) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 (M.op X0 (M.op X2 X0))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq48260 X0 X1 X2
       have i₂ := eq2061 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq2061 eq48260
    | exact resolve eq48260 eq2061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2061 eq48260
  have eq48654 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 (M.op X2 X0))) X0) := by
    intro X0 X1 X2
    first
    | exact superpose eq536 eq48540
    | exact resolve eq48540 eq536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536 eq48540
  have eq51379 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq2005 eq2128
    | exact resolve eq2128 eq2005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2128
  have eq74150 : y = (M.op (M.op x y) (M.op (M.op y (M.op y x)) (M.op y x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq45332 y
       have i₂ := eq118
       grind)
    | exact superpose eq118 eq45332
    | exact resolve eq45332 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq45332
  have eq74318 : y = (M.op (M.op x y) (M.op (M.op y x) (M.op y x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq74150
       have i₂ := eq31027 (M.op y x) y
       grind)
    | exact superpose eq31027 eq74150
    | exact resolve eq74150 eq31027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31027 eq74150
  have eq74356 : y = (M.op (M.op x y) (M.op x (M.op y x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq74318
       have i₂ := eq53 y x
       grind)
    | exact superpose eq53 eq74318
    | exact resolve eq74318 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74318
  have eq74379 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq46173 eq74356
    | exact resolve eq74356 eq46173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46173 eq74356
  have eq77468 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (M.op X0 (M.op (σ x) (σ x))) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq47592
    | (have j0 := eq47592 X0 (σ x) (σ y)
       grind)
    | exact resolve eq47592 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47592
  have eq98392 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) X2) = (M.op y (M.op (M.op x y) (M.op (M.op X3 (M.op X0 (M.op X0 X0))) (M.op X2 X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6629 X2 (M.op X1 X0) (M.op x (M.op X1 X1)) X3
       have i₂ := eq2028 X0 x X1
       grind)
    | exact superpose eq2028 eq6629
    | exact resolve eq6629 eq2028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2028
  have eq98795 : ∀ X0 X1 X2 : G, (M.op (M.op y (M.op (M.op x y) (M.op X1 X0))) X2) = (M.op y (M.op (M.op x y) (M.op (M.op X0 (M.op X1 X0)) (M.op X2 X2)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq5435 eq6629
    | exact resolve eq6629 eq5435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5435
  have eq98819 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op y (M.op (M.op x y) (M.op (σ y) (M.op X0 X0)))) := by
    intro X0
    first
    | exact superpose eq77468 eq6629
    | exact resolve eq6629 eq77468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77468
  have eq99161 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (σ y) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq6604 eq98819
    | exact resolve eq98819 eq6604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98819
  have eq99171 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op y (M.op (M.op x y) (M.op X1 X0))) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq6629 eq98795
    | exact resolve eq98795 eq6629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98795
  have eq99278 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op (M.op X0 X0) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq6629 eq98392
    | exact resolve eq98392 eq6629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98392
  have eq100360 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))))) := by
    intro X0
    first
    | exact superpose eq99161 eq51379
    | exact resolve eq51379 eq99161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51379 eq99161
  have eq100709 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | exact superpose eq29510 eq100360
    | exact resolve eq100360 eq29510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29510 eq100360
  have eq110609 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X1 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | exact superpose eq6604 eq6684
    | exact resolve eq6684 eq6604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6604
  have eq110635 : ∀ X0 X1 X2 X3 : G, (M.op y (M.op (M.op x y) (M.op (M.op X0 (M.op X1 X2)) (M.op X3 X3)))) = (M.op (M.op (M.op x y) (M.op X0 (M.op X1 X2))) X3) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq6684 eq6629
    | exact resolve eq6629 eq6684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6684
  have eq110853 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op (M.op x y) (M.op X0 (M.op X1 X2))) X3) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq6629 eq110635
    | exact resolve eq110635 eq6629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110635
  have eq114333 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) X2) = (M.op y (M.op (M.op x y) (M.op (M.op X3 (M.op y (M.op (M.op x y) X0))) (M.op X2 X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6629 X2 (M.op X1 X0) (M.op (M.op x x) (M.op X1 X1)) X3
       have i₂ := eq7346 X0 x x X1
       grind)
    | exact superpose eq7346 eq6629
    | exact resolve eq6629 eq7346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7346
  have eq114366 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op (M.op (M.op x y) X0) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq6629 eq114333
    | exact resolve eq114333 eq6629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6629 eq114333
  have eq168365 : (M.op (M.op x y) (M.op y (M.op y y))) = (M.op (M.op x x) (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq47516 eq110609
    | exact resolve eq110609 eq47516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47516
  have eq168373 : (M.op (M.op (σ x) (σ y)) (M.op y (M.op (M.op x y) (σ y)))) = (M.op (M.op (σ x) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq48137 eq110609
    | exact resolve eq110609 eq48137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48137
  have eq169134 : (M.op (M.op (σ x) (σ y)) (M.op y (M.op (M.op x y) (σ y)))) = (M.op (M.op (M.op x y) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq168373
       have i₂ := eq114366 sF2 sF2 (M.op sF4 sF4)
       grind)
    | exact superpose eq114366 eq168373
    | exact resolve eq168373 eq114366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168373
  have eq169141 : (M.op (M.op x y) (M.op y (M.op y y))) = (M.op (M.op x x) (M.op y (M.op x y))) := by
    first
    | exact superpose eq237 eq168365
    | exact resolve eq168365 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237 eq168365
  have eq169475 : (M.op (M.op (σ x) (σ y)) (M.op y (M.op (M.op x y) (σ y)))) = (M.op (M.op (M.op x y) (σ x)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq251 eq169134
    | exact resolve eq169134 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251 eq169134
  have eq169479 : y = (M.op (M.op x x) (M.op y (M.op x y))) := by
    first
    | exact superpose eq2790 eq169141
    | exact resolve eq169141 eq2790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2790 eq169141
  have eq169659 : (σ y) = (M.op (M.op (M.op x y) (σ x)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq2871 eq169475
    | exact resolve eq169475 eq2871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2871 eq169475
  have eq169806 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op y (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq169479
       have i₂ := eq99278 x x (M.op y sF0)
       grind)
    | (have i₁ := eq169479
       have i₂ := eq99278 x x (M.op y sF0)
       grind)
    | exact superpose eq99278 eq169479
    | exact resolve eq169479 eq99278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99278 eq169479
  have eq170053 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq169659
       have i₂ := eq114366 sF2 sF0 (M.op sF3 sF4)
       grind)
    | exact superpose eq114366 eq169659
    | exact resolve eq169659 eq114366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169659
  have eq171687 : (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) = (M.op (σ x) (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq170053 eq110609
    | exact resolve eq110609 eq170053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110609
  have eq171880 : (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq171687
       have i₂ := eq53 sF3 sF4
       grind)
    | exact superpose eq53 eq171687
    | exact resolve eq171687 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq171687
  have eq171936 : (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) = (M.op (σ x) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq1631 eq171880
    | exact resolve eq171880 eq1631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1631 eq171880
  have eq171964 : (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) = (M.op (σ x) (M.op y (M.op (M.op x y) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq2005 eq171936
    | exact resolve eq171936 eq2005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2005 eq171936
  have eq171975 : (M.op (M.op (M.op x y) (M.op (σ x) (σ y))) (σ y)) = (M.op (σ x) (M.op y (M.op (M.op x y) (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq171964
       have i₂ := eq114366 sF4 sF3 sF3
       grind)
    | exact superpose eq114366 eq171964
    | exact resolve eq171964 eq114366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114366 eq171964
  have eq171980 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op y (M.op (M.op x y) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq100709 eq171975
    | exact resolve eq171975 eq100709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100709 eq171975
  have eq264018 : ∀ X0 X1 X2 : G, (M.op (σ x) (σ y)) = (M.op (M.op X2 (M.op X0 X1)) (M.op (M.op y (M.op (M.op x y) (M.op X0 X1))) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq261 (M.op X2 (M.op X0 X1)) (M.op X2 (M.op X2 X2))
       have i₂ := eq6429 X2 X0 X1
       grind)
    | exact superpose eq6429 eq261
    | exact resolve eq261 eq6429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261 eq6429
  have eq264170 : ∀ X0 X1 X2 : G, (M.op (σ x) (σ y)) = (M.op (M.op X2 (M.op X0 X1)) (M.op X1 (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq99171 eq264018
    | exact resolve eq264018 eq99171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99171 eq264018
  have eq266429 : ∀ X0 X1 X2 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op X1 (M.op X2 (σ x)))) (σ y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq170053 eq264170
    | exact resolve eq264170 eq170053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170053 eq264170
  have eq288547 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq74379 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq74379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq288548 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq288547
    | exact resolve eq288547 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288547
  have eq288559 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq288548
       have r₂ := eq27
       grind)
    | exact resolve eq288548 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288548
  have eq288563 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq288559
    | exact resolve eq288559 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288559
  have eq288819 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (M.op X0 (M.op (σ y) (M.op (σ y) (σ x)))) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq288563 eq48654
    | exact resolve eq48654 eq288563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48654
  have eq288830 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op (M.op (M.op x y) (M.op X1 (M.op (σ y) (σ x)))) X0) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq288563 eq110853
    | exact resolve eq110853 eq288563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288563
  have eq288859 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) X0) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq110853 eq288830
    | exact resolve eq288830 eq110853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110853 eq288830
  have eq288868 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq266429 eq288819
    | exact resolve eq288819 eq266429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266429 eq288819
  have eq290708 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq288859 eq288868
    | exact resolve eq288868 eq288859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288859 eq288868
  have eq291342 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by grind
  clear eq290708
  have eq291898 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq291342 eq64
    | (have r₁ := eq64
       have r₂ := eq291342
       grind)
    | exact resolve eq64 eq291342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq292103 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op y (M.op (M.op x y) (M.op (σ x) (σ y))))) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq291342 eq5426
    | exact resolve eq5426 eq291342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5426 eq291342
  have eq292166 : (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by grind
  clear eq291898
  have eq292197 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq171980 eq292103
    | exact resolve eq292103 eq171980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171980 eq292103
  have eq295955 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq292166 eq74379
    | exact resolve eq74379 eq292166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74379 eq292166
  have eq295960 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by grind
  clear eq295955
  have eq296093 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq295960 eq292197
    | exact resolve eq292197 eq295960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292197 eq295960
  have eq296353 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by grind
  clear eq296093
  have eq296492 : (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq296353
       have r₂ := eq27
       grind)
    | exact resolve eq296353 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296353
  have eq296753 : (M.op x y) = (M.op (M.op x y) x) ∨ x = y := by
    first
    | (have i₁ := eq2368 x
       have i₂ := eq296492
       grind)
    | exact superpose eq296492 eq2368
    | exact resolve eq2368 eq296492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2368 eq296492
  have eq297293 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op y (M.op x y))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq296753 eq2833
    | exact resolve eq2833 eq296753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2833 eq296753
  have eq297476 : x = y ∨ x = y := by
    first
    | exact superpose eq169806 eq297293
    | exact resolve eq297293 eq169806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169806 eq297293
  have eq297477 : x = y := by grind
  clear eq297476
  have eq297522 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq297477
       grind)
    | exact superpose eq297477 eq18
    | exact resolve eq18 eq297477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq297523 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq297477
       grind)
    | exact superpose eq297477 eq24
    | exact resolve eq24 eq297477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq297477
  have eq298048 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq297523
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq297523
    | exact resolve eq297523 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq297523
  have eq298129 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq298048 eq26
    | exact resolve eq26 eq298048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq298048
  have eq299398 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq298129 eq71
    | exact resolve eq71 eq298129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq298129
  have eq299852 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq299398
       have i₂ := eq297522
       grind)
    | exact superpose eq297522 eq299398
    | exact resolve eq299398 eq297522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297522 eq299398
  have eq300092 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq299852 eq15
    | exact resolve eq15 eq299852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299852
  have eq300453 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq300092
    | exact resolve eq300092 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq300092
  have eq300580 : False := by grind
  exact eq300580
