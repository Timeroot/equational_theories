import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pyy_y_pxy_pyy_pxy_pyy_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq29 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq29 X0
       have j1 := eq10 X0 X0
       grind)
    | (have r₁ := eq29 x
       have r₂ := eq10 X0 x
       grind)
    | exact resolve eq29 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq48 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 X0
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq11 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X0 X0
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq12 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq52 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq53 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq54 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       have j1 := eq10 X1 X0
       grind)
    | (have r₁ := eq50 X1 X1
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq50 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq55 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       have j1 := eq10 X1 X0
       grind)
    | (have r₁ := eq52 X1 X1
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq52 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq56 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       have j1 := eq10 X0 X1
       grind)
    | (have r₁ := eq53 X1 X1
       have r₂ := eq10 X0 X1
       grind)
    | (have r₁ := eq53 X0 X1
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq53 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq62 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq56 X0 X1
       have j1 := eq54 X1 X0
       grind)
    | (have r₁ := eq56 X1 X0
       have r₂ := eq54 X0 X1
       grind)
    | exact resolve eq56 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq56
  have eq67 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq62 X0 X1
       have i₂ := eq30 X1
       grind)
    | exact superpose eq30 eq62
    | (have j0 := eq62 X0 X1
       grind)
    | exact resolve eq62 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq62
  have eq122 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq55 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq126 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq122 X0 X1
       have j1 := eq67 X0 X1
       grind)
    | (have r₁ := eq122 X0 X1
       have r₂ := eq67 X0 X1
       grind)
    | (have r₁ := eq122 X1 X1
       have r₂ := eq67 X1 X1
       grind)
    | exact resolve eq122 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq122
  have eq149 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq126 (σ X0) (σ X1)
       grind)
    | exact superpose eq126 eq13
    | exact resolve eq13 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq158 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq149 X0 X1
       have i₂ := eq126 X0 X1
       grind)
    | exact superpose eq126 eq149
    | exact resolve eq149 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126 eq149
  have eq1445 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq158 x y
       grind)
    | exact superpose eq158 eq14
    | (have r₁ := eq14
       have r₂ := eq158 x y
       grind)
    | exact resolve eq14 eq158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq1466 : False := by grind
  exact eq1466

/-- `x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pyy_y_pxy_x_pxy_x_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq8 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq15 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq13
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq13
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (k (τ X0) X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq8
    | exact resolve eq8 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq29 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq20
    | exact resolve eq20 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = (M.op X1 X0) ∨ (k X2 X0) = (M.op X2 X0) ∨ (M.op X2 X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 X1 X0
       have i₂ := eq12 X2 X0
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X1 X0
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 X2 : G, (k X2 X0) = (M.op X2 X0) ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X2 X0) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq42 X0 X2 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq70 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq43 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq71 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq70 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq117 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq71 (σ X0) (σ X1)
       grind)
    | exact superpose eq71 eq13
    | (have j1 := eq71 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq71 X0 (τ X1)
       grind)
    | exact superpose eq71 eq16
    | (have j1 := eq71 X0 (τ X1)
       grind)
    | exact resolve eq16 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq71
  have eq907 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq121 X0 (σ X0)
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq121
    | exact resolve eq121 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq957 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq907 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq907
    | (have j0 := eq907 X0 X1
       grind)
    | exact resolve eq907 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq907
  have eq1597 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq117 x y
       grind)
    | exact superpose eq117 eq14
    | (have j1 := eq117 x y
       grind)
    | exact resolve eq14 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1607 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq117 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq1703 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1607 (τ X0) (τ X1)
       have i₂ := eq29 X1 X0
       grind)
    | exact superpose eq29 eq1607
    | (have j0 := eq1607 (τ X0) (τ X1)
       grind)
    | exact resolve eq1607 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq1718 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1703 X0 X1
       have i₂ := eq9 (k X0 X1)
       grind)
    | exact superpose eq9 eq1703
    | (have j0 := eq1703 X0 X1
       grind)
    | exact resolve eq1703 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1703
  have eq1720 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1718 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1718
    | (have j0 := eq1718 X0 X1
       grind)
    | exact resolve eq1718 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1718
  have eq1721 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1720 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq1720
    | (have j0 := eq1720 X0 X1
       grind)
    | exact resolve eq1720 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1720
  have eq1722 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1721 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1721
    | (have j0 := eq1721 X0 X1
       grind)
    | exact resolve eq1721 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1721
  have eq2538 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1597
       have i₂ := eq957 y x
       grind)
    | exact superpose eq957 eq1597
    | (have j1 := eq957 (σ y) (σ x)
       grind)
    | (have r₁ := eq1597
       have r₂ := eq957 y x
       grind)
    | exact resolve eq1597 eq957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2539 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2538
  have eq2723 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq2539
       grind)
    | exact superpose eq2539 eq14
    | exact resolve eq14 eq2539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2724 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 (σ x) (σ y)
       have i₂ := eq2539
       grind)
    | exact superpose eq2539 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | (have r₁ := eq11 (σ x) (σ y)
       have r₂ := eq2539
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq2539
       grind)
    | exact resolve eq11 eq2539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2725 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2724
  have eq2726 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2725
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq2725
    | exact resolve eq2725 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2725
  have eq14385 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq10 X0 (σ y)
       have i₂ := eq2726
       grind)
    | exact superpose eq2726 eq10
    | (have j0 := eq10 X0 (σ y)
       grind)
    | (have r₁ := eq10 X0 (σ y)
       have r₂ := eq2726
       grind)
    | exact resolve eq10 eq2726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2726
  have eq14388 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq14385 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14385
  have eq33723 : ∀ X0 : G, (k (τ X0) y) = (τ (M.op X0 (σ y))) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq20 X0 y
       have i₂ := eq14388 X0
       grind)
    | exact superpose eq14388 eq20
    | exact resolve eq20 eq14388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq14388
  have eq62758 : (τ (σ x)) = (k (τ (σ x)) y) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq33723 (σ x)
       have i₂ := eq2539
       grind)
    | exact superpose eq2539 eq33723
    | exact resolve eq33723 eq2539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2539 eq33723
  have eq62768 : (τ (σ x)) = (k (τ (σ x)) y) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) := by grind
  clear eq62758
  have eq62772 : x = (k x y) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq62768
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq62768
    | exact resolve eq62768 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62768
  have eq62774 : (σ x) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq1722 x y
       grind)
    | (have r₁ := eq62772
       have r₂ := eq1722 x y
       grind)
    | exact resolve eq62772 eq1722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1722 eq62772
  have eq63328 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq957 y x
       have i₂ := eq62774
       grind)
    | exact superpose eq62774 eq957
    | (have j0 := eq957 y x
       grind)
    | exact resolve eq957 eq62774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq957 eq62774
  have eq63416 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq63328
  have eq63444 : x = (M.op x y) := by
    first
    | (have r₁ := eq63416
       have r₂ := eq2723
       grind)
    | exact resolve eq63416 eq2723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2723 eq63416
  have eq64053 : x ≠ x ∨ y = (M.op y y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq63444
       grind)
    | exact superpose eq63444 eq11
    | (have j0 := eq11 x y
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq63444
       grind)
    | exact resolve eq11 eq63444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64054 : x = (k x y) ∨ y = (M.op y y) := by grind
  clear eq64053
  have eq64702 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1607 x y
       have i₂ := eq64054
       grind)
    | exact superpose eq64054 eq1607
    | (have j0 := eq1607 x y
       grind)
    | exact resolve eq1607 eq64054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1607 eq64054
  have eq64763 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq64702
  have eq65732 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq64763
       grind)
    | exact superpose eq64763 eq14
    | exact resolve eq14 eq64763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64763
  have eq65737 : (σ x) ≠ (σ x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq65732
       have i₂ := eq63444
       grind)
    | exact superpose eq63444 eq65732
    | exact resolve eq65732 eq63444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65732
  have eq65738 : y = (M.op y y) := by grind
  clear eq65737
  have eq66246 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq65738
       grind)
    | exact superpose eq65738 eq10
    | (have j0 := eq10 X0 y
       grind)
    | (have r₁ := eq10 X0 y
       have r₂ := eq65738
       grind)
    | exact resolve eq10 eq65738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65738
  have eq66249 : ∀ X0 : G, (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq66246 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66246
  have eq66924 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1597
       have i₂ := eq66249 x
       grind)
    | exact superpose eq66249 eq1597
    | exact resolve eq1597 eq66249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1597 eq66249
  have eq66925 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq66924
  have eq67522 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq66925
       grind)
    | exact superpose eq66925 eq14
    | exact resolve eq14 eq66925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66925
  have eq67527 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq67522
       have i₂ := eq63444
       grind)
    | exact superpose eq63444 eq67522
    | exact resolve eq67522 eq63444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63444 eq67522
  have eq67528 : False := by grind
  exact eq67528

/-- `x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pyy_y_pxy_y_pxy_y_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq8 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq15 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq13
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (k (τ X0) X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq8
    | exact resolve eq8 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq20
    | exact resolve eq20 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = (M.op X1 X0) ∨ (k X2 X0) = (M.op X2 X0) ∨ (M.op X2 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 X1 X0
       have i₂ := eq12 X2 X0
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X1 X0
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 X2 : G, (k X2 X0) = (M.op X2 X0) ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X2 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq42 X0 X2 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq70 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq43 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq71 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq70 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq117 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq71 (σ X0) (σ X1)
       grind)
    | exact superpose eq71 eq13
    | (have j1 := eq71 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq71 (τ X0) X1
       grind)
    | exact superpose eq71 eq15
    | (have j1 := eq71 (τ X0) X1
       grind)
    | exact resolve eq15 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq71
  have eq1187 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq119 (σ X0) X1
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq119
    | exact resolve eq119 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq1242 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1187 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq1187
    | (have j0 := eq1187 X0 X1
       grind)
    | exact resolve eq1187 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1187
  have eq1628 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq117 x y
       grind)
    | exact superpose eq117 eq14
    | (have j1 := eq117 x y
       grind)
    | exact resolve eq14 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1638 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq117 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq1656 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1638 (τ X0) (τ X1)
       have i₂ := eq29 X1 X0
       grind)
    | exact superpose eq29 eq1638
    | (have j0 := eq1638 (τ X0) (τ X1)
       grind)
    | exact resolve eq1638 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq1670 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1656 X0 X1
       have i₂ := eq9 (k X0 X1)
       grind)
    | exact superpose eq9 eq1656
    | (have j0 := eq1656 X0 X1
       grind)
    | exact resolve eq1656 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1656
  have eq1672 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1670 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq1670
    | (have j0 := eq1670 X0 X1
       grind)
    | exact resolve eq1670 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1670
  have eq1673 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1672 X0 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1672
    | (have j0 := eq1672 X0 X1
       grind)
    | exact resolve eq1672 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1672
  have eq1674 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1673 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1673
    | (have j0 := eq1673 X0 X1
       grind)
    | exact resolve eq1673 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1673
  have eq2550 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1628
       have i₂ := eq1242 x y
       grind)
    | exact superpose eq1242 eq1628
    | (have j1 := eq1242 (σ x) (σ y)
       grind)
    | (have r₁ := eq1628
       have r₂ := eq1242 x y
       grind)
    | exact resolve eq1628 eq1242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2551 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2550
  have eq2731 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq2551
       grind)
    | exact superpose eq2551 eq14
    | exact resolve eq14 eq2551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2732 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 (σ x) (σ y)
       have i₂ := eq2551
       grind)
    | exact superpose eq2551 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | (have r₁ := eq11 (σ x) (σ y)
       have r₂ := eq2551
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq2551
       grind)
    | exact resolve eq11 eq2551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2733 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2732
  have eq2734 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (σ (k x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2733
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq2733
    | exact resolve eq2733 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2733
  have eq14774 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ y) = (σ (k x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq10 X0 (σ y)
       have i₂ := eq2734
       grind)
    | exact superpose eq2734 eq10
    | (have j0 := eq10 X0 (σ y)
       grind)
    | (have r₁ := eq10 X0 (σ y)
       have r₂ := eq2734
       grind)
    | exact resolve eq10 eq2734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2734
  have eq14777 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ y) = (σ (k x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq14774 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14774
  have eq32560 : ∀ X0 : G, (k (τ X0) y) = (τ (M.op X0 (σ y))) ∨ (σ y) = (σ (k x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq20 X0 y
       have i₂ := eq14777 X0
       grind)
    | exact superpose eq14777 eq20
    | exact resolve eq20 eq14777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq14777
  have eq61280 : (τ (σ y)) = (k (τ (σ x)) y) ∨ (σ y) = (σ (k x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq32560 (σ x)
       have i₂ := eq2551
       grind)
    | exact superpose eq2551 eq32560
    | exact resolve eq32560 eq2551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2551 eq32560
  have eq61294 : (τ (σ y)) = (k (τ (σ x)) y) ∨ (σ y) = (σ (k x y)) ∨ y = (M.op x y) := by grind
  clear eq61280
  have eq61299 : (k x y) = (τ (σ y)) ∨ (σ y) = (σ (k x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq61294
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq61294
    | exact resolve eq61294 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61294
  have eq61301 : y = (k x y) ∨ (σ y) = (σ (k x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq61299
       have i₂ := eq8 y
       grind)
    | exact superpose eq8 eq61299
    | exact resolve eq61299 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61299
  have eq61302 : (σ y) = (σ (k x y)) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq1674 x y
       grind)
    | (have r₁ := eq61301
       have r₂ := eq1674 x y
       grind)
    | exact resolve eq61301 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1674 eq61301
  have eq61717 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1242 x y
       have i₂ := eq61302
       grind)
    | exact superpose eq61302 eq1242
    | (have j0 := eq1242 x y
       grind)
    | exact resolve eq1242 eq61302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1242 eq61302
  have eq61808 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq61717
  have eq61836 : y = (M.op x y) := by
    first
    | (have r₁ := eq61808
       have r₂ := eq2731
       grind)
    | exact resolve eq61808 eq2731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2731 eq61808
  have eq62368 : y ≠ y ∨ y = (M.op y y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq61836
       grind)
    | exact superpose eq61836 eq11
    | (have j0 := eq11 x y
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq61836
       grind)
    | exact resolve eq11 eq61836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62369 : y = (k x y) ∨ y = (M.op y y) := by grind
  clear eq62368
  have eq62909 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1638 x y
       have i₂ := eq62369
       grind)
    | exact superpose eq62369 eq1638
    | (have j0 := eq1638 x y
       grind)
    | exact resolve eq1638 eq62369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1638 eq62369
  have eq62966 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq62909
  have eq64046 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq62966
       grind)
    | exact superpose eq62966 eq14
    | exact resolve eq14 eq62966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62966
  have eq64051 : (σ y) ≠ (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq64046
       have i₂ := eq61836
       grind)
    | exact superpose eq61836 eq64046
    | exact resolve eq64046 eq61836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64046
  have eq64052 : y = (M.op y y) := by grind
  clear eq64051
  have eq64604 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq64052
       grind)
    | exact superpose eq64052 eq10
    | (have j0 := eq10 X0 y
       grind)
    | (have r₁ := eq10 X0 y
       have r₂ := eq64052
       grind)
    | exact resolve eq10 eq64052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64052
  have eq64607 : ∀ X0 : G, (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq64604 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64604
  have eq65295 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1628
       have i₂ := eq64607 x
       grind)
    | exact superpose eq64607 eq1628
    | exact resolve eq1628 eq64607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1628 eq64607
  have eq65296 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq65295
  have eq65953 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq65296
       grind)
    | exact superpose eq65296 eq14
    | exact resolve eq14 eq65296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65296
  have eq65958 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq65953
       have i₂ := eq61836
       grind)
    | exact superpose eq61836 eq65953
    | exact resolve eq65953 eq61836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61836 eq65953
  have eq65959 : False := by grind
  exact eq65959

/-- `x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pyy_y_pyx_pyy_pyx_pyy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq29 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq29 X0
       have j1 := eq10 X0 X0
       grind)
    | (have r₁ := eq29 x
       have r₂ := eq10 X0 x
       grind)
    | exact resolve eq29 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq48 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X0 X0
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 X0
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq11 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X0 X0
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq12 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq52 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq53 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq54 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       have j1 := eq10 X1 X0
       grind)
    | (have r₁ := eq50 X1 X1
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq50 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq55 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       have j1 := eq10 X1 X0
       grind)
    | (have r₁ := eq52 X1 X1
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq52 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq56 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       have j1 := eq10 X1 X0
       grind)
    | (have r₁ := eq53 X1 X1
       have r₂ := eq10 X0 X1
       grind)
    | (have r₁ := eq53 X1 X1
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq53 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq62 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X0) ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq56 X0 X1
       have j1 := eq54 X0 X1
       grind)
    | (have r₁ := eq56 X0 X1
       have r₂ := eq54 X0 X1
       grind)
    | exact resolve eq56 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq56
  have eq67 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq62 X0 X1
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq62
    | (have j0 := eq62 X0 X1
       grind)
    | exact resolve eq62 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq62
  have eq122 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq55 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq126 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq122 X0 X1
       have j1 := eq67 X1 X0
       grind)
    | (have r₁ := eq122 X1 X0
       have r₂ := eq67 X0 X1
       grind)
    | (have r₁ := eq122 X1 X1
       have r₂ := eq67 X1 X1
       grind)
    | exact resolve eq122 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq122
  have eq149 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq126 (σ X1) (σ X0)
       grind)
    | exact superpose eq126 eq13
    | exact resolve eq13 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq158 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq149 X0 X1
       have i₂ := eq126 X1 X0
       grind)
    | exact superpose eq126 eq149
    | exact resolve eq149 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126 eq149
  have eq1447 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq158 x y
       grind)
    | exact superpose eq158 eq14
    | (have r₁ := eq14
       have r₂ := eq158 x y
       grind)
    | exact resolve eq14 eq158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq1468 : False := by grind
  exact eq1468

/-- `x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pyy_y_pyx_x_pyx_x_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq8 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq15 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq13
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq13
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (k (τ X0) X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq8
    | exact resolve eq8 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq29 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq20
    | exact resolve eq20 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = (M.op X0 X1) ∨ (k X2 X0) = (M.op X0 X2) ∨ (M.op X0 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 X1 X0
       have i₂ := eq12 X2 X0
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X1 X0
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 X2 : G, (k X2 X0) = (M.op X0 X2) ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq42 X0 X2 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq70 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq43 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq71 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq70 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq118 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq71 (σ X1) (σ X0)
       grind)
    | exact superpose eq71 eq13
    | (have j1 := eq71 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq71 X1 (τ X0)
       grind)
    | exact superpose eq71 eq16
    | (have j1 := eq71 X1 (τ X0)
       grind)
    | exact resolve eq16 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq71
  have eq828 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq122 (σ X0) X1
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq122
    | exact resolve eq122 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq877 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq828 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq828
    | (have j0 := eq828 X0 X1
       grind)
    | exact resolve eq828 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828
  have eq1608 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq118 x y
       grind)
    | exact superpose eq118 eq14
    | (have j1 := eq118 x y
       grind)
    | exact resolve eq14 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1618 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq118 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq1636 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1618 (τ X1) (τ X0)
       have i₂ := eq29 X1 X0
       grind)
    | exact superpose eq29 eq1618
    | (have j0 := eq1618 (τ X1) (τ X0)
       grind)
    | exact resolve eq1618 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq1650 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1636 X0 X1
       have i₂ := eq9 (k X0 X1)
       grind)
    | exact superpose eq9 eq1636
    | (have j0 := eq1636 X0 X1
       grind)
    | exact resolve eq1636 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1636
  have eq1652 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1650 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1650
    | (have j0 := eq1650 X0 X1
       grind)
    | exact resolve eq1650 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1650
  have eq1653 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1652 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1652
    | (have j0 := eq1652 X0 X1
       grind)
    | exact resolve eq1652 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1652
  have eq1654 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1653 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq1653
    | (have j0 := eq1653 X0 X1
       grind)
    | exact resolve eq1653 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1653
  have eq2381 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1608
       have i₂ := eq877 x y
       grind)
    | exact superpose eq877 eq1608
    | (have j1 := eq877 (σ x) (σ y)
       grind)
    | (have r₁ := eq1608
       have r₂ := eq877 x y
       grind)
    | exact resolve eq1608 eq877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2382 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2381
  have eq2561 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq2382
       grind)
    | exact superpose eq2382 eq14
    | exact resolve eq14 eq2382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2562 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 (σ y) (σ x)
       have i₂ := eq2382
       grind)
    | exact superpose eq2382 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | (have r₁ := eq11 (σ y) (σ x)
       have r₂ := eq2382
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq2382
       grind)
    | exact resolve eq11 eq2382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2563 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq2562
  have eq2564 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2563
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq2563
    | exact resolve eq2563 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2563
  have eq13864 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq10 X0 (σ x)
       have i₂ := eq2564
       grind)
    | exact superpose eq2564 eq10
    | (have j0 := eq10 X0 (σ x)
       grind)
    | (have r₁ := eq10 X0 (σ x)
       have r₂ := eq2564
       grind)
    | exact resolve eq10 eq2564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2564
  have eq13867 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq13864 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13864
  have eq32310 : ∀ X0 : G, (k (τ X0) x) = (τ (M.op (σ x) X0)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq20 X0 x
       have i₂ := eq13867 X0
       grind)
    | exact superpose eq13867 eq20
    | exact resolve eq20 eq13867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq13867
  have eq61910 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq32310 (σ y)
       have i₂ := eq2382
       grind)
    | exact superpose eq2382 eq32310
    | exact resolve eq32310 eq2382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2382 eq32310
  have eq61925 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by grind
  clear eq61910
  have eq61931 : y = (k y x) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq61925
       have i₂ := eq8 y
       grind)
    | exact superpose eq8 eq61925
    | exact resolve eq61925 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61925
  have eq61932 : (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq1654 y x
       grind)
    | (have r₁ := eq61931
       have r₂ := eq1654 y x
       grind)
    | exact resolve eq61931 eq1654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1654 eq61931
  have eq62501 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq877 x y
       have i₂ := eq61932
       grind)
    | exact superpose eq61932 eq877
    | (have j0 := eq877 x y
       grind)
    | exact resolve eq877 eq61932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq877 eq61932
  have eq62592 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq62501
  have eq62620 : y = (M.op x y) := by
    first
    | (have r₁ := eq62592
       have r₂ := eq2561
       grind)
    | exact resolve eq62592 eq2561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2561 eq62592
  have eq63208 : y ≠ y ∨ x = (M.op x x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq62620
       grind)
    | exact superpose eq62620 eq11
    | (have j0 := eq11 y x
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq62620
       grind)
    | exact resolve eq11 eq62620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63209 : y = (k y x) ∨ x = (M.op x x) := by grind
  clear eq63208
  have eq63794 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1618 x y
       have i₂ := eq63209
       grind)
    | exact superpose eq63209 eq1618
    | (have j0 := eq1618 x y
       grind)
    | exact resolve eq1618 eq63209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1618 eq63209
  have eq63855 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq63794
  have eq65016 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq63855
       grind)
    | exact superpose eq63855 eq14
    | exact resolve eq14 eq63855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63855
  have eq65021 : (σ y) ≠ (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq65016
       have i₂ := eq62620
       grind)
    | exact superpose eq62620 eq65016
    | exact resolve eq65016 eq62620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65016
  have eq65022 : x = (M.op x x) := by grind
  clear eq65021
  have eq65651 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq10 X0 x
       have i₂ := eq65022
       grind)
    | exact superpose eq65022 eq10
    | (have j0 := eq10 X0 x
       grind)
    | (have r₁ := eq10 X0 x
       have r₂ := eq65022
       grind)
    | exact resolve eq10 eq65022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65022
  have eq65654 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq65651 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65651
  have eq66219 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1608
       have i₂ := eq65654 y
       grind)
    | exact superpose eq65654 eq1608
    | exact resolve eq1608 eq65654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1608 eq65654
  have eq66222 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq66219
  have eq66827 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq66222
       grind)
    | exact superpose eq66222 eq14
    | exact resolve eq14 eq66222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66222
  have eq66832 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq66827
       have i₂ := eq62620
       grind)
    | exact superpose eq62620 eq66827
    | exact resolve eq66827 eq62620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62620 eq66827
  have eq66833 : False := by grind
  exact eq66833

/-- `x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_y_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq8 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq15 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq13
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (k (τ X0) X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq8
    | exact resolve eq8 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq20
    | exact resolve eq20 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = (M.op X0 X1) ∨ (k X2 X0) = (M.op X0 X2) ∨ (M.op X0 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 X1 X0
       have i₂ := eq12 X2 X0
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X1 X0
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 X2 : G, (k X2 X0) = (M.op X0 X2) ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq42 X0 X2 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq70 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq43 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq71 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq70 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq118 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq71 (σ X1) (σ X0)
       grind)
    | exact superpose eq71 eq13
    | (have j1 := eq71 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq71 (τ X1) X0
       grind)
    | exact superpose eq71 eq15
    | (have j1 := eq71 (τ X1) X0
       grind)
    | exact resolve eq15 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq71
  have eq1081 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq120 X0 (σ X0)
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq120
    | exact resolve eq120 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq1135 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1081 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq1081
    | (have j0 := eq1081 X0 X1
       grind)
    | exact resolve eq1081 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1081
  have eq1639 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq118 x y
       grind)
    | exact superpose eq118 eq14
    | (have j1 := eq118 x y
       grind)
    | exact resolve eq14 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1649 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq118 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq1748 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1649 (τ X1) (τ X0)
       have i₂ := eq29 X1 X0
       grind)
    | exact superpose eq29 eq1649
    | (have j0 := eq1649 (τ X1) (τ X0)
       grind)
    | exact resolve eq1649 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq1763 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1748 X0 X1
       have i₂ := eq9 (k X0 X1)
       grind)
    | exact superpose eq9 eq1748
    | (have j0 := eq1748 X0 X1
       grind)
    | exact resolve eq1748 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1748
  have eq1765 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1763 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq1763
    | (have j0 := eq1763 X0 X1
       grind)
    | exact resolve eq1763 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1763
  have eq1766 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1765 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1765
    | (have j0 := eq1765 X0 X1
       grind)
    | exact resolve eq1765 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1765
  have eq1767 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1766 X0 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1766
    | (have j0 := eq1766 X0 X1
       grind)
    | exact resolve eq1766 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1766
  have eq2735 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1639
       have i₂ := eq1135 y x
       grind)
    | exact superpose eq1135 eq1639
    | (have j1 := eq1135 (σ y) (σ x)
       grind)
    | (have r₁ := eq1639
       have r₂ := eq1135 y x
       grind)
    | exact resolve eq1639 eq1135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2736 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2735
  have eq2920 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq2736
       grind)
    | exact superpose eq2736 eq14
    | exact resolve eq14 eq2736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2921 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 (σ y) (σ x)
       have i₂ := eq2736
       grind)
    | exact superpose eq2736 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | (have r₁ := eq11 (σ y) (σ x)
       have r₂ := eq2736
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq2736
       grind)
    | exact resolve eq11 eq2736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2922 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq2921
  have eq2923 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2922
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq2922
    | exact resolve eq2922 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2922
  have eq14626 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq10 X0 (σ x)
       have i₂ := eq2923
       grind)
    | exact superpose eq2923 eq10
    | (have j0 := eq10 X0 (σ x)
       grind)
    | (have r₁ := eq10 X0 (σ x)
       have r₂ := eq2923
       grind)
    | exact resolve eq10 eq2923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2923
  have eq14629 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq14626 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14626
  have eq31803 : ∀ X0 : G, (k (τ X0) x) = (τ (M.op (σ x) X0)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq20 X0 x
       have i₂ := eq14629 X0
       grind)
    | exact superpose eq14629 eq20
    | exact resolve eq20 eq14629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq14629
  have eq60414 : (k (τ (σ y)) x) = (τ (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq31803 (σ y)
       have i₂ := eq2736
       grind)
    | exact superpose eq2736 eq31803
    | exact resolve eq31803 eq2736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2736 eq31803
  have eq60429 : (k (τ (σ y)) x) = (τ (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by grind
  clear eq60414
  have eq60435 : x = (k (τ (σ y)) x) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq60429
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq60429
    | exact resolve eq60429 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60429
  have eq60436 : x = (k y x) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq60435
       have i₂ := eq8 y
       grind)
    | exact superpose eq8 eq60435
    | exact resolve eq60435 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60435
  have eq60437 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq1767 y x
       grind)
    | (have r₁ := eq60436
       have r₂ := eq1767 y x
       grind)
    | exact resolve eq60436 eq1767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1767 eq60436
  have eq60747 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1135 y x
       have i₂ := eq60437
       grind)
    | exact superpose eq60437 eq1135
    | (have j0 := eq1135 y x
       grind)
    | exact resolve eq1135 eq60437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1135 eq60437
  have eq60838 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq60747
  have eq60866 : x = (M.op x y) := by
    first
    | (have r₁ := eq60838
       have r₂ := eq2920
       grind)
    | exact resolve eq60838 eq2920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2920 eq60838
  have eq61275 : x ≠ x ∨ x = (M.op x x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq60866
       grind)
    | exact superpose eq60866 eq11
    | (have j0 := eq11 y x
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq60866
       grind)
    | exact resolve eq11 eq60866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61276 : x = (k y x) ∨ x = (M.op x x) := by grind
  clear eq61275
  have eq61824 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1649 x y
       have i₂ := eq61276
       grind)
    | exact superpose eq61276 eq1649
    | (have j0 := eq1649 x y
       grind)
    | exact resolve eq1649 eq61276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1649 eq61276
  have eq61881 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq61824
  have eq62954 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq61881
       grind)
    | exact superpose eq61881 eq14
    | exact resolve eq14 eq61881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61881
  have eq62959 : (σ x) ≠ (σ x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq62954
       have i₂ := eq60866
       grind)
    | exact superpose eq60866 eq62954
    | exact resolve eq62954 eq60866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62954
  have eq62960 : x = (M.op x x) := by grind
  clear eq62959
  have eq63486 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq10 X0 x
       have i₂ := eq62960
       grind)
    | exact superpose eq62960 eq10
    | (have j0 := eq10 X0 x
       grind)
    | (have r₁ := eq10 X0 x
       have r₂ := eq62960
       grind)
    | exact resolve eq10 eq62960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62960
  have eq63489 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq63486 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63486
  have eq64184 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1639
       have i₂ := eq63489 y
       grind)
    | exact superpose eq63489 eq1639
    | exact resolve eq1639 eq63489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1639 eq63489
  have eq64187 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq64184
  have eq64813 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq64187
       grind)
    | exact superpose eq64187 eq14
    | exact resolve eq14 eq64187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64187
  have eq64818 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq64813
       have i₂ := eq60866
       grind)
    | exact superpose eq60866 eq64813
    | exact resolve eq64813 eq60866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60866 eq64813
  have eq64819 : False := by grind
  exact eq64819

/-- `x □ y = if m(Y,Y) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pyy_y_x_y_pxy_pxx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
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
  have eq8 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq13
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq13
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (k (τ X0) X1)
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq8
    | exact resolve eq8 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq33 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    grind
  have eq34 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq33 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq33
    | (have j0 := eq33 X0
       grind)
    | exact resolve eq33 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq36 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq21 X1 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq21
    | exact resolve eq21 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq51 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = (M.op X1 X0) ∨ (k X2 X0) = (M.op X2 X0) ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 X1 X0
       have i₂ := eq12 X2 X0
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X1 X0
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq10 X0 X0
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 : G, (k X2 X0) = (M.op X2 X0) ∨ (k X1 X0) = (M.op X1 X0) ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq51 X0 X2 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq81 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq52 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq82 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq81 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq85 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq82 (σ X0) (σ X1)
       grind)
    | exact superpose eq82 eq13
    | (have j1 := eq82 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq13 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq82 (τ X0) X1
       grind)
    | exact superpose eq82 eq16
    | (have j1 := eq82 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq16 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq82
  have eq95 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq31 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq225 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq87 (σ X0) X1
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq87
    | exact resolve eq87 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq251 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq225 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq225
    | (have j0 := eq225 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq225 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq401 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq95 (τ X0)
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq95
    | (have j0 := eq95 (τ X0)
       grind)
    | exact resolve eq95 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq95
  have eq402 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq401 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq401
    | (have j0 := eq401 X0
       grind)
    | exact resolve eq401 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401
  have eq405 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq402 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq402
    | (have j0 := eq402 X0
       grind)
    | exact resolve eq402 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402
  have eq412 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq405 (τ X0)
       have i₂ := eq36 X0 X0
       grind)
    | exact superpose eq36 eq405
    | (have j0 := eq405 (τ X0)
       grind)
    | exact resolve eq405 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq405
  have eq431 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq34 (σ X0)
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq34
    | exact resolve eq34 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq456 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq431 X0
       have i₂ := eq13 X0 X0
       grind)
    | exact superpose eq13 eq431
    | (have j0 := eq431 X0
       grind)
    | exact resolve eq431 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431
  have eq1220 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq85 x y
       grind)
    | exact superpose eq85 eq14
    | (have j1 := eq85 x y
       grind)
    | exact resolve eq14 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq1308 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1220
       have i₂ := eq251 x y
       grind)
    | exact superpose eq251 eq1220
    | (have j1 := eq251 (σ x) (σ y)
       grind)
    | (have r₁ := eq1220
       have r₂ := eq251 x y
       grind)
    | (have r₁ := eq1220
       have r₂ := eq251 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq1220
       have r₂ := eq251 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq1220 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251 eq1220
  have eq1309 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1308
  have eq1391 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq8 y
       have i₂ := eq1309
       grind)
    | exact superpose eq1309 eq8
    | exact resolve eq8 eq1309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1309
  have eq1439 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1391
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq1391
    | exact resolve eq1391 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1391
  have eq1440 : x = y := by grind
  clear eq1439
  have eq1562 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1440
       grind)
    | exact superpose eq1440 eq14
    | exact resolve eq14 eq1440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1440
  have eq1659 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1562
       have i₂ := eq31 x
       grind)
    | exact superpose eq31 eq1562
    | (have j1 := eq31 x
       grind)
    | exact resolve eq1562 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq9951 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1659
       have i₂ := eq456 x
       grind)
    | exact superpose eq456 eq1659
    | (have j1 := eq456 (σ x)
       grind)
    | (have r₁ := eq1659
       have r₂ := eq456 x
       grind)
    | exact resolve eq1659 eq456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456
  have eq9952 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq9951
  have eq10096 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq10 X0 (σ x)
       have i₂ := eq9952
       grind)
    | exact superpose eq9952 eq10
    | (have j0 := eq10 X0 (σ x)
       grind)
    | (have r₁ := eq10 X0 (σ x)
       have r₂ := eq9952
       grind)
    | (have r₁ := eq10 X0 x
       have r₂ := eq9952
       grind)
    | exact resolve eq10 eq9952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10097 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq10096 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10096
  have eq10360 : (τ (σ x)) ≠ (τ (M.op (σ x) (σ x))) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq412 (σ x)
       have i₂ := eq10097 (σ x)
       grind)
    | exact superpose eq10097 eq412
    | (have j0 := eq412 (σ x)
       grind)
    | exact resolve eq412 eq10097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412 eq10097
  have eq10420 : x ≠ (τ (M.op (σ x) (σ x))) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10360
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq10360
    | exact resolve eq10360 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10360
  have eq10423 : x = (M.op x x) ∨ x ≠ (τ (M.op (σ x) (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10420
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq10420
    | exact resolve eq10420 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10420
  have eq10424 : x ≠ (τ (M.op (σ x) (σ x))) ∨ x = (M.op x x) := by grind
  clear eq10423
  have eq10656 : x ≠ (τ (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10424
       have i₂ := eq9952
       grind)
    | exact superpose eq9952 eq10424
    | exact resolve eq10424 eq9952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9952 eq10424
  have eq10661 : x ≠ (τ (σ x)) ∨ x = (M.op x x) := by grind
  clear eq10656
  have eq10662 : x = (M.op x x) := by
    first
    | (have r₁ := eq10661
       have r₂ := eq8 x
       grind)
    | exact resolve eq10661 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10661
  have eq10961 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq10 X0 x
       have i₂ := eq10662
       grind)
    | exact superpose eq10662 eq10
    | (have j0 := eq10 X0 x
       grind)
    | (have r₁ := eq10 X0 x
       have r₂ := eq10662
       grind)
    | exact resolve eq10 eq10662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10962 : ∀ X0 : G, (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq10961 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10961
  have eq11316 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1659
       have i₂ := eq10962 x
       grind)
    | exact superpose eq10962 eq1659
    | exact resolve eq1659 eq10962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1659 eq10962
  have eq11318 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq11316
  have eq11616 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1562
       have i₂ := eq11318
       grind)
    | exact superpose eq11318 eq1562
    | exact resolve eq1562 eq11318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1562 eq11318
  have eq11619 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq11616
       have i₂ := eq10662
       grind)
    | exact superpose eq10662 eq11616
    | exact resolve eq11616 eq10662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10662 eq11616
  have eq11620 : False := by grind
  exact eq11620

/-- `x □ y = if m(Y,Y) = Y then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pyy_y_x_y_pyx_pxx_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq8 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq13
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq13
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (k (τ X0) X1)
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq8
    | exact resolve eq8 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq33 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    grind
  have eq34 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq33 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq33
    | (have j0 := eq33 X0
       grind)
    | exact resolve eq33 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq36 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq21 X1 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq21
    | exact resolve eq21 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq51 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = (M.op X0 X1) ∨ (k X2 X0) = (M.op X0 X2) ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 X1 X0
       have i₂ := eq12 X2 X0
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X1 X0
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq10 X0 X0
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 : G, (k X2 X0) = (M.op X0 X2) ∨ (k X1 X0) = (M.op X0 X1) ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq51 X0 X2 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq81 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq52 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq82 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq81 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq85 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq82 (σ X1) (σ X0)
       grind)
    | exact superpose eq82 eq13
    | (have j1 := eq82 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq13 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq82 (τ X1) X0
       grind)
    | exact superpose eq82 eq16
    | (have j1 := eq82 (k X1 (σ X0)) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq16 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq82
  have eq95 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq31 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq226 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq87 X0 (σ X0)
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq87
    | exact resolve eq87 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq252 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq226 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq226
    | (have j0 := eq226 (σ (k X0 X1)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq226 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq402 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq95 (τ X0)
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq95
    | (have j0 := eq95 (τ X0)
       grind)
    | exact resolve eq95 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq95
  have eq403 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq402 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq402
    | (have j0 := eq402 X0
       grind)
    | exact resolve eq402 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402
  have eq406 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq403 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq403
    | (have j0 := eq403 X0
       grind)
    | exact resolve eq403 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403
  have eq413 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq406 (τ X0)
       have i₂ := eq36 X0 X0
       grind)
    | exact superpose eq36 eq406
    | (have j0 := eq406 (τ X0)
       grind)
    | exact resolve eq406 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq406
  have eq432 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq34 (σ X0)
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq34
    | exact resolve eq34 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq457 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq432 X0
       have i₂ := eq13 X0 X0
       grind)
    | exact superpose eq13 eq432
    | (have j0 := eq432 X0
       grind)
    | exact resolve eq432 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432
  have eq1163 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq85 x y
       grind)
    | exact superpose eq85 eq14
    | (have j1 := eq85 x y
       grind)
    | exact resolve eq14 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq1244 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1163
       have i₂ := eq252 y x
       grind)
    | exact superpose eq252 eq1163
    | (have j1 := eq252 (σ x) (σ y)
       grind)
    | (have r₁ := eq1163
       have r₂ := eq252 y x
       grind)
    | (have r₁ := eq1163
       have r₂ := eq252 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1163
       have r₂ := eq252 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1163 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252 eq1163
  have eq1245 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1244
  have eq1326 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq8 y
       have i₂ := eq1245
       grind)
    | exact superpose eq1245 eq8
    | exact resolve eq8 eq1245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1245
  have eq1374 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1326
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq1326
    | exact resolve eq1326 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1326
  have eq1375 : x = y := by grind
  clear eq1374
  have eq1452 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1375
       grind)
    | exact superpose eq1375 eq14
    | exact resolve eq14 eq1375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1375
  have eq1575 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1452
       have i₂ := eq31 x
       grind)
    | exact superpose eq31 eq1452
    | (have j1 := eq31 x
       grind)
    | exact resolve eq1452 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq9975 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1575
       have i₂ := eq457 x
       grind)
    | exact superpose eq457 eq1575
    | (have j1 := eq457 (σ x)
       grind)
    | (have r₁ := eq1575
       have r₂ := eq457 x
       grind)
    | exact resolve eq1575 eq457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457
  have eq9976 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq9975
  have eq10120 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq10 X0 (σ x)
       have i₂ := eq9976
       grind)
    | exact superpose eq9976 eq10
    | (have j0 := eq10 X0 (σ x)
       grind)
    | (have r₁ := eq10 X0 (σ x)
       have r₂ := eq9976
       grind)
    | (have r₁ := eq10 X0 x
       have r₂ := eq9976
       grind)
    | exact resolve eq10 eq9976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10121 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq10120 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10120
  have eq10384 : (τ (σ x)) ≠ (τ (M.op (σ x) (σ x))) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq413 (σ x)
       have i₂ := eq10121 (σ x)
       grind)
    | exact superpose eq10121 eq413
    | (have j0 := eq413 (σ x)
       grind)
    | exact resolve eq413 eq10121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413 eq10121
  have eq10444 : x ≠ (τ (M.op (σ x) (σ x))) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10384
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq10384
    | exact resolve eq10384 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10384
  have eq10447 : x = (M.op x x) ∨ x ≠ (τ (M.op (σ x) (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10444
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq10444
    | exact resolve eq10444 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10444
  have eq10448 : x ≠ (τ (M.op (σ x) (σ x))) ∨ x = (M.op x x) := by grind
  clear eq10447
  have eq10680 : x ≠ (τ (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10448
       have i₂ := eq9976
       grind)
    | exact superpose eq9976 eq10448
    | exact resolve eq10448 eq9976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9976 eq10448
  have eq10686 : x ≠ (τ (σ x)) ∨ x = (M.op x x) := by grind
  clear eq10680
  have eq10687 : x = (M.op x x) := by
    first
    | (have r₁ := eq10686
       have r₂ := eq8 x
       grind)
    | exact resolve eq10686 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10686
  have eq10986 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq10 X0 x
       have i₂ := eq10687
       grind)
    | exact superpose eq10687 eq10
    | (have j0 := eq10 X0 x
       grind)
    | (have r₁ := eq10 X0 x
       have r₂ := eq10687
       grind)
    | exact resolve eq10 eq10687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10987 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq10986 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10986
  have eq11341 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1575
       have i₂ := eq10987 x
       grind)
    | exact superpose eq10987 eq1575
    | exact resolve eq1575 eq10987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1575 eq10987
  have eq11349 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq11341
  have eq11647 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1452
       have i₂ := eq11349
       grind)
    | exact superpose eq11349 eq1452
    | exact resolve eq1452 eq11349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1452 eq11349
  have eq11650 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq11647
       have i₂ := eq10687
       grind)
    | exact superpose eq10687 eq11647
    | exact resolve eq11647 eq10687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10687 eq11647
  have eq11651 : False := by grind
  exact eq11651
