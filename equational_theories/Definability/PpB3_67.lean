import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation426`: `x = x ◇ (y ◇ (x ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pyx_pyy_pyx_Equation426 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law426 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law426.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X0 X0)))) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
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
  have eq52 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq52 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq52 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq52 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq55 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq53 (σ X0)
       grind)
    | exact superpose eq53 eq15
    | exact resolve eq15 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq53 (τ X0)
       grind)
    | exact superpose eq53 eq18
    | exact resolve eq18 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq58 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq58
    | exact resolve eq58 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq64 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq55 X0
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq55
    | exact resolve eq55 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq67 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq61 X0
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq61
    | exact resolve eq61 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq61
  have eq74 : ∀ X0 X1 : G, (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq64 (k X1 (τ X0))
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq64
    | exact resolve eq64 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (σ (M.op X0 X0)) = (k X1 (σ X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X0)
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq13
    | exact resolve eq13 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (M.op X1 (M.op (σ X0) (σ (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq9
    | exact resolve eq9 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq88 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq82 X0 X1
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq82
    | (have j0 := eq82 X0 X1
       grind)
    | exact resolve eq82 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq91 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq88 X0 X1
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq88
    | (have j0 := eq88 X0 X1
       grind)
    | exact resolve eq88 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq88
  have eq101 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq10
    | exact resolve eq10 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq91 (k X1 (τ X0)) X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq91
    | exact resolve eq91 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq91 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq91
    | (have j0 := eq91 X1 X1
       grind)
    | exact resolve eq91 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq145 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq131 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq131
    | (have j0 := eq131 X0 X1
       grind)
    | exact resolve eq131 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq147 : ∀ X0 X1 X2 : G, (M.op (k (σ X0) X1) (k (σ X0) X1)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (k X2 (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq129 X0 X1 X2
       have i₂ := eq74 X0 X1
       grind)
    | exact superpose eq74 eq129
    | (have j0 := eq129 X0 X1 X2
       grind)
    | exact resolve eq129 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq151 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq145 X0 X1
       have j1 := eq76 X1 X0
       grind)
    | (have r₁ := eq145 X0 X0
       have r₂ := eq76 X0 X1
       grind)
    | exact resolve eq145 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq145
  have eq153 : ∀ X0 X1 X2 : G, (M.op (k (σ X0) X1) (k (σ X0) X1)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (σ (k X2 (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq147 X0 X1 X2
       have i₂ := eq74 X0 X1
       grind)
    | exact superpose eq74 eq147
    | (have j0 := eq147 X0 X1 X2
       grind)
    | exact resolve eq147 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq147
  have eq309 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq151 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq151
    | exact resolve eq151 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq318 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq151 X1 X0
       grind)
    | exact superpose eq151 eq22
    | (have j1 := eq151 X1 X0
       grind)
    | exact resolve eq22 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq319 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq151 (σ X1) X0
       grind)
    | exact superpose eq151 eq15
    | (have j1 := eq151 (σ X1) X0
       grind)
    | exact resolve eq15 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151
  have eq332 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq309 X0 X1
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq309
    | (have j0 := eq309 X0 X1
       grind)
    | exact resolve eq309 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309
  have eq350 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq332 X0 (τ X1)
       grind)
    | exact superpose eq332 eq17
    | (have j1 := eq332 X0 (τ X1)
       grind)
    | exact resolve eq17 eq332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq332
  have eq970 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq350 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq350
    | exact resolve eq350 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350
  have eq1015 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq970 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq970
    | (have j0 := eq970 X0 X1
       grind)
    | exact resolve eq970 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq970
  have eq1177 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (M.op X1 (M.op (σ X0) (σ (M.op X0 X0))))) X0) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq318 X0 (M.op X1 (M.op (σ X0) (σ (M.op X0 X0))))
       have i₂ := eq77 X0 X1
       grind)
    | exact superpose eq77 eq318
    | exact resolve eq318 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq318
  have eq1201 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k (τ (M.op X1 (M.op (σ X0) (σ (M.op X0 X0))))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1177 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1177
    | (have j0 := eq1177 X0 X1
       grind)
    | exact resolve eq1177 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1177
  have eq1253 : ∀ X0 X1 X2 : G, (k (σ X0) X1) ≠ (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (σ (k X2 (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq153 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq3503 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq319 x y
       grind)
    | exact superpose eq319 eq16
    | (have j1 := eq319 x y
       grind)
    | exact resolve eq16 eq319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3521 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq319 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319
  have eq3557 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq3503
       have i₂ := eq1015 y x
       grind)
    | exact superpose eq1015 eq3503
    | (have j1 := eq1015 y x
       grind)
    | (have r₁ := eq3503
       have r₂ := eq1015 y x
       grind)
    | exact resolve eq3503 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1015 eq3503
  have eq3558 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq3557
  have eq3561 : (M.op x x) ≠ (M.op x x) ∨ (k y x) = (M.op x x) ∨ x = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq3558
       grind)
    | exact superpose eq3558 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq3558
       grind)
    | exact resolve eq13 eq3558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3562 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ (k y x) = (M.op x x) := by grind
  clear eq3561
  have eq3697 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3521 (τ X1) (τ X0)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq3521
    | (have j0 := eq3521 (τ X1) (τ X0)
       grind)
    | exact resolve eq3521 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3748 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3697 X0 X1
       have i₂ := eq67 X1
       grind)
    | exact superpose eq67 eq3697
    | (have j0 := eq3697 X0 X1
       grind)
    | exact resolve eq3697 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3697
  have eq3769 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3748 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq3748
    | (have j0 := eq3748 X0 X1
       grind)
    | exact resolve eq3748 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3748
  have eq3783 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3769 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3769
    | (have j0 := eq3769 X0 X1
       grind)
    | exact resolve eq3769 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3769
  have eq3794 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X1))) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3783 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq3783
    | (have j0 := eq3783 X0 X1
       grind)
    | exact resolve eq3783 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3783
  have eq3799 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3794 X0 X1
       have i₂ := eq67 X1
       grind)
    | exact superpose eq67 eq3794
    | (have j0 := eq3794 X0 X1
       grind)
    | exact resolve eq3794 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3794
  have eq11128 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (τ X0)) ∨ (τ X0) = (k (τ (M.op X1 (M.op (σ (τ X0)) (M.op X0 X0)))) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1201 (τ X0) X1
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq1201
    | exact resolve eq1201 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq1201
  have eq11225 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (τ X0) = (k (τ (M.op X1 (M.op (σ (τ X0)) (M.op X0 X0)))) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11128 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq11128
    | (have j0 := eq11128 X0 X1
       grind)
    | exact resolve eq11128 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11128
  have eq11233 : ∀ X0 X1 : G, (τ X0) = (τ (k (M.op X1 (M.op (σ (τ X0)) (M.op X0 X0))) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11225 X0 X1
       have i₂ := eq31 X0 (M.op X1 (M.op (σ (τ X0)) (M.op X0 X0)))
       grind)
    | exact superpose eq31 eq11225
    | (have j0 := eq11225 X0 X1
       grind)
    | exact resolve eq11225 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq11225
  have eq11238 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (τ X0) = (τ (k (M.op X1 (M.op X0 (M.op X0 X0))) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11233 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq11233
    | (have j0 := eq11233 X0 X1
       grind)
    | exact resolve eq11233 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11233
  have eq11304 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = (M.op X0 X1) ∨ (τ X0) = (τ (k (M.op X2 (M.op X0 (M.op X0 X0))) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq11238 X0 X2
       grind)
    | exact superpose eq11238 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq11238 X0 X2
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq11238 X0 X1
       grind)
    | exact resolve eq12 eq11238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11238
  have eq11348 : ∀ X0 X1 X2 : G, (τ X0) = (τ (k (M.op X2 (M.op X0 (M.op X0 X0))) X0)) ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq11304 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11304
  have eq11646 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k (M.op X1 (M.op X0 (M.op X0 X0))) X0) ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 (k (M.op X1 (M.op X0 (M.op X0 X0))) X0)
       have i₂ := eq11348 X0 X2 X1
       grind)
    | exact superpose eq11348 eq11
    | (have j1 := eq11348 X0 X2 X2
       grind)
    | exact resolve eq11 eq11348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11348
  have eq11779 : ∀ X0 X1 X2 : G, (k (M.op X1 (M.op X0 (M.op X0 X0))) X0) = X0 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11646 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq11646
    | (have j0 := eq11646 X0 X1 X2
       grind)
    | exact resolve eq11646 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11646
  have eq11903 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X1 (M.op X1 X1)))) ≠ X1 ∨ (k (M.op X0 (M.op X1 (M.op X1 X1))) X1) = (M.op X1 (M.op X0 (M.op X1 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have j0 := eq11779 X1 X1 (M.op X0 (M.op X1 (M.op X1 X1)))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11779
  have eq11904 : ∀ X0 X1 : G, (k (M.op X0 (M.op X1 (M.op X1 X1))) X1) = (M.op X1 (M.op X0 (M.op X1 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have j0 := eq11903 X0 X1
       grind)
    | (have r₁ := eq11903 X1 X0
       have r₂ := eq9 X0 X1
       grind)
    | exact resolve eq11903 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11903
  have eq11942 : ∀ X0 X1 : G, (k (M.op X0 (M.op X1 (M.op X1 X1))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11904 X0 X1
       have i₂ := eq9 X1 X0
       grind)
    | exact superpose eq9 eq11904
    | exact resolve eq11904 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11904
  have eq12188 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (M.op X1 (M.op (τ X0) (M.op (τ X0) (τ X0))))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (M.op X1 (M.op (τ X0) (M.op (τ X0) (τ X0))))
       have i₂ := eq11942 X1 (τ X0)
       grind)
    | exact superpose eq11942 eq18
    | exact resolve eq18 eq11942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11942
  have eq12240 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (M.op X1 (M.op (τ X0) (τ (M.op X0 X0))))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12188 X0 X1
       have i₂ := eq101 X0
       grind)
    | exact superpose eq101 eq12188
    | exact resolve eq12188 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12188
  have eq12274 : ∀ X0 X1 : G, (k (σ (M.op X1 (M.op (τ X0) (τ (M.op X0 X0))))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12240 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq12240
    | exact resolve eq12240 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12240
  have eq12426 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (σ (M.op X1 (M.op (τ (τ X0)) (τ (M.op (τ X0) (τ X0))))))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (σ (M.op X1 (M.op (τ (τ X0)) (τ (M.op (τ X0) (τ X0))))))
       have i₂ := eq12274 (τ X0) X1
       grind)
    | exact superpose eq12274 eq18
    | exact resolve eq18 eq12274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12274
  have eq12481 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (σ (M.op X1 (M.op (τ (τ X0)) (τ (τ (M.op X0 X0))))))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12426 X0 X1
       have i₂ := eq101 X0
       grind)
    | exact superpose eq101 eq12426
    | exact resolve eq12426 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12426
  have eq12545 : ∀ X0 X1 : G, (k (σ (σ (M.op X1 (M.op (τ (τ X0)) (τ (τ (M.op X0 X0))))))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12481 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq12481
    | exact resolve eq12481 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12481
  have eq13577 : ∀ X0 X1 : G, (τ X0) = (k (σ (σ (M.op X1 (M.op (τ (τ (τ X0))) (τ (τ (τ (M.op X0 X0)))))))) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12545 (τ X0) X1
       have i₂ := eq101 X0
       grind)
    | exact superpose eq101 eq12545
    | exact resolve eq12545 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13667 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (σ (σ (M.op X1 (M.op (τ (τ (τ X0))) (τ (τ (M.op (τ X0) (τ X0))))))))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (σ (σ (M.op X1 (M.op (τ (τ (τ X0))) (τ (τ (M.op (τ X0) (τ X0))))))))
       have i₂ := eq12545 (τ X0) X1
       grind)
    | exact superpose eq12545 eq18
    | exact resolve eq18 eq12545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12545
  have eq13724 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (σ (σ (M.op X1 (M.op (τ (τ (τ X0))) (τ (τ (τ (M.op X0 X0))))))))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13667 X0 X1
       have i₂ := eq101 X0
       grind)
    | exact superpose eq101 eq13667
    | exact resolve eq13667 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq13667
  have eq13790 : ∀ X0 X1 : G, (k (σ (σ (σ (M.op X1 (M.op (τ (τ (τ X0))) (τ (τ (τ (M.op X0 X0))))))))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13724 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq13724
    | exact resolve eq13724 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13724
  have eq41734 : ∀ X0 X1 X2 : G, (M.op X0 (σ X2)) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 (σ X2)) = (σ (k X2 (k (σ (σ (M.op X1 (M.op (τ (τ (τ X0))) (τ (τ (τ (M.op X0 X0)))))))) (τ X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1253 (σ (σ (M.op X1 (M.op (τ (τ (τ X0))) (τ (τ (τ (M.op X0 X0)))))))) X0 X2
       have i₂ := eq13790 X0 X1
       grind)
    | exact superpose eq13790 eq1253
    | exact resolve eq1253 eq13790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1253 eq13790
  have eq41843 : ∀ X0 X2 : G, (M.op X0 (σ X2)) = (σ (k X2 (τ X0))) ∨ (M.op X0 (σ X2)) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq41734 X0 x X2
       have i₂ := eq13577 X0 x
       grind)
    | exact superpose eq13577 eq41734
    | (have j0 := eq41734 X0 x X2
       grind)
    | exact resolve eq41734 eq13577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13577 eq41734
  have eq41897 : ∀ X0 X2 : G, (M.op X0 (σ X2)) = (k (σ X2) X0) ∨ (M.op X0 (σ X2)) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq41843 X0 X2
       have i₂ := eq18 X0 X2
       grind)
    | exact superpose eq18 eq41843
    | (have j0 := eq41843 X0 X2
       grind)
    | exact resolve eq41843 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq41843
  have eq41931 : ∀ X0 X2 : G, (M.op X0 (σ X2)) ≠ X0 ∨ (M.op X0 (σ X2)) = (k (σ X2) X0) := by
    intro X0 X2
    first
    | (have j0 := eq41897 X0 X2
       have j1 := eq12 (σ X2) X0
       grind)
    | (have r₁ := eq41897 x X2
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq41897 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41897
  have eq41978 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq41931 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq41931
    | exact resolve eq41931 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41931
  have eq42109 : x ≠ (M.op x x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq41978 y x
       have i₂ := eq3558
       grind)
    | exact superpose eq3558 eq41978
    | (have j0 := eq41978 x x
       grind)
    | exact resolve eq41978 eq3558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3558
  have eq42142 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have r₁ := eq42109
       have r₂ := eq3562
       grind)
    | exact resolve eq42109 eq3562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3562 eq42109
  have eq42299 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq75 x (σ y)
       have i₂ := eq42142
       grind)
    | exact superpose eq42142 eq75
    | (have j0 := eq75 x (σ y)
       grind)
    | (have r₁ := eq75 x (σ y)
       have r₂ := eq42142
       grind)
    | exact resolve eq75 eq42142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42316 : (σ x) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq41978 (σ y) (σ x)
       have i₂ := eq42142
       grind)
    | exact superpose eq42142 eq41978
    | exact resolve eq41978 eq42142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42142
  have eq42317 : (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ (k y x) = (M.op x x) := by grind
  clear eq42299
  have eq42318 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ x) ≠ (σ (M.op x x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq42316
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq42316
    | exact resolve eq42316 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42316
  have eq42321 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq42317
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq42317
    | exact resolve eq42317 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42317
  have eq42323 : (k y x) = (M.op x x) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq42321
       have r₂ := eq42318
       grind)
    | exact resolve eq42321 eq42318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42318 eq42321
  have eq42501 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq3521 x y
       have i₂ := eq42323
       grind)
    | exact superpose eq42323 eq3521
    | (have j0 := eq3521 x y
       grind)
    | (have r₁ := eq3521 x y
       have r₂ := eq42323
       grind)
    | exact resolve eq3521 eq42323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42323
  have eq42530 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq42501
  have eq42539 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have j1 := eq3521 x y
       grind)
    | (have r₁ := eq42530
       have r₂ := eq3521 x y
       grind)
    | exact resolve eq42530 eq3521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3521 eq42530
  have eq42545 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq42539
       grind)
    | exact superpose eq42539 eq16
    | exact resolve eq16 eq42539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42546 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq75 x (σ y)
       have i₂ := eq42539
       grind)
    | exact superpose eq42539 eq75
    | (have j0 := eq75 x (σ y)
       grind)
    | (have r₁ := eq75 x (σ y)
       have r₂ := eq42539
       grind)
    | exact resolve eq75 eq42539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq42563 : (σ x) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq41978 (σ y) (σ x)
       have i₂ := eq42539
       grind)
    | exact superpose eq42539 eq41978
    | exact resolve eq41978 eq42539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41978 eq42539
  have eq42564 : (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq42546
  have eq42565 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq42563
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq42563
    | exact resolve eq42563 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42563
  have eq42568 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq42564
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq42564
    | exact resolve eq42564 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42564
  have eq42570 : (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq42568
       have r₂ := eq42565
       grind)
    | exact resolve eq42568 eq42565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42565 eq42568
  have eq42743 : (k y x) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq42570
       grind)
    | exact superpose eq42570 eq10
    | exact resolve eq10 eq42570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42570
  have eq42857 : (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq42743
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq42743
    | exact resolve eq42743 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42743
  have eq43046 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq3799 y x
       have i₂ := eq42857
       grind)
    | exact superpose eq42857 eq3799
    | (have j0 := eq3799 y x
       grind)
    | (have r₁ := eq3799 y x
       have r₂ := eq42857
       grind)
    | exact resolve eq3799 eq42857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3799 eq42857
  have eq43073 : (M.op x y) = (M.op x x) := by grind
  clear eq43046
  have eq43084 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq42545
       have i₂ := eq43073
       grind)
    | exact superpose eq43073 eq42545
    | exact resolve eq42545 eq43073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42545 eq43073
  have eq43093 : False := by grind
  exact eq43093

/-- `Equation426`: `x = x ◇ (y ◇ (x ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pyx_pxx_pyx_Equation426 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law426 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law426.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq62 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    grind
  have eq65 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq62 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq74 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq65 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq75 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq74 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq90 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq75 (σ X0)
       grind)
    | exact superpose eq75 eq15
    | exact resolve eq15 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq90 X0
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq90
    | exact resolve eq90 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq90
  have eq117 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq101 X0
       grind)
    | exact superpose eq101 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = X1 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq101 X0
       have i₂ := eq14 X1 (σ X0)
       grind)
    | exact superpose eq14 eq101
    | (have j1 := eq14 (σ X0) (σ (M.op X0 X0))
       grind)
    | exact resolve eq101 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq132 X0 X1
       have j1 := eq117 X0 X1
       grind)
    | (have r₁ := eq132 X0 X1
       have r₂ := eq117 X0 X1
       grind)
    | (have r₁ := eq132 X0 (σ (M.op X0 X0))
       have r₂ := eq117 X0 X1
       grind)
    | (have r₁ := eq132 (M.op X0 X0) (σ X0)
       have r₂ := eq117 X0 X1
       grind)
    | exact resolve eq132 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq132
  have eq164 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq142 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq142
    | exact resolve eq142 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq169 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq142 X0 (σ X1)
       grind)
    | exact superpose eq142 eq15
    | (have j1 := eq142 (k X1 X0) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq176 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq164 (τ X0) X1
       grind)
    | exact superpose eq164 eq19
    | (have j1 := eq164 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq164
  have eq264 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq176 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq176
    | exact resolve eq176 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq289 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq264 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq264
    | (have j0 := eq264 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq264 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264
  have eq965 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq169 x y
       grind)
    | exact superpose eq169 eq16
    | (have j1 := eq169 x y
       grind)
    | exact resolve eq16 eq169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq979 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq965
       have i₂ := eq289 x y
       grind)
    | exact superpose eq289 eq965
    | (have j1 := eq289 (σ x) (σ y)
       grind)
    | (have r₁ := eq965
       have r₂ := eq289 x y
       grind)
    | (have r₁ := eq965
       have r₂ := eq289 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq965
       have r₂ := eq289 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq965 eq289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289 eq965
  have eq980 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq979
  have eq982 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq980
       grind)
    | exact superpose eq980 eq16
    | exact resolve eq16 eq980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq980
  have eq983 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq982
       have r₂ := eq101 x
       grind)
    | exact resolve eq982 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq982
  have eq984 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq983
       grind)
    | exact superpose eq983 eq16
    | exact resolve eq16 eq983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq985 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq983
       grind)
    | exact superpose eq983 eq10
    | exact resolve eq10 eq983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq983
  have eq1029 : x = y := by
    first
    | (have i₁ := eq985
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq985
    | exact resolve eq985 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq985
  have eq1030 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq984
       have i₂ := eq101 x
       grind)
    | exact superpose eq101 eq984
    | exact resolve eq984 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq984
  have eq1031 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1030
       have i₂ := eq1029
       grind)
    | exact superpose eq1029 eq1030
    | exact resolve eq1030 eq1029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1029 eq1030
  have eq1032 : False := by grind
  exact eq1032

/-- `Equation426`: `x = x ◇ (y ◇ (x ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxy_pxx_pxy_Equation426 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law426 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law426.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
  have eq450 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (σ X1)) ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq28
    | (have j1 := eq14 X0 (σ X1)
       grind)
    | exact resolve eq28 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq451 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) ∨ (τ X1) = X0 := by
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
  have eq2982 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq451 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq451
    | exact resolve eq451 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451
  have eq3025 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 X0) ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2982 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2982
    | (have j0 := eq2982 X0 X1
       grind)
    | exact resolve eq2982 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2982
  have eq3049 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op (τ X0) X1)) ∨ (σ (k (τ X0) X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0
       have i₂ := eq3025 X1 (τ X0)
       grind)
    | (have i₁ := eq30 X0
       have i₂ := eq3025 (τ X0) (τ X0)
       grind)
    | exact superpose eq3025 eq30
    | (have j1 := eq3025 X1 (τ X0)
       grind)
    | exact resolve eq30 eq3025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq3054 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq3025 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq3025 X0 X1
       grind)
    | exact superpose eq3025 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq3025 X1 X0
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq3025 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq3025 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq3025 (M.op X0 X0) (M.op X0 X1)
       grind)
    | exact resolve eq13 eq3025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3025
  have eq3075 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3054 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3054
  have eq3076 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq3075 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3075
  have eq3089 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X0 X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3049 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq3049
    | (have j0 := eq3049 X0 X1
       grind)
    | exact resolve eq3049 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq3049
  have eq3167 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ (M.op X0 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq3076 X0 X1
       grind)
    | exact superpose eq3076 eq10
    | (have j1 := eq3076 X0 X1
       grind)
    | exact resolve eq10 eq3076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3076
  have eq3211 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3167 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq3167
    | (have j0 := eq3167 X0 X1
       grind)
    | exact resolve eq3167 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3167
  have eq3243 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3211 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3211
    | (have j0 := eq3211 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq3211 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3211
  have eq3401 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3243 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq3243
    | (have j0 := eq3243 X0 X1
       grind)
    | exact resolve eq3243 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3243
  have eq3545 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (k (τ (σ x)) y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq450 (σ x) y
       grind)
    | exact superpose eq450 eq16
    | (have j1 := eq450 (σ x) y
       grind)
    | (have r₁ := eq16
       have r₂ := eq450 (M.op (σ x) (σ y)) (M.op x y)
       grind)
    | exact resolve eq16 eq450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450
  have eq3558 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (k (τ (σ x)) y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3545
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq3545
    | exact resolve eq3545 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3545
  have eq3569 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3558
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3558
    | exact resolve eq3558 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3558
  have eq8638 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3089 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3089
    | exact resolve eq3089 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3089
  have eq8776 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8638 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq8638
    | (have j0 := eq8638 X0 X1
       grind)
    | exact resolve eq8638 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8638
  have eq8799 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8776 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq8776
    | (have j0 := eq8776 X0 X1
       grind)
    | exact resolve eq8776 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8776
  have eq19425 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3401 x y
       grind)
    | exact superpose eq3401 eq16
    | (have j1 := eq3401 x y
       grind)
    | exact resolve eq16 eq3401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3401
  have eq19531 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ x = y := by
    first
    | (have i₁ := eq19425
       have i₂ := eq8799 x y
       grind)
    | exact superpose eq8799 eq19425
    | (have j1 := eq8799 x y
       grind)
    | (have r₁ := eq19425
       have r₂ := eq8799 x y
       grind)
    | (have r₁ := eq19425
       have r₂ := eq8799 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq19425
       have r₂ := eq8799 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq19425 eq8799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8799 eq19425
  have eq19534 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq19531
  have eq19535 : x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by grind
  clear eq19534
  have eq19540 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19535
       grind)
    | exact superpose eq19535 eq16
    | exact resolve eq16 eq19535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19535
  have eq19541 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq19540
       have r₂ := eq22 x
       grind)
    | exact resolve eq19540 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19540
  have eq19543 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq19541
       grind)
    | exact superpose eq19541 eq10
    | exact resolve eq10 eq19541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19541
  have eq19618 : x = y ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq19543
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq19543
    | exact resolve eq19543 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19543
  have eq19620 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19618
       grind)
    | exact superpose eq19618 eq16
    | exact resolve eq16 eq19618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19618
  have eq19621 : (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq19620
       have r₂ := eq22 x
       grind)
    | exact resolve eq19620 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19620
  have eq19622 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3569
       have i₂ := eq19621
       grind)
    | exact superpose eq19621 eq3569
    | (have r₁ := eq3569
       have r₂ := eq19621
       grind)
    | exact resolve eq3569 eq19621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3569
  have eq19623 : (M.op x y) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq19621
       grind)
    | exact superpose eq19621 eq10
    | exact resolve eq10 eq19621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19677 : (σ x) = (σ y) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq19622
  have eq19699 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19623
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq19623
    | exact resolve eq19623 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19623
  have eq19703 : (M.op x x) ≠ (M.op x x) ∨ x = y ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq19699
       grind)
    | exact superpose eq19699 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq19699
       grind)
    | exact resolve eq13 eq19699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19699
  have eq19704 : x = y ∨ (k x y) = (M.op x x) := by grind
  clear eq19703
  have eq19706 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19704
       grind)
    | exact superpose eq19704 eq16
    | exact resolve eq16 eq19704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19704
  have eq19707 : (k x y) = (M.op x x) := by
    first
    | (have r₁ := eq19706
       have r₂ := eq22 x
       grind)
    | exact resolve eq19706 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19706
  have eq20617 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19677
       grind)
    | exact superpose eq19677 eq16
    | exact resolve eq16 eq19677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19677
  have eq20723 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq20617
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq20617
    | exact resolve eq20617 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq20617
  have eq20746 : (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq20723
       have r₂ := eq19621
       grind)
    | exact resolve eq20723 eq19621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20723
  have eq20747 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq20746
       have i₂ := eq19707
       grind)
    | exact superpose eq19707 eq20746
    | exact resolve eq20746 eq19707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19707 eq20746
  have eq20766 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq11 (M.op (σ x) (σ y))
       have i₂ := eq20747
       grind)
    | exact superpose eq20747 eq11
    | exact resolve eq11 eq20747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20747
  have eq20890 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20766
       grind)
    | exact superpose eq20766 eq16
    | exact resolve eq16 eq20766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20766
  have eq20910 : False := by grind
  exact eq20910

/-- `Equation426`: `x = x ◇ (y ◇ (x ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxy_pxx_pyx_Equation426 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law426 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law426.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq45 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq28
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq187 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (σ X0) = X1 ∨ (σ (M.op X0 X0)) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq13
    | (have j0 := eq13 (σ X0) X1
       grind)
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq385 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq408 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq385 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq385
    | (have j0 := eq385 X0 X1
       grind)
    | exact resolve eq385 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385
  have eq512 : ∀ X0 X1 : G, (M.op (σ (σ X1)) (σ (σ X0))) = (σ (σ (k X0 X1))) ∨ (σ (M.op (σ X0) (σ X0))) = (M.op (σ (σ X1)) (σ (σ X0))) ∨ (σ (σ X0)) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq408 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq408
    | (have j0 := eq408 (σ X1) (σ X0)
       grind)
    | exact resolve eq408 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408
  have eq555 : ∀ X0 X1 : G, (σ (σ (M.op X0 X0))) = (M.op (σ (σ X1)) (σ (σ X0))) ∨ (M.op (σ (σ X1)) (σ (σ X0))) = (σ (σ (k X0 X1))) ∨ (σ (σ X0)) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq512 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq512
    | (have j0 := eq512 X0 X1
       grind)
    | exact resolve eq512 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512
  have eq34485 : ∀ X0 X1 : G, (σ (M.op (σ X0) (σ X0))) ≠ (σ (σ (M.op X0 X0))) ∨ (σ (σ X0)) = (σ (σ X1)) ∨ (σ (M.op (σ X0) (σ X0))) = (k (σ (σ X0)) (σ (σ X1))) ∨ (M.op (σ (σ X1)) (σ (σ X0))) = (σ (σ (k X0 X1))) ∨ (σ (σ X0)) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq187 (σ X0) (σ (σ X1))
       have i₂ := eq555 X0 X1
       grind)
    | exact superpose eq555 eq187
    | (have j0 := eq187 (σ X0) (σ (σ X1))
       have j1 := eq555 X0 X1
       grind)
    | exact resolve eq187 eq555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq34487 : ∀ X0 X1 : G, (σ (σ (M.op X1 X1))) ≠ (σ (σ (k X1 X0))) ∨ (σ (σ (k X1 X0))) = (M.op (σ (σ X0)) (σ (σ X1))) ∨ (σ (σ X0)) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq555 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555
  have eq34489 : ∀ X0 X1 : G, (σ (M.op (σ X0) (σ X0))) ≠ (σ (σ (M.op X0 X0))) ∨ (σ (σ X0)) = (σ (σ X1)) ∨ (σ (M.op (σ X0) (σ X0))) = (k (σ (σ X0)) (σ (σ X1))) ∨ (M.op (σ (σ X1)) (σ (σ X0))) = (σ (σ (k X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq34485 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34485
  have eq34500 : ∀ X0 X1 : G, (σ (σ (M.op X0 X0))) ≠ (σ (σ (M.op X0 X0))) ∨ (σ (σ X0)) = (σ (σ X1)) ∨ (σ (M.op (σ X0) (σ X0))) = (k (σ (σ X0)) (σ (σ X1))) ∨ (M.op (σ (σ X1)) (σ (σ X0))) = (σ (σ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq34489 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq34489
    | (have j0 := eq34489 X0 X1
       grind)
    | exact resolve eq34489 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34489
  have eq34501 : ∀ X0 X1 : G, (σ (σ X0)) = (σ (σ X1)) ∨ (σ (M.op (σ X0) (σ X0))) = (k (σ (σ X0)) (σ (σ X1))) ∨ (M.op (σ (σ X1)) (σ (σ X0))) = (σ (σ (k X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq34500 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34500
  have eq34558 : ∀ X0 X1 : G, (σ (M.op (σ X0) (σ X0))) = (σ (k (σ X0) (σ X1))) ∨ (σ (σ X0)) = (σ (σ X1)) ∨ (M.op (σ (σ X1)) (σ (σ X0))) = (σ (σ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq34501 X0 X1
       have i₂ := eq15 (σ X0) (σ X1)
       grind)
    | exact superpose eq15 eq34501
    | (have j0 := eq34501 X0 X1
       grind)
    | exact resolve eq34501 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34501
  have eq34585 : ∀ X0 X1 : G, (σ (M.op (σ X0) (σ X0))) = (σ (σ (k X0 X1))) ∨ (σ (σ X0)) = (σ (σ X1)) ∨ (M.op (σ (σ X1)) (σ (σ X0))) = (σ (σ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq34558 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq34558
    | (have j0 := eq34558 X0 X1
       grind)
    | exact resolve eq34558 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34558
  have eq34598 : ∀ X0 X1 : G, (σ (σ (M.op X0 X0))) = (σ (σ (k X0 X1))) ∨ (σ (σ X0)) = (σ (σ X1)) ∨ (M.op (σ (σ X1)) (σ (σ X0))) = (σ (σ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq34585 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq34585
    | (have j0 := eq34585 X0 X1
       grind)
    | exact resolve eq34585 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34585
  have eq98908 : ∀ X0 X1 : G, (M.op (σ (σ X1)) (σ (σ X0))) = (σ (σ (k X0 X1))) ∨ (σ (σ X0)) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq34598 X0 X1
       have j1 := eq34487 X1 X0
       grind)
    | (have r₁ := eq34598 X1 X0
       have r₂ := eq34487 X0 X1
       grind)
    | (have r₁ := eq34598 (M.op X1 X1) (k X1 X0)
       have r₂ := eq34487 X0 X1
       grind)
    | (have r₁ := eq34598 (k X1 X0) (M.op X1 X1)
       have r₂ := eq34487 X0 X1
       grind)
    | exact resolve eq34598 eq34487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34487 eq34598
  have eq99017 : ∀ X0 X1 : G, (σ (σ (k (τ X0) X1))) = (M.op (σ (σ X1)) (σ X0)) ∨ (σ X0) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq98908 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq98908
    | exact resolve eq98908 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98908
  have eq99154 : ∀ X0 X1 : G, (σ (k X0 (σ X1))) = (M.op (σ (σ X1)) (σ X0)) ∨ (σ X0) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq99017 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq99017
    | (have j0 := eq99017 X0 X1
       grind)
    | exact resolve eq99017 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq99017
  have eq99191 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq99154 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq99154
    | exact resolve eq99154 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99154
  have eq99754 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq99191 (τ X1) (τ X0)
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq99191
    | (have j0 := eq99191 (τ X0) (τ X1)
       grind)
    | exact resolve eq99191 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq100325 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq99754 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq99754
    | (have j0 := eq99754 X0 X1
       grind)
    | exact resolve eq99754 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99754
  have eq100558 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq100325 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq100325
    | (have j0 := eq100325 X0 X1
       grind)
    | exact resolve eq100325 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100325
  have eq100771 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq100558 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq100558
    | (have j0 := eq100558 X0 X1
       grind)
    | exact resolve eq100558 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100558
  have eq100983 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq100771 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq100771
    | (have j0 := eq100771 X0 X1
       grind)
    | exact resolve eq100771 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100771
  have eq101045 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq100983 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq100983
    | (have j0 := eq100983 X0 X1
       grind)
    | exact resolve eq100983 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100983
  have eq101235 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq99191 X0 X1
       have i₂ := eq101045 X1 X0
       grind)
    | exact superpose eq101045 eq99191
    | (have j0 := eq99191 X0 X1
       have j1 := eq101045 (M.op (σ X0) (σ X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq99191 eq101045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99191 eq101045
  have eq104168 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq101235 x y
       grind)
    | exact superpose eq101235 eq16
    | (have j1 := eq101235 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq101235 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq101235 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq101235 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq101235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101235
  have eq104197 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq104168
  have eq104223 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq104197
       grind)
    | exact superpose eq104197 eq10
    | exact resolve eq10 eq104197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104197
  have eq104396 : x = y ∨ x = y := by
    first
    | (have i₁ := eq104223
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq104223
    | exact resolve eq104223 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104223
  have eq104397 : x = y := by grind
  clear eq104396
  have eq104400 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq104397
       grind)
    | exact superpose eq104397 eq16
    | exact resolve eq16 eq104397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104397
  have eq104401 : False := by grind
  exact eq104401

/-- `Equation426`: `x = x ◇ (y ◇ (x ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pxy_pyx_Equation426 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law426 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law426.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq45 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq28
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq441 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op X1 (σ X0)) ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 X0
       have i₂ := eq14 X1 (σ X0)
       grind)
    | exact superpose eq14 eq28
    | (have j1 := eq14 (σ X0) X1
       grind)
    | exact resolve eq28 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3033 : ∀ X0 X1 : G, (M.op (σ X0) X1) ≠ (M.op (σ X0) X1) ∨ (σ X0) = X1 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq441 X0 X1
       grind)
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq441 X0 X1
       grind)
    | exact superpose eq441 eq13
    | (have j0 := eq13 (σ X0) X1
       have j1 := eq441 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) X1
       have r₂ := eq441 X0 X1
       grind)
    | (have r₁ := eq13 X1 (σ X0)
       have r₂ := eq441 X0 X1
       grind)
    | exact resolve eq13 eq441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441
  have eq3034 : ∀ X0 X1 : G, (M.op (σ X0) X1) ≠ (M.op (σ X0) X1) ∨ (σ X0) = X1 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3033 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3033
  have eq3035 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3034 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3034
  have eq3987 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 X0
       have i₂ := eq3035 X0 X1
       grind)
    | exact superpose eq3035 eq28
    | (have j1 := eq3035 X0 X1
       grind)
    | exact resolve eq28 eq3035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq3035
  have eq4022 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq3987 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3987
  have eq4041 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4022 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4022
    | exact resolve eq4022 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4022
  have eq4150 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4041 X0 X1
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq4041
    | (have j0 := eq4041 (τ (k X1 X0)) (τ (M.op X0 X1))
       grind)
    | exact resolve eq4041 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq4041
  have eq4185 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq4150 X0 X1
       grind)
    | exact superpose eq4150 eq11
    | (have j1 := eq4150 (k X1 X0) (σ (τ (M.op X0 X1)))
       grind)
    | exact resolve eq11 eq4150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4150
  have eq4304 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4185 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq4185
    | (have j0 := eq4185 (M.op X0 X1) (k X1 X0)
       grind)
    | exact resolve eq4185 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4185
  have eq4334 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq4304 (τ X0) X1
       grind)
    | exact superpose eq4304 eq19
    | (have j1 := eq4304 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq4304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq4356 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq4304 (σ X0) (σ X1)
       grind)
    | exact superpose eq4304 eq15
    | (have j1 := eq4304 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq4304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4304
  have eq4594 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4334 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4334
    | exact resolve eq4334 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4334
  have eq4663 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4594 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq4594
    | (have j0 := eq4594 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq4594 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4594
  have eq5041 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4356 x y
       grind)
    | exact superpose eq4356 eq16
    | (have j1 := eq4356 x y
       grind)
    | exact resolve eq16 eq4356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4356
  have eq5084 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq5041
       have i₂ := eq4663 x y
       grind)
    | exact superpose eq4663 eq5041
    | (have j1 := eq4663 (σ x) (σ y)
       grind)
    | (have r₁ := eq5041
       have r₂ := eq4663 x y
       grind)
    | (have r₁ := eq5041
       have r₂ := eq4663 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq5041
       have r₂ := eq4663 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq5041 eq4663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4663 eq5041
  have eq5087 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq5084
  have eq5090 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5087
       grind)
    | exact superpose eq5087 eq16
    | exact resolve eq16 eq5087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5087
  have eq5091 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq5090
       have r₂ := eq22 x
       grind)
    | exact resolve eq5090 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5090
  have eq5092 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5091
       grind)
    | exact superpose eq5091 eq16
    | exact resolve eq16 eq5091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5093 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq5091
       grind)
    | exact superpose eq5091 eq10
    | exact resolve eq10 eq5091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5091
  have eq5147 : x = y := by
    first
    | (have i₁ := eq5093
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5093
    | exact resolve eq5093 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5093
  have eq5148 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5092
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq5092
    | exact resolve eq5092 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5092
  have eq5149 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5148
       have i₂ := eq5147
       grind)
    | exact superpose eq5147 eq5148
    | exact resolve eq5148 eq5147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5147 eq5148
  have eq5150 : False := by grind
  exact eq5150

/-- `Equation426`: `x = x ◇ (y ◇ (x ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pyx_pxy_Equation426 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law426 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law426.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq45 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq28
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq441 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = (M.op (σ X1) X0) ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq28
    | (have j1 := eq14 X0 (σ X1)
       grind)
    | exact resolve eq28 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3027 : ∀ X0 X1 : G, (M.op X0 (σ X1)) ≠ (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) X0
       have i₂ := eq441 X0 X1
       grind)
    | (have i₁ := eq13 X0 (σ X1)
       have i₂ := eq441 X0 X1
       grind)
    | exact superpose eq441 eq13
    | (have j0 := eq13 (σ X1) X0
       have j1 := eq441 X0 X1
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq441 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) X0
       have r₂ := eq441 X0 X1
       grind)
    | exact resolve eq13 eq441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441
  have eq3036 : ∀ X0 X1 : G, (M.op X0 (σ X1)) ≠ (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq3027 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3027
  have eq3037 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq3036 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3036
  have eq4417 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq3037 X0 X1
       grind)
    | exact superpose eq3037 eq28
    | (have j1 := eq3037 X0 X1
       grind)
    | exact resolve eq28 eq3037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq3037
  have eq4454 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq4417 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4417
  have eq4470 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4454 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4454
    | exact resolve eq4454 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4454
  have eq4571 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4470 X0 X1
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq4470
    | (have j0 := eq4470 (τ (k X1 X0)) (τ (M.op X1 X0))
       grind)
    | exact resolve eq4470 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq4470
  have eq4605 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq4571 X1 X0
       grind)
    | exact superpose eq4571 eq11
    | (have j1 := eq4571 (k X0 X1) (σ (τ (M.op X0 X1)))
       grind)
    | exact resolve eq11 eq4571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4571
  have eq4725 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4605 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq4605
    | (have j0 := eq4605 (k X0 X1) (M.op X0 X1)
       grind)
    | exact resolve eq4605 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4605
  have eq4756 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq4725 X0 (τ X1)
       grind)
    | exact superpose eq4725 eq19
    | (have j1 := eq4725 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq4725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq4778 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq4725 (σ X0) (σ X1)
       grind)
    | exact superpose eq4725 eq15
    | (have j1 := eq4725 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq4725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4725
  have eq5033 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4756 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4756
    | exact resolve eq4756 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4756
  have eq5098 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5033 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq5033
    | (have j0 := eq5033 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq5033 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5033
  have eq5487 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4778 x y
       grind)
    | exact superpose eq4778 eq16
    | (have j1 := eq4778 x y
       grind)
    | exact resolve eq16 eq4778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4778
  have eq5531 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq5487
       have i₂ := eq5098 y x
       grind)
    | exact superpose eq5098 eq5487
    | (have j1 := eq5098 (σ x) (σ y)
       grind)
    | (have r₁ := eq5487
       have r₂ := eq5098 y x
       grind)
    | (have r₁ := eq5487
       have r₂ := eq5098 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq5487
       have r₂ := eq5098 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq5487 eq5098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5098 eq5487
  have eq5534 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq5531
  have eq5538 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5534
       grind)
    | exact superpose eq5534 eq16
    | exact resolve eq16 eq5534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5534
  have eq5539 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq5538
       have r₂ := eq22 x
       grind)
    | exact resolve eq5538 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5538
  have eq5540 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5539
       grind)
    | exact superpose eq5539 eq16
    | exact resolve eq16 eq5539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5541 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq5539
       grind)
    | exact superpose eq5539 eq10
    | exact resolve eq10 eq5539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5539
  have eq5596 : x = y := by
    first
    | (have i₁ := eq5541
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5541
    | exact resolve eq5541 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5541
  have eq5597 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5540
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq5540
    | exact resolve eq5540 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5540
  have eq5598 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5597
       have i₂ := eq5596
       grind)
    | exact superpose eq5596 eq5597
    | exact resolve eq5597 eq5596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5596 eq5597
  have eq5599 : False := by grind
  exact eq5599

/-- `Equation426`: `x = x ◇ (y ◇ (x ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxx_x_pyx_Equation426 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law426 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law426.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
  have eq112 : ∀ X0 X1 : G, (M.op (τ X0) X1) = X1 ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
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
  have eq113 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq600 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (τ X1) = X0 ∨ (k X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op (τ X1) X0)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (τ X1)
       have i₂ := eq112 X1 X0
       grind)
    | exact superpose eq112 eq13
    | (have j0 := eq13 (τ X1) X0
       have j1 := eq112 X1 X0
       grind)
    | (have r₁ := eq13 X1 (τ X0)
       have r₂ := eq112 X0 X1
       grind)
    | (have r₁ := eq13 (τ X0) X1
       have r₂ := eq112 X0 (M.op X1 (τ X0))
       grind)
    | exact resolve eq13 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq601 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (τ X1) = X0 ∨ (k X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq600 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600
  have eq602 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op (τ X1) X0)) ∨ (k X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq601 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601
  have eq779 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq113 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq2104 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq602 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq602
    | exact resolve eq602 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602
  have eq2153 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2104 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2104
    | (have j0 := eq2104 X0 X1
       grind)
    | exact resolve eq2104 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2104
  have eq2192 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X1))) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq2153 X0 X1
       grind)
    | exact superpose eq2153 eq10
    | (have j1 := eq2153 X0 X1
       grind)
    | exact resolve eq10 eq2153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2234 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2192 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq2192
    | (have j0 := eq2192 X0 X1
       grind)
    | exact resolve eq2192 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2192
  have eq2249 : ∀ X0 X1 : G, (k X1 (σ X0)) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 X0
       have i₂ := eq2234 (σ X0) X1
       grind)
    | exact superpose eq2234 eq28
    | (have j1 := eq2234 (σ X0) X1
       grind)
    | exact resolve eq28 eq2234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2234
  have eq3921 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 (σ X1)
       have i₂ := eq2249 X1 (σ X0)
       grind)
    | exact superpose eq2249 eq37
    | (have j1 := eq2249 X1 (σ X0)
       grind)
    | exact resolve eq37 eq2249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq2249
  have eq3986 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3921 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq3921
    | (have j0 := eq3921 X0 X1
       grind)
    | exact resolve eq3921 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3921
  have eq4018 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3986 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3986
    | (have j0 := eq3986 X0 X1
       grind)
    | exact resolve eq3986 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3986
  have eq4028 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X1) (σ X0))) ∨ (k X0 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4018 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4018
    | (have j0 := eq4018 X0 X1
       grind)
    | exact resolve eq4018 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4018
  have eq4255 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (k X0 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X1) (σ X0))
       have i₂ := eq4028 X0 X1
       grind)
    | exact superpose eq4028 eq11
    | (have j1 := eq4028 X0 X1
       grind)
    | exact resolve eq11 eq4028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4028
  have eq5116 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4255 y x
       grind)
    | exact superpose eq4255 eq16
    | (have j1 := eq4255 y x
       grind)
    | exact resolve eq16 eq4255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4255
  have eq5142 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq5116
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq5116
    | (have j1 := eq14 y x
       grind)
    | (have r₁ := eq5116
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq5116
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq5116 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5143 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k y x) ∨ (σ x) = (σ y) ∨ y = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq5116
       have i₂ := eq2153 x y
       grind)
    | exact superpose eq2153 eq5116
    | (have j1 := eq2153 x y
       grind)
    | (have r₁ := eq5116
       have r₂ := eq2153 x y
       grind)
    | (have r₁ := eq5116
       have r₂ := eq2153 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq5116
       have r₂ := eq2153 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq5116 eq2153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2153 eq5116
  have eq5146 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5143
  have eq5147 : x = y ∨ (σ x) = (σ y) ∨ y = (k y x) := by grind
  clear eq5146
  have eq5148 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5142
  have eq5149 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5148
  have eq5153 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5147
       grind)
    | exact superpose eq5147 eq16
    | exact resolve eq16 eq5147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5147
  have eq5154 : y = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq5153
       have r₂ := eq22 x
       grind)
    | exact resolve eq5153 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5153
  have eq5160 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq779 x y
       have i₂ := eq5154
       grind)
    | exact superpose eq5154 eq779
    | (have j0 := eq779 x y
       grind)
    | exact resolve eq779 eq5154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779 eq5154
  have eq5165 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq5160
  have eq5166 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq5165
  have eq5178 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5166
       grind)
    | exact superpose eq5166 eq16
    | exact resolve eq16 eq5166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5166
  have eq5194 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq5178
       have i₂ := eq5149
       grind)
    | exact superpose eq5149 eq5178
    | exact resolve eq5178 eq5149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5149 eq5178
  have eq5195 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5194
  have eq5196 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq5195
  have eq5197 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5196
       grind)
    | exact superpose eq5196 eq16
    | exact resolve eq16 eq5196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5196
  have eq5198 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq5197
       have r₂ := eq22 x
       grind)
    | exact resolve eq5197 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5197
  have eq5199 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5198
       grind)
    | exact superpose eq5198 eq16
    | exact resolve eq16 eq5198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5200 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq5198
       grind)
    | exact superpose eq5198 eq10
    | exact resolve eq10 eq5198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5198
  have eq5252 : x = y := by
    first
    | (have i₁ := eq5200
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5200
    | exact resolve eq5200 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5200
  have eq5253 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5199
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq5199
    | exact resolve eq5199 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5199
  have eq5254 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5253
       have i₂ := eq5252
       grind)
    | exact superpose eq5252 eq5253
    | exact resolve eq5253 eq5252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5252 eq5253
  have eq5255 : False := by grind
  exact eq5255

/-- `Equation4294`: `x ◇ (x ◇ y) = y ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then Y else if m(X,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_y_y_pxx_pxy_Equation4294 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4294 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4294.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X1 (M.op X1 X2)) := by
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
  clear eq36
  have eq72 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 y)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq15
    | exact resolve eq15 eq40
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
  have eq152 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq72 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq72
    | exact resolve eq72 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq174 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 : G, (M.op X0 (M.op X0 x)) = (M.op x (M.op x y)) := by
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
  have eq180 : ∀ X0 : G, (M.op X0 (M.op X0 (σ x))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X3)) = (M.op X3 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X2 X3 (M.op X3 X0)
       have i₂ := eq16 X3 X0 X1
       grind)
    | (have i₁ := eq16 X0 X1 (M.op X1 X2)
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : (σ (M.op (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq37 (M.op sF0 sF0)
       have i₂ := eq174 sF0
       grind)
    | exact superpose eq174 eq37
    | exact resolve eq37 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq190 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 x
       have i₂ := eq179 X1
       grind)
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X1 (M.op x (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 (M.op X1 x)
       have i₂ := eq179 X1
       grind)
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : ∀ X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ x) X1)) := by
    intro X1
    first
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq198 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X1 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq201 : ∀ X1 : G, (M.op x (M.op x y)) = (M.op X1 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X1
    first
    | (have i₁ := eq198 x X1
       have i₂ := eq190 x X1
       grind)
    | (have i₁ := eq198 x y
       have i₂ := eq190 x X1
       grind)
    | exact superpose eq190 eq198
    | exact resolve eq198 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq202 : (M.op x (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq197 x
       have i₂ := eq190 sF2 x
       grind)
    | exact superpose eq190 eq197
    | (have j1 := eq190 (σ x) (σ y)
       grind)
    | exact resolve eq197 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq212 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq190 X0 (M.op X0 x)
       have i₂ := eq179 X0
       grind)
    | exact superpose eq179 eq190
    | exact resolve eq190 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq223 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq202 eq212
    | exact resolve eq212 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq287 : (M.op x (M.op x y)) = (k (M.op (σ x) (M.op (σ x) (σ y))) (M.op x (M.op x y))) := by
    first
    | exact superpose eq201 eq174
    | exact resolve eq174 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq297 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq202 eq287
    | exact resolve eq287 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287
  have eq300 : (τ (M.op (σ x) (σ x))) = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq90 (M.op sF2 sF2)
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq90
    | exact resolve eq90 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq311 : (τ (M.op (σ y) (σ y))) = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | (have i₁ := eq107 (M.op sF3 sF3)
       have i₂ := eq174 sF3
       grind)
    | exact superpose eq174 eq107
    | exact resolve eq107 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq174
  have eq1166 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1169 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1223 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1224 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1225 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1224 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1224
  have eq1803 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1166
       grind)
    | exact superpose eq1166 eq40
    | exact resolve eq40 eq1166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq1804 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1803
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1803
    | exact resolve eq1803 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1803
  have eq1806 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq1804
    | exact resolve eq1804 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1804
  have eq1814 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1806 eq1169
    | exact resolve eq1169 eq1806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1806
  have eq1821 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq1814
       have r₂ := eq27
       grind)
    | exact resolve eq1814 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1814
  have eq1826 : (τ (σ y)) = (k x (τ (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1821 eq300
    | exact resolve eq300 eq1821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300 eq1821
  have eq1849 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq31 eq1826
    | exact resolve eq1826 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1826
  have eq1856 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq1849
       have r₂ := eq13 x y
       grind)
    | exact resolve eq1849 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1849
  have eq1863 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1166
       have i₂ := eq1856
       grind)
    | exact superpose eq1856 eq1166
    | exact resolve eq1166 eq1856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1166
  have eq1864 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq35 y
       have i₂ := eq1856
       grind)
    | exact superpose eq1856 eq35
    | exact resolve eq35 eq1856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq1856
  have eq1866 : y = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1863
  have eq1869 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1864
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1864
    | exact resolve eq1864 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1864
  have eq1881 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X1 (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq182 x x X0 X1
       have i₂ := eq1866
       grind)
    | exact superpose eq1866 eq182
    | exact resolve eq182 eq1866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1886 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq196 x x
       have i₂ := eq1866
       grind)
    | exact superpose eq1866 eq196
    | exact resolve eq196 eq1866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1866
  have eq1889 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1886
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1886
    | exact resolve eq1886 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1886
  have eq1894 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X1 (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq1881 X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1881
    | (have j0 := eq1881 X0 X1
       grind)
    | exact resolve eq1881 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1881
  have eq1904 : ∀ X1 : G, (M.op x (M.op x y)) = (M.op X1 (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | (have i₁ := eq1894 x X1
       have i₂ := eq190 x X1
       grind)
    | (have i₁ := eq1894 x y
       have i₂ := eq190 x X1
       grind)
    | exact superpose eq190 eq1894
    | exact resolve eq1894 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1894
  have eq1912 : ∀ X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X1 (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | exact superpose eq202 eq1904
    | exact resolve eq1904 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1904
  have eq1915 : ∀ X1 : G, (M.op x y) = (M.op X1 (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | exact superpose eq1889 eq1912
    | exact resolve eq1912 eq1889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1912
  have eq1919 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1869 eq1169
    | exact resolve eq1169 eq1869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1169 eq1869
  have eq1923 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1919
  have eq1989 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1915 eq187
    | exact resolve eq187 eq1915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1915
  have eq1991 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1989
    | exact resolve eq1989 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1989
  have eq2039 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1923 eq196
    | exact resolve eq196 eq1923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1923
  have eq2042 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq2039
    | exact resolve eq2039 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2039
  have eq2051 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1889 eq2042
    | exact resolve eq2042 eq1889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2042
  have eq2075 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2051 eq297
    | exact resolve eq297 eq2051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297
  have eq2076 : (M.op x y) ≠ (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  have eq2077 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq2075
    | exact resolve eq2075 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2075
  have eq2082 : (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2051 eq2077
    | exact resolve eq2077 eq2051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2077
  have eq2106 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1991 eq1225
    | (have j0 := eq1225 (σ (M.op x y))
       grind)
    | (have r₁ := eq1225 (σ (M.op x y))
       have r₂ := eq1991
       grind)
    | exact resolve eq1225 eq1991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1991
  have eq2107 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2106
  have eq2113 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2082 eq152
    | exact resolve eq152 eq2082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq2082
  have eq2116 : y = (k y y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq2113
    | exact resolve eq2113 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2113
  have eq2189 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2107 eq196
    | exact resolve eq196 eq2107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2191 : (M.op x y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1889 eq2189
    | exact resolve eq2189 eq1889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1889 eq2189
  have eq2218 : y ≠ y ∨ y = (M.op y y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1225 y
       have i₂ := eq2116
       grind)
    | exact superpose eq2116 eq1225
    | (have j0 := eq1225 y
       grind)
    | (have r₁ := eq1225 y
       have r₂ := eq2116
       grind)
    | exact resolve eq1225 eq2116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1225 eq2116
  have eq2219 : y = (M.op y y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2218
  have eq2224 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2191 eq2107
    | exact resolve eq2107 eq2191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2107 eq2191
  have eq2239 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq2224
  have eq2268 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq2239 eq223
    | exact resolve eq223 eq2239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq2273 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq26 eq2268
    | (have j0 := eq2268 X0
       grind)
    | exact resolve eq2268 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2268
  have eq2278 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq2239 eq2273
    | exact resolve eq2273 eq2239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2273
  have eq2348 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X1 (M.op y y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq182 y y X0 X1
       have i₂ := eq2219
       grind)
    | exact superpose eq2219 eq182
    | exact resolve eq182 eq2219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq2360 : ∀ X1 : G, (M.op x (M.op x y)) = (M.op X1 (M.op y y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X1
    first
    | (have i₁ := eq2348 x X1
       have i₂ := eq190 x X1
       grind)
    | (have i₁ := eq2348 x y
       have i₂ := eq190 x X1
       grind)
    | exact superpose eq190 eq2348
    | exact resolve eq2348 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190 eq2348
  have eq2370 : ∀ X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X1 (M.op y y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X1
    first
    | exact superpose eq202 eq2360
    | exact resolve eq2360 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2360
  have eq2378 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op X1 (M.op y y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X1
    first
    | exact superpose eq2051 eq2370
    | exact resolve eq2370 eq2051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2370
  have eq2385 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op X1 (M.op y y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X1
    first
    | exact superpose eq26 eq2378
    | (have j0 := eq2378 X1
       grind)
    | exact resolve eq2378 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2378
  have eq2391 : ∀ X1 : G, (σ y) = (M.op X1 (M.op y y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X1
    first
    | exact superpose eq2051 eq2385
    | exact resolve eq2385 eq2051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2051 eq2385
  have eq2395 : ∀ X1 : G, (σ y) = (M.op X1 y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X1
    first
    | exact superpose eq2219 eq2391
    | exact resolve eq2391 eq2219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2219 eq2391
  have eq2663 : (M.op x y) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq2395 x
       grind)
    | (have i₁ := eq18
       have i₂ := eq2395 x
       grind)
    | exact superpose eq2395 eq18
    | (have j1 := eq2395 x
       grind)
    | exact resolve eq18 eq2395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2395
  have eq2670 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq2663
       have r₂ := eq2076
       grind)
    | exact resolve eq2663 eq2076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2076 eq2663
  have eq2686 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2670 eq27
    | exact resolve eq27 eq2670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2693 : (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2670 eq2239
    | exact resolve eq2239 eq2670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2239
  have eq2694 : (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq2693
  have eq2705 : y = (τ (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq2694 eq31
    | exact resolve eq31 eq2694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq2716 : (τ (M.op (M.op x y) (M.op x y))) = (k y (τ (M.op (M.op x y) (M.op x y)))) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq2694 eq311
    | exact resolve eq311 eq2694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311
  have eq2724 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq2694 eq2278
    | exact resolve eq2278 eq2694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2278 eq2694
  have eq2725 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq2724 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2724
  have eq2733 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq2725 X0
       grind)
    | (have r₁ := eq2725 X0
       have r₂ := eq2686
       grind)
    | exact resolve eq2725 eq2686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2725
  have eq2736 : (τ (M.op (M.op x y) (M.op x y))) = (k y (τ (M.op (M.op x y) (M.op x y)))) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq2716
       have r₂ := eq2686
       grind)
    | exact resolve eq2716 eq2686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2716
  have eq2747 : y = (τ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq2705
       have r₂ := eq2686
       grind)
    | exact resolve eq2705 eq2686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2686 eq2705
  have eq2749 : (τ (M.op x y)) = (k y (τ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2733 eq2736
    | exact resolve eq2736 eq2733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2736
  have eq2758 : y = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2747 eq2749
    | exact resolve eq2749 eq2747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2747 eq2749
  have eq2890 : y ≠ y ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1223 y y
       have i₂ := eq2758
       grind)
    | exact superpose eq2758 eq1223
    | (have j0 := eq1223 y y
       grind)
    | (have r₁ := eq1223 y y
       have r₂ := eq2758
       grind)
    | exact resolve eq1223 eq2758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2758
  have eq2891 : y ≠ y ∨ y = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq2890
  have eq2892 : y = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq2891
  have eq2925 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq196 y y
       have i₂ := eq2892
       grind)
    | exact superpose eq2892 eq196
    | exact resolve eq196 eq2892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2931 : (M.op y y) = (M.op (σ x) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2670 eq2925
    | exact resolve eq2925 eq2670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2670 eq2925
  have eq2941 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2733 eq2931
    | exact resolve eq2931 eq2733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2733 eq2931
  have eq3024 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2892
       have i₂ := eq2941
       grind)
    | exact superpose eq2941 eq2892
    | exact resolve eq2892 eq2941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2892 eq2941
  have eq3046 : y = (M.op x y) := by grind
  clear eq3024
  have eq3061 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq3046
       grind)
    | exact superpose eq3046 eq18
    | exact resolve eq18 eq3046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq3062 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq3046
       grind)
    | exact superpose eq3046 eq24
    | exact resolve eq24 eq3046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq3046
  have eq3068 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq3062 eq20
    | exact resolve eq20 eq3062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3062
  have eq3145 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3061 eq202
    | exact resolve eq202 eq3061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq3154 : (M.op x (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq3061 eq192
    | exact resolve eq192 eq3061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq3157 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq3061 eq3154
    | exact resolve eq3154 eq3061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3061 eq3154
  have eq3177 : (M.op x y) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq3145 eq196
    | exact resolve eq196 eq3145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3186 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq3157 eq187
    | exact resolve eq187 eq3157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187 eq3157
  have eq3202 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq3186
    | exact resolve eq3186 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq3186
  have eq3203 : (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq3068 eq3202
    | exact resolve eq3202 eq3068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3202
  have eq3290 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq3203 eq1223
    | (have j0 := eq1223 (σ y) (σ y)
       grind)
    | (have r₁ := eq1223 (σ y) (σ y)
       have r₂ := eq3203
       grind)
    | exact resolve eq1223 eq3203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1223 eq3203
  have eq3291 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq3290
  have eq3292 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq3291
  have eq4032 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq3292 eq196
    | exact resolve eq196 eq3292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq4034 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3292 eq4032
    | exact resolve eq4032 eq3292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3292 eq4032
  have eq4043 : (M.op x y) = (σ y) := by
    first
    | exact superpose eq3145 eq4034
    | exact resolve eq4034 eq3145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3145 eq4034
  have eq4055 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq4043 eq26
    | exact resolve eq26 eq4043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq4092 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3177 eq4055
    | exact resolve eq4055 eq3177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3177 eq4055
  have eq4113 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq4092 eq27
    | exact resolve eq27 eq4092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq4092
  have eq4129 : (M.op x y) ≠ (σ y) := by
    first
    | exact superpose eq3068 eq4113
    | exact resolve eq4113 eq3068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3068 eq4113
  have eq4133 : False := by grind
  exact eq4133
