import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation106`: `x = x ◇ ((y ◇ x) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if x = y then D(x, y) else (if X = m(Y,Y) then m(Y,X) else m(X,Y))`, writing `X`, `Y` for `x`,
`y`.  The diagonal value `D` does not appear: the obligation is target-free, so `dcell`-style reuse
can spend it on any target whose law the companion satisfies. -/
theorem GuardFix_G1V4_Equation106 :
    AutBox.GuardFix (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law106 := by
  classical
  refine AutBox.guardFix_of (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hoff x y ↦ ?_)
  have hm := (@Law106.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (M.op b b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (M.op b b)).imp id (helse a b)
  have hd := hoff
  clear hthen helse hoff
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq17 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X0 (M.op (M.op x (M.op X0 X1)) x)
       have i₂ := eq8 (M.op X0 X1) x x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (M.op X1 X0)
       have i₂ := eq17 X1 X0
       grind)
    | exact superpose eq17 eq17
    | exact resolve eq17 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op X1 X0) X0 X2
       have i₂ := eq17 X1 X0
       grind)
    | exact superpose eq17 eq8
    | exact resolve eq8 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq19 X0 X1
       have i₂ := eq12 (M.op X1 X0) X1
       grind)
    | exact superpose eq12 eq19
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq19 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq48 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op (M.op X1 X2) (M.op (M.op X0 X1) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op X1 X2) (M.op X0 X1) X3
       have i₂ := eq20 X1 X0 X2
       grind)
    | exact superpose eq20 eq8
    | exact resolve eq8 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = (M.op X1 (M.op X0 X0)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq20 X0 X0 X0
       grind)
    | exact superpose eq20 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | exact resolve eq12 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    grind
  have eq51 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq50 X0
       have i₂ := eq20 X0 X0 X0
       grind)
    | exact superpose eq20 eq50
    | exact resolve eq50 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq50
  have eq52 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | (have j0 := eq13 (σ (k (τ X0) X1)) (k X0 (σ X1))
       grind)
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | (have j0 := eq13 (σ (k X1 (τ X0))) (k (σ X1) X0)
       grind)
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq13 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq12 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq51 X0
       have i₂ := eq12 (M.op X0 X0) X1
       grind)
    | exact superpose eq12 eq51
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq51 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq150 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X1
       have i₂ := eq32 (τ X0) X1
       grind)
    | exact superpose eq32 eq52
    | (have j0 := eq52 X0 X1
       have j1 := eq32 (τ X0) X1
       grind)
    | exact resolve eq52 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq152 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq52
    | (have j0 := eq52 X0 (M.op X1 X1)
       have j1 := eq12 (τ X0) X1
       grind)
    | exact resolve eq52 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq155 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq52 X0 X1
       grind)
    | exact superpose eq52 eq9
    | (have j1 := eq52 (k X0 (σ X1)) (k (τ X0) X1)
       grind)
    | exact resolve eq9 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq167 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    grind
  have eq169 : ∀ X0 X1 : G, (σ (M.op X0 (τ X1))) = (k (σ X0) X1) ∨ (τ X1) = X0 ∨ (M.op (τ X1) X0) = (k X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X1 X0
       have i₂ := eq32 X0 (τ X1)
       grind)
    | exact superpose eq32 eq53
    | (have j0 := eq53 X1 X0
       have j1 := eq32 X0 (τ X1)
       grind)
    | exact resolve eq53 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq176 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq9
    | (have j1 := eq53 (k (σ X0) X1) (k X0 (τ X1))
       grind)
    | exact resolve eq9 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq181 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq167 X0
       have i₂ := eq17 (τ X0) (τ X0)
       grind)
    | exact superpose eq17 eq167
    | (have j0 := eq167 X0
       grind)
    | exact resolve eq167 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq182 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq181 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq181
    | (have j0 := eq181 X0
       grind)
    | exact resolve eq181 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq243 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq140 X0 X1
       grind)
    | exact superpose eq140 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq140 X0 X1
       grind)
    | exact resolve eq12 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq249 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq243 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq362 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ (k X0 X1))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 (σ X0) (σ X1)
       have i₂ := eq55 X0 X1
       grind)
    | exact superpose eq55 eq17
    | (have j1 := eq55 X0 X1
       grind)
    | exact resolve eq17 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq371 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq55 X1 X0
       grind)
    | exact superpose eq55 eq9
    | (have j1 := eq55 X1 X0
       grind)
    | exact resolve eq9 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq440 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 (M.op X0 X1)) ∨ (M.op X1 (M.op X0 X1)) = (k X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq135 X1 (M.op X0 X1)
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq135
    | (have j0 := eq135 X1 (M.op X0 X1)
       grind)
    | exact resolve eq135 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq450 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 (M.op X0 X1)) ∨ (M.op X0 X1) = (k (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq135 (M.op X1 X0) X0
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq135
    | exact resolve eq135 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq470 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq450 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq450
    | (have j0 := eq450 X0 X1
       grind)
    | exact resolve eq450 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450
  have eq477 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 (M.op X0 X1)) = (k X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq440 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq440
    | (have j0 := eq440 X0 X1
       grind)
    | exact resolve eq440 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440
  have eq483 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq477 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq477
    | (have j0 := eq477 X0 X1
       grind)
    | exact resolve eq477 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477
  have eq490 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 (M.op X0 X1)) ∨ (M.op X0 X1) = (k X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq136 X0 (M.op X1 X0)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq136
    | exact resolve eq136 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq500 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 (M.op X0 X1)) ∨ (M.op X1 (M.op X0 X1)) = (k (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq136 (M.op X0 X1) X1
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq136
    | (have j0 := eq136 (M.op X0 X1) X1
       grind)
    | exact resolve eq136 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq520 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 (M.op X0 X1)) = (k (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq500 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq500
    | (have j0 := eq500 X0 X1
       grind)
    | exact resolve eq500 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500
  have eq527 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq490 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq490
    | (have j0 := eq490 X0 X1
       grind)
    | exact resolve eq490 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490
  have eq533 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k (M.op X0 X1) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq520 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq520
    | (have j0 := eq520 X0 X1
       grind)
    | exact resolve eq520 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520
  have eq552 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))) ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0
    grind
  have eq570 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq552 X0
       have i₂ := eq17 (σ X0) (σ X0)
       grind)
    | exact superpose eq17 eq552
    | (have j0 := eq552 X0
       grind)
    | exact resolve eq552 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552
  have eq571 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq570 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq570
    | (have j0 := eq570 X0
       grind)
    | exact resolve eq570 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570
  have eq573 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq533 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq533 X0 X1
       have i₂ := eq12 (M.op X0 X1) X1
       grind)
    | exact superpose eq12 eq533
    | (have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq533 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq533 X0 (M.op X1 X1)
       have r₂ := eq12 (M.op X0 (M.op X1 X1)) X1
       grind)
    | exact resolve eq533 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq984 : ∀ X0 : G, (σ X0) = (k (σ (M.op X0 X0)) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq182 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq182
    | exact resolve eq182 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq987 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (τ X1) = X0 ∨ (M.op X0 (τ X1)) = (k X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq182 X0
       have i₂ := eq12 X0 (τ X0)
       grind)
    | (have i₁ := eq182 X0
       have i₂ := eq12 (M.op (τ X0) (τ X0)) X1
       grind)
    | exact superpose eq12 eq182
    | (have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq182 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq1315 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq152 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq152
    | exact resolve eq152 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq2549 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 (M.op X0 X0)))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    grind
  clear eq362
  have eq2604 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2549 X0
       have i₂ := eq17 X0 X0
       grind)
    | exact superpose eq17 eq2549
    | (have j0 := eq2549 X0
       grind)
    | exact resolve eq2549 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2549
  have eq3231 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 (τ X0)))) ∨ (τ X0) = (M.op X1 (τ X0)) ∨ (k (τ X0) (M.op X1 (τ X0))) = (M.op (M.op X1 (τ X0)) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq150 X0 (M.op X1 (τ X0))
       have i₂ := eq17 X1 (τ X0)
       grind)
    | exact superpose eq17 eq150
    | (have j0 := eq150 X0 (M.op X1 (τ X0))
       grind)
    | exact resolve eq150 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150
  have eq3270 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 (τ X0)))) = X0 ∨ (τ X0) = (M.op X1 (τ X0)) ∨ (k (τ X0) (M.op X1 (τ X0))) = (M.op (M.op X1 (τ X0)) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3231 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3231
    | (have j0 := eq3231 X0 X1
       grind)
    | exact resolve eq3231 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3231
  have eq3275 : ∀ X0 X1 : G, (M.op X1 (τ X0)) = (k (τ X0) (M.op X1 (τ X0))) ∨ (k X0 (σ (M.op X1 (τ X0)))) = X0 ∨ (τ X0) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3270 X0 X1
       have i₂ := eq19 (τ X0) X1
       grind)
    | exact superpose eq19 eq3270
    | (have j0 := eq3270 X0 X1
       grind)
    | exact resolve eq3270 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3270
  have eq3279 : ∀ X0 X1 : G, (M.op X1 (τ X0)) = (k (τ X0) (M.op X1 (τ X0))) ∨ (k X0 (σ (M.op X1 (τ X0)))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq3275 X0 X1
       have j1 := eq527 X1 (τ X0)
       grind)
    | (have r₁ := eq3275 X0 X0
       have r₂ := eq527 X0 (τ X0)
       grind)
    | exact resolve eq3275 eq527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527 eq3275
  have eq3558 : ∀ X0 X1 : G, (σ (M.op X0 (τ X1))) = (k (σ (M.op X0 (τ X1))) X1) ∨ (τ X1) = (M.op X0 (τ X1)) ∨ (M.op (τ X1) (M.op X0 (τ X1))) = (k (M.op X0 (τ X1)) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq169 (M.op X0 (τ X1)) X1
       have i₂ := eq19 (τ X1) X0
       grind)
    | exact superpose eq19 eq169
    | (have j0 := eq169 (M.op X0 (τ X1)) X1
       grind)
    | exact resolve eq169 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq3602 : ∀ X0 X1 : G, (τ X1) = (k (M.op X0 (τ X1)) (τ X1)) ∨ (σ (M.op X0 (τ X1))) = (k (σ (M.op X0 (τ X1))) X1) ∨ (τ X1) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3558 X0 X1
       have i₂ := eq17 X0 (τ X1)
       grind)
    | exact superpose eq17 eq3558
    | (have j0 := eq3558 X0 X1
       grind)
    | exact resolve eq3558 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3558
  have eq3604 : ∀ X0 X1 : G, (σ (M.op X0 (τ X1))) = (k (σ (M.op X0 (τ X1))) X1) ∨ (τ X1) = (k (M.op X0 (τ X1)) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3602 X0 X1
       have j1 := eq533 X0 (τ X1)
       grind)
    | (have r₁ := eq3602 X0 X1
       have r₂ := eq533 X0 (τ X1)
       grind)
    | exact resolve eq3602 eq533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3602
  have eq12739 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ X0 = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq571 X0
       have i₂ := eq371 X0 X1
       grind)
    | (have i₁ := eq571 X0
       have i₂ := eq371 X0 (τ (M.op (σ X0) (σ X0)))
       grind)
    | exact superpose eq371 eq571
    | (have j1 := eq371 X1 X0
       grind)
    | exact resolve eq571 eq371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq571
  have eq12819 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq12739 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12739
  have eq14757 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq1315 X0 X1
       grind)
    | exact superpose eq1315 eq13
    | (have j0 := eq13 (σ (k X0 X1)) (σ (M.op X0 X1))
       have j1 := eq1315 X0 X1
       grind)
    | exact resolve eq13 eq1315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1315
  have eq15020 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14757 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14757
  have eq23631 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (τ (σ X1)) = X0 ∨ (τ (σ X0)) = X1 ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq155 (σ X1) X0
       have i₂ := eq987 X1 (σ X0)
       grind)
    | exact superpose eq987 eq155
    | (have j0 := eq155 (σ X0) (k (τ (σ X1)) X0)
       have j1 := eq987 X1 (σ X0)
       grind)
    | exact resolve eq155 eq987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq987
  have eq23664 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (τ (σ X1)) = X0 ∨ (τ (σ X0)) = X1 ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq23631 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq23631
    | (have j0 := eq23631 X0 X1
       grind)
    | exact resolve eq23631 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23631
  have eq23695 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (τ (σ X1)) = X0 ∨ (τ (σ X0)) = X1 ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq23664 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq23664
    | (have j0 := eq23664 X0 X1
       grind)
    | exact resolve eq23664 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23664
  have eq23712 : ∀ X0 X1 : G, X0 = X1 ∨ (k X1 X0) = X0 ∨ (τ (σ X0)) = X1 ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq23695 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq23695
    | (have j0 := eq23695 X0 X1
       grind)
    | exact resolve eq23695 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23695
  have eq23723 : ∀ X0 X1 : G, X0 = X1 ∨ X0 = X1 ∨ (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq23712 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq23712
    | (have j0 := eq23712 X0 X1
       grind)
    | exact resolve eq23712 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23712
  have eq23724 : ∀ X0 X1 : G, X0 = X1 ∨ (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq23723 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23723
  have eq23735 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq23724 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq23724
    | (have j0 := eq23724 X0 X1
       grind)
    | exact resolve eq23724 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23724
  have eq23741 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq23735 X0 X1
       have j1 := eq573 X1 X0
       grind)
    | (have r₁ := eq23735 X0 X1
       have r₂ := eq573 (M.op X1 X0) (k X1 X0)
       grind)
    | (have r₁ := eq23735 X0 X1
       have r₂ := eq573 (k X1 X0) (M.op X1 X0)
       grind)
    | (have r₁ := eq23735 X0 X1
       have r₂ := eq573 X0 X1
       grind)
    | exact resolve eq23735 eq573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573 eq23735
  have eq23783 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    grind
  have eq23817 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq23783 X0
       have i₂ := eq19 X0 X0
       grind)
    | exact superpose eq19 eq23783
    | (have j0 := eq23783 X0
       grind)
    | exact resolve eq23783 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq23783
  have eq23818 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq23817 X0
       have i₂ := eq17 X0 X0
       grind)
    | exact superpose eq17 eq23817
    | (have j0 := eq23817 X0
       grind)
    | exact resolve eq23817 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23817
  have eq23819 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq23818 X0
       have j1 := eq533 X0 X0
       grind)
    | (have r₁ := eq23818 x
       have r₂ := eq533 x x
       grind)
    | exact resolve eq23818 eq533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533 eq23818
  have eq23910 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq23819 X1
       have i₂ := eq15020 X0 X1
       grind)
    | (have i₁ := eq23819 X0
       have i₂ := eq15020 (M.op X0 X0) X1
       grind)
    | exact superpose eq15020 eq23819
    | (have j1 := eq15020 X0 X1
       grind)
    | exact resolve eq23819 eq15020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29989 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = y ∨ y = (k x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq12819 x y
       grind)
    | exact superpose eq12819 eq14
    | (have j1 := eq12819 x y
       grind)
    | (have r₁ := eq14
       have r₂ := eq12819 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq14
       have r₂ := eq12819 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq14 eq12819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12819
  have eq30109 : y = (k x y) ∨ x = y := by
    first
    | (have j1 := eq23910 x y
       grind)
    | (have r₁ := eq29989
       have r₂ := eq23910 x y
       grind)
    | (have r₁ := eq29989
       have r₂ := eq23910 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq29989
       have r₂ := eq23910 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq29989 eq23910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23910 eq29989
  have eq30325 : x = (M.op y y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq30109
       grind)
    | exact superpose eq30109 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq30109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30109
  have eq40785 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (M.op (τ X0) (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq49 (τ X0) (τ X0)
       have i₂ := eq3279 X0 (τ X0)
       grind)
    | exact superpose eq3279 eq49
    | (have j0 := eq49 (τ X0) (M.op (τ X0) (M.op (τ X0) (τ X0)))
       have j1 := eq3279 X0 (τ X0)
       grind)
    | exact resolve eq49 eq3279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40853 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq40785 X0
       have i₂ := eq17 (τ X0) (τ X0)
       grind)
    | exact superpose eq17 eq40785
    | (have j0 := eq40785 X0
       grind)
    | exact resolve eq40785 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40785
  have eq40854 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq40853 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40853
  have eq57498 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq40854 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq40854
    | exact resolve eq40854 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57646 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ (M.op (τ (σ X0)) (τ (σ X0)))))) ∨ (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) = X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq176 X0 (σ (M.op (τ (σ X0)) (τ (σ X0))))
       have i₂ := eq40854 (σ X0)
       grind)
    | exact superpose eq40854 eq176
    | (have j0 := eq176 (k X0 (τ (σ (M.op (τ (σ X0)) (τ (σ X0)))))) (σ X0)
       have j1 := eq40854 (σ X0)
       grind)
    | exact resolve eq176 eq40854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40854
  have eq57696 : ∀ X0 : G, (τ (σ X0)) = (k X0 (M.op (τ (σ X0)) (τ (σ X0)))) ∨ (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) = X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq57646 X0
       have i₂ := eq9 (M.op (τ (σ X0)) (τ (σ X0)))
       grind)
    | exact superpose eq9 eq57646
    | (have j0 := eq57646 X0
       grind)
    | exact resolve eq57646 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57646
  have eq57732 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) = X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq57696 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq57696
    | (have j0 := eq57696 X0
       grind)
    | exact resolve eq57696 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57696
  have eq57754 : ∀ X0 : G, (M.op (τ (σ X0)) (τ (σ X0))) = X0 ∨ (k X0 (M.op X0 X0)) = X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq57732 X0
       have i₂ := eq9 (M.op (τ (σ X0)) (τ (σ X0)))
       grind)
    | exact superpose eq9 eq57732
    | (have j0 := eq57732 X0
       grind)
    | exact resolve eq57732 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57732
  have eq57773 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 (M.op X0 X0)) = X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq57754 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq57754
    | (have j0 := eq57754 X0
       grind)
    | exact resolve eq57754 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57754
  have eq57792 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have j0 := eq57773 X0
       have j1 := eq483 X0 X0
       grind)
    | (have r₁ := eq57773 x
       have r₂ := eq483 x x
       grind)
    | (have r₁ := eq57773 X0
       have r₂ := eq483 (τ (σ X0)) (τ (σ X0))
       grind)
    | exact resolve eq57773 eq483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57773
  have eq57801 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq57792 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq57792
    | (have j0 := eq57792 X0
       grind)
    | exact resolve eq57792 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57792
  have eq57812 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq57801 X0
       have j1 := eq483 X0 X0
       grind)
    | (have r₁ := eq57801 x
       have r₂ := eq483 x x
       grind)
    | exact resolve eq57801 eq483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57801
  have eq58157 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq57812 X1
       have i₂ := eq15020 X0 X1
       grind)
    | (have i₁ := eq57812 X0
       have i₂ := eq15020 (M.op X0 X0) X1
       grind)
    | exact superpose eq15020 eq57812
    | (have j1 := eq15020 X0 X1
       grind)
    | exact resolve eq57812 eq15020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15020
  have eq58345 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq176 X0 (M.op (σ X0) (σ X0))
       have i₂ := eq57812 (σ X0)
       grind)
    | exact superpose eq57812 eq176
    | (have j0 := eq176 (k X0 (τ (M.op (σ X0) (σ X0)))) (σ X0)
       grind)
    | exact resolve eq176 eq57812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57812
  have eq58372 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq58345 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq58345
    | (have j0 := eq58345 X0
       grind)
    | exact resolve eq58345 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58345
  have eq62254 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq29 (σ X0) (σ (M.op X0 X0))
       have i₂ := eq57498 X0
       grind)
    | exact superpose eq57498 eq29
    | (have j0 := eq29 (σ X0) (σ (M.op X0 X0))
       have j1 := eq57498 X0
       grind)
    | exact resolve eq29 eq57498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq57498
  have eq62302 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq62254 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62254
  have eq62965 : (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq62302 y
       have i₂ := eq30325
       grind)
    | exact superpose eq30325 eq62302
    | exact resolve eq62302 eq30325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30325
  have eq63015 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq17 (σ X0) (σ (M.op X0 X0))
       have i₂ := eq62302 X0
       grind)
    | exact superpose eq62302 eq17
    | (have j1 := eq62302 X0
       grind)
    | exact resolve eq17 eq62302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62302
  have eq63145 : (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq62965
  have eq64743 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq17 (σ y) (σ x)
       have i₂ := eq63145
       grind)
    | exact superpose eq63145 eq17
    | exact resolve eq17 eq63145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63145
  have eq65221 : (σ (M.op x y)) ≠ (σ x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq64743
       grind)
    | exact superpose eq64743 eq14
    | exact resolve eq14 eq64743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64743
  have eq66209 : ∀ X0 X1 : G, (τ (σ (M.op X0 (τ (σ X1))))) = (k (τ (σ (M.op X0 (τ (σ X1))))) X1) ∨ (τ (σ (M.op X0 (τ (σ X1))))) = X1 ∨ (τ (σ X1)) = (k (M.op X0 (τ (σ X1))) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq155 (σ (M.op X0 (τ (σ X1)))) X1
       have i₂ := eq3604 X0 (σ X1)
       grind)
    | exact superpose eq3604 eq155
    | (have j0 := eq155 (σ (M.op X0 (τ (σ X1)))) (k (τ (σ (M.op X0 (τ (σ X1))))) X1)
       have j1 := eq3604 X0 (σ X1)
       grind)
    | exact resolve eq155 eq3604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155 eq3604
  have eq66249 : ∀ X0 X1 : G, (M.op X0 (τ (σ X1))) = (k (M.op X0 (τ (σ X1))) X1) ∨ (τ (σ (M.op X0 (τ (σ X1))))) = X1 ∨ (τ (σ X1)) = (k (M.op X0 (τ (σ X1))) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq66209 X0 X1
       have i₂ := eq9 (M.op X0 (τ (σ X1)))
       grind)
    | exact superpose eq9 eq66209
    | (have j0 := eq66209 X0 X1
       grind)
    | exact resolve eq66209 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66209
  have eq66306 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X1) ∨ (τ (σ (M.op X0 (τ (σ X1))))) = X1 ∨ (τ (σ X1)) = (k (M.op X0 (τ (σ X1))) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq66249 X0 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq66249
    | (have j0 := eq66249 X0 X1
       grind)
    | exact resolve eq66249 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66249
  have eq66334 : ∀ X0 X1 : G, (M.op X0 (τ (σ X1))) = X1 ∨ (M.op X0 X1) = (k (M.op X0 X1) X1) ∨ (τ (σ X1)) = (k (M.op X0 (τ (σ X1))) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq66306 X0 X1
       have i₂ := eq9 (M.op X0 (τ (σ X1)))
       grind)
    | exact superpose eq9 eq66306
    | (have j0 := eq66306 X0 X1
       grind)
    | exact resolve eq66306 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66306
  have eq66354 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k (M.op X0 X1) X1) ∨ (τ (σ X1)) = (k (M.op X0 (τ (σ X1))) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq66334 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq66334
    | (have j0 := eq66334 X0 X1
       grind)
    | exact resolve eq66334 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66334
  have eq66373 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X1) ∨ (τ (σ X1)) = (k (M.op X0 (τ (σ X1))) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq66354 X0 X1
       have j1 := eq470 X0 X1
       grind)
    | (have r₁ := eq66354 X0 X1
       have r₂ := eq470 X0 X1
       grind)
    | exact resolve eq66354 eq470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470 eq66354
  have eq66389 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X1) ∨ (k (M.op X0 X1) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq66373 X0 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq66373
    | (have j0 := eq66373 X0 X1
       grind)
    | exact resolve eq66373 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66373
  have eq66450 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 (M.op X1 X0)) ∨ (k X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq66389 X1 (M.op X0 X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq66389
    | exact resolve eq66389 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66389
  have eq107608 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ X0 = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq58372 X0
       have i₂ := eq371 X0 X1
       grind)
    | (have i₁ := eq58372 X0
       have i₂ := eq371 X0 (τ (M.op (σ X0) (σ X0)))
       grind)
    | exact superpose eq371 eq58372
    | (have j1 := eq371 X1 X0
       grind)
    | exact resolve eq58372 eq371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371 eq58372
  have eq107632 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ X0 = X1 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq107608 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107608
  have eq112570 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = y ∨ y = (k y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq107632 x y
       grind)
    | exact superpose eq107632 eq14
    | (have j1 := eq107632 x y
       grind)
    | (have r₁ := eq14
       have r₂ := eq107632 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq14
       have r₂ := eq107632 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq14 eq107632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107632
  have eq112636 : y = (k y x) ∨ x = y := by
    first
    | (have j1 := eq58157 x y
       grind)
    | (have r₁ := eq112570
       have r₂ := eq58157 x y
       grind)
    | (have r₁ := eq112570
       have r₂ := eq58157 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq112570
       have r₂ := eq58157 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq112570 eq58157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58157 eq112570
  have eq112722 : y = (M.op y x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq23741 x y
       have i₂ := eq112636
       grind)
    | exact superpose eq112636 eq23741
    | exact resolve eq23741 eq112636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112636
  have eq112730 : y = (M.op y x) ∨ x = y := by grind
  clear eq112722
  have eq112818 : x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq17 y x
       have i₂ := eq112730
       grind)
    | exact superpose eq112730 eq17
    | exact resolve eq17 eq112730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112730
  have eq113107 : (σ x) ≠ (σ x) ∨ x = y ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq65221
       have i₂ := eq112818
       grind)
    | exact superpose eq112818 eq65221
    | exact resolve eq65221 eq112818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65221 eq112818
  have eq113360 : (σ x) ≠ (σ x) ∨ x = y := by grind
  clear eq113107
  have eq113361 : x = y := by grind
  clear eq113360
  have eq113375 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq113361
       grind)
    | exact superpose eq113361 eq14
    | exact resolve eq14 eq113361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113361
  have eq115051 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq113375
       have i₂ := eq2604 x
       grind)
    | exact superpose eq2604 eq113375
    | (have j1 := eq2604 x
       grind)
    | (have r₁ := eq113375
       have r₂ := eq2604 x
       grind)
    | exact resolve eq113375 eq2604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2604
  have eq115052 : ∀ X0 : G, (σ (M.op x x)) ≠ X0 ∨ (k X0 (σ x)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq113375
       have i₂ := eq12 X0 (σ x)
       grind)
    | (have i₁ := eq113375
       have i₂ := eq12 (M.op (σ x) (σ x)) x
       grind)
    | exact superpose eq12 eq113375
    | (have j1 := eq12 X0 (σ x)
       grind)
    | (have r₁ := eq113375
       have r₂ := eq12 (σ (M.op x x)) (σ x)
       grind)
    | exact resolve eq113375 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115053 : ∀ X0 : G, (σ x) ≠ (σ (M.op x x)) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq113375
       have i₂ := eq249 (σ x) X0
       grind)
    | exact superpose eq249 eq113375
    | (have j1 := eq249 (σ x) X0
       grind)
    | exact resolve eq113375 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq115056 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq115051
  have eq117055 : (σ x) ≠ (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq113375
       have i₂ := eq115056
       grind)
    | exact superpose eq115056 eq113375
    | exact resolve eq113375 eq115056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115056
  have eq124317 : (k (σ (M.op x x)) (σ x)) = (M.op (σ (M.op x x)) (σ x)) := by
    first
    | (have j0 := eq115052 (σ (M.op x x))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115052
  have eq126472 : (σ x) = (M.op (σ (M.op x x)) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq984 x
       have i₂ := eq124317
       grind)
    | exact superpose eq124317 eq984
    | (have j0 := eq984 x
       grind)
    | exact resolve eq984 eq124317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq984 eq124317
  have eq127581 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq63015 x
       have i₂ := eq126472
       grind)
    | exact superpose eq126472 eq63015
    | (have j0 := eq63015 x
       grind)
    | exact resolve eq63015 eq126472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63015 eq126472
  have eq127735 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq127581
  have eq127755 : x = (M.op x x) := by
    first
    | (have r₁ := eq127735
       have r₂ := eq117055
       grind)
    | exact resolve eq127735 eq117055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117055 eq127735
  have eq129200 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op x X0) (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq48 x x X0 X1
       have i₂ := eq127755
       grind)
    | exact superpose eq127755 eq48
    | exact resolve eq48 eq127755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq134300 : ∀ X0 X1 : G, (M.op X1 (M.op x X0)) = (k X1 (M.op x X0)) ∨ (M.op x X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq49 (M.op x X1) X1
       have i₂ := eq129200 X1 X1
       grind)
    | exact superpose eq129200 eq49
    | exact resolve eq49 eq129200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq129200
  have eq165270 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq115053 X0
       have i₂ := eq127755
       grind)
    | exact superpose eq127755 eq115053
    | (have j0 := eq115053 X0
       grind)
    | exact resolve eq115053 eq127755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115053
  have eq165273 : ∀ X0 : G, (M.op (σ x) X0) = (k (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq165270 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165270
  have eq167443 : ∀ X0 : G, (k x (τ X0)) = (τ (M.op (σ x) X0)) ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq176 x X0
       have i₂ := eq165273 X0
       grind)
    | exact superpose eq165273 eq176
    | (have j0 := eq176 (k x (τ X0)) (M.op (σ x) X0)
       grind)
    | exact resolve eq176 eq165273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq165273
  have eq169835 : ∀ X0 : G, (τ (σ x)) = (k x (τ (M.op X0 (σ x)))) ∨ x = (τ (M.op X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq167443 (M.op X0 (σ x))
       have i₂ := eq17 X0 (σ x)
       grind)
    | exact superpose eq17 eq167443
    | (have j0 := eq167443 (M.op X0 (σ x))
       grind)
    | exact resolve eq167443 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167443
  have eq169888 : ∀ X0 : G, x = (k x (τ (M.op X0 (σ x)))) ∨ x = (τ (M.op X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq169835 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq169835
    | (have j0 := eq169835 X0
       grind)
    | exact resolve eq169835 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169835
  have eq211884 : ∀ X0 : G, (M.op x X0) = (M.op X0 (M.op x X0)) ∨ (M.op x X0) = X0 ∨ (k X0 (M.op x X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq134300 X0 X0
       have i₂ := eq66450 X0 x
       grind)
    | exact superpose eq66450 eq134300
    | (have j0 := eq134300 X0 (M.op X0 (M.op x X0))
       have j1 := eq66450 X0 x
       grind)
    | exact resolve eq134300 eq66450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66450 eq134300
  have eq211985 : ∀ X0 : G, (M.op x X0) = (M.op X0 (M.op x X0)) ∨ (k X0 (M.op x X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq211884 X0
       have j1 := eq483 x X0
       grind)
    | (have r₁ := eq211884 X0
       have r₂ := eq483 X0 (M.op x X0)
       grind)
    | (have r₁ := eq211884 x
       have r₂ := eq483 x x
       grind)
    | exact resolve eq211884 eq483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211884
  have eq211986 : ∀ X0 : G, (M.op x X0) = X0 ∨ (k X0 (M.op x X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq211985 X0
       have i₂ := eq17 x X0
       grind)
    | exact superpose eq17 eq211985
    | (have j0 := eq211985 X0
       grind)
    | exact resolve eq211985 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq211985
  have eq211987 : ∀ X0 : G, (k X0 (M.op x X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq211986 X0
       have j1 := eq483 x X0
       grind)
    | (have r₁ := eq211986 x
       have r₂ := eq483 x x
       grind)
    | exact resolve eq211986 eq483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483 eq211986
  have eq215192 : ∀ X0 : G, (k X0 (σ (M.op x (τ X0)))) = X0 ∨ (τ X0) = (M.op x (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq3279 X0 x
       have i₂ := eq211987 (τ X0)
       grind)
    | exact superpose eq211987 eq3279
    | (have j0 := eq3279 X0 x
       grind)
    | exact resolve eq3279 eq211987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3279 eq211987
  have eq222252 : ∀ X0 : G, x = (M.op x (τ (M.op X0 (σ x)))) ∨ x = (τ (M.op X0 (σ x))) ∨ x = (τ (M.op X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq23741 (τ (M.op X0 (σ x))) x
       have i₂ := eq169888 X0
       grind)
    | exact superpose eq169888 eq23741
    | (have j1 := eq169888 X0
       grind)
    | exact resolve eq23741 eq169888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23741 eq169888
  have eq222255 : ∀ X0 : G, x = (M.op x (τ (M.op X0 (σ x)))) ∨ x = (τ (M.op X0 (σ x))) := by
    intro X0
    first
    | (have j0 := eq222252 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222252
  have eq231075 : ∀ X0 : G, (M.op X0 (σ x)) = (k (M.op X0 (σ x)) (σ x)) ∨ x = (τ (M.op X0 (σ x))) ∨ x = (τ (M.op X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq215192 (M.op X0 (σ x))
       have i₂ := eq222255 X0
       grind)
    | exact superpose eq222255 eq215192
    | (have j1 := eq222255 X0
       grind)
    | exact resolve eq215192 eq222255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215192 eq222255
  have eq231280 : ∀ X0 : G, (M.op X0 (σ x)) = (k (M.op X0 (σ x)) (σ x)) ∨ x = (τ (M.op X0 (σ x))) := by
    intro X0
    first
    | (have j0 := eq231075 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231075
  have eq466863 : x = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq23819 (σ x)
       have i₂ := eq231280 (σ x)
       grind)
    | exact superpose eq231280 eq23819
    | (have j1 := eq231280 (σ x)
       grind)
    | exact resolve eq23819 eq231280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23819 eq231280
  have eq466879 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq10 (M.op (σ x) (σ x))
       have i₂ := eq466863
       grind)
    | exact superpose eq466863 eq10
    | exact resolve eq10 eq466863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466863
  have eq466881 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq466879
  have eq466893 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq113375
       have i₂ := eq466881
       grind)
    | exact superpose eq466881 eq113375
    | exact resolve eq113375 eq466881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113375 eq466881
  have eq467481 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq466893
       have i₂ := eq127755
       grind)
    | exact superpose eq127755 eq466893
    | exact resolve eq466893 eq127755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127755 eq466893
  have eq467482 : False := by grind
  exact eq467482

/-- The `Equation3` cell the obligation pays for. -/
theorem Equation3_StructuralFromFin_Equation106 : Law3.StructuralFromFin Law106 :=
  AutBox.structuralFromFin_boxIte (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    GuardFix_G1V4_Equation106

/-- `Equation224`: `x = (y ◇ (x ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if x = y then D(x, y) else (if Y = m(X,X) then X else m(X,Y))`, writing `X`, `Y` for `x`,
`y`.  The diagonal value `D` does not appear: the obligation is target-free, so `dcell`-style reuse
can spend it on any target whose law the companion satisfies. -/
theorem GuardFix_G0V0_Equation224 :
    AutBox.GuardFix (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law224 := by
  classical
  refine AutBox.guardFix_of (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hoff x y ↦ ?_)
  have hm := (@Law224.models_iff G M).mp hM
  have ht : ∀ a b : G, b ≠ M.op a a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (b) (M.op a a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, b = M.op a a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (b) (M.op a a)).imp id (helse a b)
  have hd := hoff
  clear hthen helse hoff
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq17 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 (M.op x (M.op (M.op X0 X1) x)) X1
       have i₂ := eq8 (M.op X0 X1) x x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 (M.op X0 X1) X0
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq17
    | exact resolve eq17 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op X1 X0) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op X0 X2) X1 X0
       have i₂ := eq17 X0 X2
       grind)
    | exact superpose eq17 eq8
    | exact resolve eq8 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq30 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq19 X0 X1
       have i₂ := eq12 X0 (M.op X0 X1)
       grind)
    | exact superpose eq12 eq19
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq19 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X1
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq17 X0 X1
       have i₂ := eq12 X0 (M.op X0 X1)
       grind)
    | exact superpose eq12 eq17
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq17 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 X2 : G, (k (M.op X1 X2) X0) = (M.op (M.op X1 X2) X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 (M.op X1 X2) X2
       have i₂ := eq12 (M.op X1 X2) X0
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq12 X0 (M.op X1 (M.op X0 X2))
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 (M.op X1 X2) X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = (M.op (M.op X0 X0) X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X0) X1
       have i₂ := eq20 X0 X0 X0
       grind)
    | exact superpose eq20 eq12
    | (have j0 := eq12 X0 X1
       grind)
    | exact resolve eq12 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    grind
  have eq51 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | (have j0 := eq13 (σ (k (τ X0) X1)) (k X0 (σ X1))
       grind)
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | (have j0 := eq13 (σ (k X1 (τ X0))) (k (σ X1) X0)
       grind)
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq13 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq12 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq29 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq29
    | (have j1 := eq13 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq29 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (σ X1)) ∨ X0 = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq29 (σ X1) (σ X0)
       grind)
    | exact superpose eq29 eq13
    | (have j0 := eq13 (σ X0) (k (σ X0) (σ X1))
       have j1 := eq29 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq47 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq47 X0
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq47
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq47 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq118 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    grind
  have eq123 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq51 X0 X1
       grind)
    | exact superpose eq51 eq9
    | (have j1 := eq51 (k X0 (σ X1)) (k (τ X0) X1)
       grind)
    | exact resolve eq9 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq124 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq118 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq118
    | (have j0 := eq118 X0
       grind)
    | exact resolve eq118 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq158 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq52 X1 X0
       have i₂ := eq12 X0 (τ X1)
       grind)
    | exact superpose eq12 eq52
    | (have j0 := eq52 X1 (M.op X0 X0)
       have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq52 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq163 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq52 X1 X0
       grind)
    | exact superpose eq52 eq9
    | (have j1 := eq52 (k (σ X0) X1) (k X0 (τ X1))
       grind)
    | exact resolve eq9 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq241 : ∀ X0 X1 X2 : G, (k (σ (M.op X0 X1)) X2) = (σ (M.op (M.op X0 X1) (τ X2))) ∨ (M.op X0 X1) = (τ X2) ∨ (M.op (τ X2) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X2 (M.op X0 X1)
       have i₂ := eq33 (τ X2) X0 X1
       grind)
    | exact superpose eq33 eq52
    | (have j0 := eq52 X2 (M.op X0 X1)
       have j1 := eq33 (τ X2) X0 X2
       grind)
    | exact resolve eq52 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq52
  have eq282 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq111 X0 X1
       grind)
    | exact superpose eq111 eq31
    | (have j0 := eq31 X0 X1
       have j1 := eq111 X0 X1
       grind)
    | exact resolve eq31 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq111
  have eq289 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq282 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282
  have eq313 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq54 x y
       grind)
    | exact superpose eq54 eq14
    | (have j1 := eq54 x y
       grind)
    | (have r₁ := eq14
       have r₂ := eq54 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq14
       have r₂ := eq54 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq589 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0
    grind
  have eq593 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (τ X1) = X0 ∨ (σ X0) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq163 X0 X1
       have i₂ := eq29 X1 (σ X0)
       grind)
    | exact superpose eq29 eq163
    | (have j0 := eq163 (k X0 (τ X1)) (M.op (σ X0) X1)
       have j1 := eq29 X1 (σ X0)
       grind)
    | exact resolve eq163 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq606 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq589 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq589
    | (have j0 := eq589 X0
       grind)
    | exact resolve eq589 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589
  have eq890 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq124 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq124
    | exact resolve eq124 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq1230 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (k X0 X1)) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 (σ X0) (σ X1)
       have i₂ := eq79 X0 X1
       grind)
    | exact superpose eq79 eq17
    | (have j1 := eq79 X0 X1
       grind)
    | exact resolve eq17 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq1382 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq158 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq158
    | exact resolve eq158 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1386 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (τ (k (σ X0) X1)) ∨ (M.op X0 X0) = (τ X1) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 (τ X1))
       have i₂ := eq158 X0 X1
       grind)
    | exact superpose eq158 eq9
    | (have j1 := eq158 X0 X1
       grind)
    | exact resolve eq9 eq158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq2577 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq313
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq313
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq313 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2580 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (k x y) := by
    first
    | (have i₁ := eq313
       have i₂ := eq29 y x
       grind)
    | exact superpose eq29 eq313
    | (have j1 := eq29 y x
       grind)
    | exact resolve eq313 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq2590 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (k x y) := by grind
  clear eq2580
  have eq2593 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by grind
  clear eq2577
  have eq2625 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X0)) X1) ∨ (τ (σ X0)) = X1 ∨ X0 = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq123 (σ X0) X1
       have i₂ := eq81 X0 X1
       grind)
    | exact superpose eq81 eq123
    | (have j0 := eq123 (σ X0) (k (τ (σ X0)) X1)
       have j1 := eq81 X0 X1
       grind)
    | exact resolve eq123 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq2638 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (τ (σ X0)) = X1 ∨ X0 = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2625 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq2625
    | (have j0 := eq2625 X0 X1
       grind)
    | exact resolve eq2625 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2625
  have eq2640 : ∀ X0 X1 : G, X0 = X1 ∨ (k X0 X1) = X0 ∨ X0 = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2638 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq2638
    | (have j0 := eq2638 X0 X1
       grind)
    | exact resolve eq2638 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2638
  have eq2641 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq2640 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2640
  have eq3262 : (σ x) = (k (σ x) (σ y)) ∨ x = y ∨ x = (k x y) := by grind
  clear eq2590
  have eq3443 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq19 (σ x) (σ x)
       have i₂ := eq2593
       grind)
    | exact superpose eq2593 eq19
    | exact resolve eq19 eq2593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2593
  have eq5680 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) X1)) X0) ∨ (τ X0) = (M.op (τ X0) X1) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq241 (τ X0) X1 X0
       have i₂ := eq17 (τ X0) X1
       grind)
    | exact superpose eq17 eq241
    | (have j0 := eq241 (τ X0) X1 X0
       grind)
    | exact resolve eq241 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241
  have eq5725 : ∀ X0 X1 : G, (k (σ (M.op (τ X0) X1)) X0) = X0 ∨ (τ X0) = (M.op (τ X0) X1) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5680 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5680
    | (have j0 := eq5680 X0 X1
       grind)
    | exact resolve eq5680 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5680
  have eq8443 : (τ (σ x)) = (k (τ (σ x)) y) ∨ y = (τ (σ x)) ∨ x = y ∨ x = (k x y) := by
    first
    | (have i₁ := eq123 (σ x) y
       have i₂ := eq3262
       grind)
    | exact superpose eq3262 eq123
    | (have j0 := eq123 (σ x) (k (τ (σ x)) y)
       grind)
    | exact resolve eq123 eq3262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3262
  have eq8459 : x = (k x y) ∨ y = (τ (σ x)) ∨ x = y ∨ x = (k x y) := by
    first
    | (have i₁ := eq8443
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq8443
    | exact resolve eq8443 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8443
  have eq8460 : x = (k x y) ∨ y = (τ (σ x)) ∨ x = y := by grind
  clear eq8459
  have eq8466 : x = y ∨ x = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq8460
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq8460
    | exact resolve eq8460 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8460
  have eq8467 : x = (k x y) ∨ x = y := by grind
  clear eq8466
  have eq8840 : x = (M.op x y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq8467
       grind)
    | exact superpose eq8467 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq8467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8467
  have eq9068 : ∀ X0 : G, x = (M.op (M.op X0 x) x) ∨ y = (M.op x x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq20 x x y
       have i₂ := eq8840
       grind)
    | exact superpose eq8840 eq20
    | exact resolve eq20 eq8840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq8840
  have eq17140 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq1382 X1 X0
       grind)
    | exact superpose eq1382 eq13
    | (have j0 := eq13 (σ (k X0 X1)) (σ (M.op X0 X1))
       have j1 := eq1382 X1 X0
       grind)
    | exact resolve eq13 eq1382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1382
  have eq17363 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq17140 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17140
  have eq17608 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (k X0 X1)) (σ X0)) ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 (σ X0) (σ X1)
       have i₂ := eq2641 X0 X1
       grind)
    | exact superpose eq2641 eq17
    | (have j1 := eq2641 X0 X1
       grind)
    | exact resolve eq17 eq2641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2641
  have eq20247 : (σ (M.op x y)) ≠ (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq3443
       grind)
    | exact superpose eq3443 eq14
    | exact resolve eq14 eq3443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3443
  have eq22757 : ∀ X0 X1 : G, (M.op X1 X0) = (τ (k (σ X1) (σ X0))) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1386 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1386
    | (have j0 := eq1386 (M.op X1 X0) (k (σ X1) (σ X0))
       grind)
    | exact resolve eq1386 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1386
  have eq62619 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ (M.op (τ (σ X0)) X1))) X0) ∨ (τ (σ (M.op (τ (σ X0)) X1))) = X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) X1) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq123 (σ (M.op (τ (σ X0)) X1)) X0
       have i₂ := eq5725 (σ X0) X1
       grind)
    | exact superpose eq5725 eq123
    | (have j0 := eq123 (σ X0) (k (τ (σ (M.op (τ (σ X0)) X1))) X0)
       have j1 := eq5725 (σ X0) X1
       grind)
    | exact resolve eq123 eq5725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5725
  have eq62677 : ∀ X0 X1 : G, (τ (σ X0)) = (k (M.op (τ (σ X0)) X1) X0) ∨ (τ (σ (M.op (τ (σ X0)) X1))) = X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) X1) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq62619 X0 X1
       have i₂ := eq9 (M.op (τ (σ X0)) X1)
       grind)
    | exact superpose eq9 eq62619
    | (have j0 := eq62619 X0 X1
       grind)
    | exact resolve eq62619 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62619
  have eq62712 : ∀ X0 X1 : G, (k (M.op X0 X1) X0) = X0 ∨ (τ (σ (M.op (τ (σ X0)) X1))) = X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) X1) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq62677 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq62677
    | (have j0 := eq62677 X0 X1
       grind)
    | exact resolve eq62677 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62677
  have eq62729 : ∀ X0 X1 : G, (M.op (τ (σ X0)) X1) = X0 ∨ (k (M.op X0 X1) X0) = X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) X1) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq62712 X0 X1
       have i₂ := eq9 (M.op (τ (σ X0)) X1)
       grind)
    | exact superpose eq9 eq62712
    | (have j0 := eq62712 X0 X1
       grind)
    | exact resolve eq62712 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62712
  have eq62745 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k (M.op X0 X1) X0) = X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) X1) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq62729 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq62729
    | (have j0 := eq62729 X0 X1
       grind)
    | exact resolve eq62729 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62729
  have eq62764 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X0 ∨ (k (M.op X0 X1) X0) = X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq62745 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq62745
    | (have j0 := eq62745 X0 X1
       grind)
    | exact resolve eq62745 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62745
  have eq62765 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k (M.op X0 X1) X0) = X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq62764 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62764
  have eq62777 : ∀ X0 X1 : G, (k (M.op X0 X1) X0) = X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq62765 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq62765
    | (have j0 := eq62765 X0 X1
       grind)
    | exact resolve eq62765 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62765
  have eq62810 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ X0 = X1 ∨ X0 = X1 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq62777 X0 X0
       have i₂ := eq17363 X0 X1
       grind)
    | (have i₁ := eq62777 X0 X1
       have i₂ := eq17363 X0 (M.op X0 X1)
       grind)
    | exact superpose eq17363 eq62777
    | (have j1 := eq17363 X1 X0
       grind)
    | exact resolve eq62777 eq17363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17363
  have eq63219 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq62810 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62810
  have eq66590 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = y ∨ x = (k y x) := by
    first
    | (have i₁ := eq313
       have i₂ := eq63219 y x
       grind)
    | exact superpose eq63219 eq313
    | (have j1 := eq63219 (σ y) (M.op (σ x) (σ x))
       grind)
    | (have r₁ := eq313
       have r₂ := eq63219 y x
       grind)
    | (have r₁ := eq313
       have r₂ := eq63219 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq313
       have r₂ := eq63219 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq313 eq63219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313 eq63219
  have eq66761 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (k y x) := by grind
  clear eq66590
  have eq66762 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (k y x) := by grind
  clear eq66761
  have eq69958 : (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (k y x) := by
    first
    | (have i₁ := eq17 (σ x) (σ x)
       have i₂ := eq66762
       grind)
    | exact superpose eq66762 eq17
    | exact resolve eq17 eq66762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66762
  have eq72507 : (τ (σ x)) = (k y (τ (σ x))) ∨ y = (τ (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ x = (k y x) := by
    first
    | (have i₁ := eq593 y (σ x)
       have i₂ := eq69958
       grind)
    | exact superpose eq69958 eq593
    | (have j0 := eq593 y (σ x)
       grind)
    | exact resolve eq593 eq69958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593 eq69958
  have eq72652 : x = (k y x) ∨ y = (τ (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ x = (k y x) := by
    first
    | (have i₁ := eq72507
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq72507
    | exact resolve eq72507 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72507
  have eq72653 : x = (k y x) ∨ y = (τ (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = y := by grind
  clear eq72652
  have eq72665 : x = y ∨ x = (k y x) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq72653
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq72653
    | exact resolve eq72653 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72653
  have eq72666 : (σ y) = (k (σ y) (σ x)) ∨ x = (k y x) ∨ x = y := by grind
  clear eq72665
  have eq75900 : (τ (σ y)) = (k (τ (σ y)) x) ∨ x = (τ (σ y)) ∨ x = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq123 (σ y) x
       have i₂ := eq72666
       grind)
    | exact superpose eq72666 eq123
    | (have j0 := eq123 (σ y) (k (τ (σ y)) x)
       grind)
    | exact resolve eq123 eq72666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72666
  have eq75958 : y = (k y x) ∨ x = (τ (σ y)) ∨ x = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq75900
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq75900
    | exact resolve eq75900 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75900
  have eq75980 : x = y ∨ y = (k y x) ∨ x = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq75958
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq75958
    | exact resolve eq75958 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75958
  have eq75981 : y = (k y x) ∨ x = y ∨ x = (k y x) := by grind
  clear eq75980
  have eq76820 : y = (M.op y x) ∨ x = y ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq75981
       have i₂ := eq30 x y
       grind)
    | exact superpose eq30 eq75981
    | (have j1 := eq30 x y
       grind)
    | exact resolve eq75981 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75981
  have eq76899 : y = (M.op y x) ∨ x = y ∨ x = (M.op y x) := by grind
  clear eq76820
  have eq76977 : x = (M.op y x) ∨ y = (M.op x x) ∨ x = y ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq9068 y
       have i₂ := eq76899
       grind)
    | exact superpose eq76899 eq9068
    | exact resolve eq9068 eq76899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9068 eq76899
  have eq77094 : x = (M.op y x) ∨ y = (M.op x x) ∨ x = y := by grind
  clear eq76977
  have eq78645 : y = (M.op x y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq17 y x
       have i₂ := eq77094
       grind)
    | exact superpose eq77094 eq17
    | exact resolve eq17 eq77094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77094
  have eq79360 : (σ y) ≠ (σ y) ∨ x = y ∨ y = (M.op x x) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq20247
       have i₂ := eq78645
       grind)
    | exact superpose eq78645 eq20247
    | exact resolve eq20247 eq78645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20247 eq78645
  have eq79507 : (σ y) ≠ (σ y) ∨ x = y ∨ y = (M.op x x) := by grind
  clear eq79360
  have eq79508 : y = (M.op x x) ∨ x = y := by grind
  clear eq79507
  have eq79942 : y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq19 x x
       have i₂ := eq79508
       grind)
    | exact superpose eq79508 eq19
    | exact resolve eq19 eq79508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80039 : x = (k y x) ∨ x = y ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq62777 x x
       have i₂ := eq79508
       grind)
    | exact superpose eq79508 eq62777
    | exact resolve eq62777 eq79508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79508
  have eq80040 : x = (k y x) ∨ x = y := by grind
  clear eq80039
  have eq82899 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq1230 y x
       have i₂ := eq80040
       grind)
    | exact superpose eq80040 eq1230
    | (have j0 := eq1230 (σ y) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq1230 eq80040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1230 eq80040
  have eq82937 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq82899
  have eq123919 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq82937
       grind)
    | exact superpose eq82937 eq14
    | exact resolve eq14 eq82937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82937
  have eq124033 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq123919
       have i₂ := eq79942
       grind)
    | exact superpose eq79942 eq123919
    | exact resolve eq123919 eq79942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79942 eq123919
  have eq124059 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq124033
  have eq124060 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq124059
  have eq124113 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq124060
       grind)
    | exact superpose eq124060 eq9
    | exact resolve eq9 eq124060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124060
  have eq124279 : x = y ∨ x = y := by
    first
    | (have i₁ := eq124113
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq124113
    | exact resolve eq124113 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124113
  have eq124280 : x = y := by grind
  clear eq124279
  have eq125438 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq124280
       grind)
    | exact superpose eq124280 eq14
    | exact resolve eq14 eq124280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124280
  have eq126581 : ∀ X0 : G, (σ (M.op x x)) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq125438
       have i₂ := eq12 (σ x) X0
       grind)
    | (have i₁ := eq125438
       have i₂ := eq12 X0 (M.op (σ x) (σ x))
       grind)
    | exact superpose eq12 eq125438
    | (have j1 := eq12 (σ x) X0
       grind)
    | (have r₁ := eq125438
       have r₂ := eq12 (σ x) (σ (M.op x x))
       grind)
    | exact resolve eq125438 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126582 : ∀ X0 : G, (σ x) ≠ (σ (M.op x x)) ∨ (M.op X0 (σ x)) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq125438
       have i₂ := eq289 (σ x) X0
       grind)
    | exact superpose eq289 eq125438
    | (have j1 := eq289 (σ x) X0
       grind)
    | exact resolve eq125438 eq289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289
  have eq135148 : (k (σ x) (σ (M.op x x))) = (M.op (σ x) (σ (M.op x x))) := by
    first
    | (have j0 := eq126581 (σ (M.op x x))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126581
  have eq136548 : (τ (M.op (σ x) (σ (M.op x x)))) = (k (τ (σ x)) (M.op x x)) ∨ (M.op x x) = (τ (σ x)) := by
    first
    | (have i₁ := eq123 (σ x) (M.op x x)
       have i₂ := eq135148
       grind)
    | exact superpose eq135148 eq123
    | (have j0 := eq123 (M.op (σ x) (σ (M.op x x))) (k (τ (σ x)) (M.op x x))
       grind)
    | exact resolve eq123 eq135148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135148
  have eq136549 : (k x (M.op x x)) = (τ (M.op (σ x) (σ (M.op x x)))) ∨ (M.op x x) = (τ (σ x)) := by
    first
    | (have i₁ := eq136548
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq136548
    | exact resolve eq136548 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136548
  have eq136555 : x = (τ (M.op (σ x) (σ (M.op x x)))) ∨ (M.op x x) = (τ (σ x)) := by grind
  clear eq136549
  have eq136557 : x = (τ (M.op (σ x) (σ (M.op x x)))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq136555
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq136555
    | exact resolve eq136555 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136555
  have eq195630 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ X0 = X1 ∨ X0 = X1 ∨ (M.op X1 X0) = (τ (k (σ X1) (σ X0))) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq62777 X1 X1
       have i₂ := eq22757 X0 X1
       grind)
    | (have i₁ := eq62777 X0 X1
       have i₂ := eq22757 (M.op X0 X1) X1
       grind)
    | exact superpose eq22757 eq62777
    | (have j1 := eq22757 X0 X1
       grind)
    | exact resolve eq62777 eq22757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22757 eq62777
  have eq195670 : ∀ X0 X1 : G, (M.op X1 X0) = (τ (k (σ X1) (σ X0))) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq195630 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195630
  have eq208502 : ∀ X0 : G, (τ (σ X0)) = (M.op X0 (M.op X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (k (M.op X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq195670 (M.op X0 X0) X0
       have i₂ := eq890 X0
       grind)
    | exact superpose eq890 eq195670
    | (have j0 := eq195670 (M.op X0 X0) X0
       have j1 := eq890 X0
       grind)
    | exact resolve eq195670 eq890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq890 eq195670
  have eq208544 : ∀ X0 : G, (τ (σ X0)) = (M.op X0 (M.op X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq208502 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208502
  have eq208559 : ∀ X0 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq208544 X0
       have i₂ := eq19 X0 X0
       grind)
    | exact superpose eq19 eq208544
    | (have j0 := eq208544 X0
       grind)
    | exact resolve eq208544 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq208544
  have eq208562 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq208559 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq208559
    | (have j0 := eq208559 X0
       grind)
    | exact resolve eq208559 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208559
  have eq208563 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq208562 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208562
  have eq210408 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq17608 (M.op X0 X0) X0
       have i₂ := eq208563 X0
       grind)
    | exact superpose eq208563 eq17608
    | (have j0 := eq17608 (σ (M.op X0 X0)) (M.op (σ X0) (σ (M.op X0 X0)))
       have j1 := eq208563 X0
       grind)
    | exact resolve eq17608 eq208563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17608 eq208563
  have eq210436 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq210408 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210408
  have eq212253 : x = (τ (σ (M.op x x))) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq136557
       have i₂ := eq210436 x
       grind)
    | exact superpose eq210436 eq136557
    | (have j1 := eq210436 x
       grind)
    | exact resolve eq136557 eq210436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136557 eq210436
  have eq212315 : x = (τ (σ (M.op x x))) ∨ x = (M.op x x) := by grind
  clear eq212253
  have eq212327 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq212315
       have i₂ := eq9 (M.op x x)
       grind)
    | exact superpose eq9 eq212315
    | exact resolve eq212315 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212315
  have eq212328 : x = (M.op x x) := by grind
  clear eq212327
  have eq213769 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 (σ x)) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq126582 X0
       have i₂ := eq212328
       grind)
    | exact superpose eq212328 eq126582
    | (have j0 := eq126582 X0
       grind)
    | exact resolve eq126582 eq212328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126582
  have eq213810 : ∀ X0 : G, (M.op x X0) = (k x X0) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq46 x x
       have i₂ := eq212328
       grind)
    | exact superpose eq212328 eq46
    | exact resolve eq46 eq212328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq214003 : ∀ X0 : G, (M.op X0 (σ x)) = (k X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq213769 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213769
  have eq217897 : ∀ X0 : G, (τ (M.op X0 (σ x))) = (k (τ X0) x) ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq123 X0 x
       have i₂ := eq214003 X0
       grind)
    | exact superpose eq214003 eq123
    | (have j0 := eq123 (M.op X0 (σ x)) (k (τ X0) x)
       grind)
    | exact resolve eq123 eq214003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq214003
  have eq218086 : x = (M.op x (τ (M.op (σ x) (σ x)))) ∨ x = (τ (M.op (σ x) (σ x))) ∨ x = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq606 x
       have i₂ := eq213810 (τ (M.op (σ x) (σ x)))
       grind)
    | exact superpose eq213810 eq606
    | (have j0 := eq606 x
       have j1 := eq213810 (M.op x (τ (M.op (σ x) (σ x))))
       grind)
    | exact resolve eq606 eq213810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606 eq213810
  have eq218087 : x = (M.op x (τ (M.op (σ x) (σ x)))) ∨ x = (τ (M.op (σ x) (σ x))) := by grind
  clear eq218086
  have eq234669 : ∀ X0 : G, (τ (σ x)) = (k (τ (M.op (σ x) X0)) x) ∨ x = (τ (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq217897 (M.op (σ x) X0)
       have i₂ := eq17 (σ x) X0
       grind)
    | exact superpose eq17 eq217897
    | (have j0 := eq217897 (M.op (σ x) X0)
       grind)
    | exact resolve eq217897 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217897
  have eq234746 : ∀ X0 : G, x = (k (τ (M.op (σ x) X0)) x) ∨ x = (τ (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq234669 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq234669
    | (have j0 := eq234669 X0
       grind)
    | exact resolve eq234669 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234669
  have eq258574 : ∀ X0 : G, x = (M.op (τ (M.op (σ x) X0)) x) ∨ x = (M.op (τ (M.op (σ x) X0)) x) ∨ x = (τ (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq30 x (τ (M.op (σ x) X0))
       have i₂ := eq234746 X0
       grind)
    | exact superpose eq234746 eq30
    | (have j0 := eq30 x (τ (M.op (σ x) X0))
       have j1 := eq234746 X0
       grind)
    | exact resolve eq30 eq234746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq234746
  have eq258581 : ∀ X0 : G, x = (M.op (τ (M.op (σ x) X0)) x) ∨ x = (τ (M.op (σ x) X0)) := by
    intro X0
    first
    | (have j0 := eq258574 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258574
  have eq261155 : ∀ X0 : G, (τ (M.op (σ x) X0)) = (M.op x (τ (M.op (σ x) X0))) ∨ x = (τ (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq17 (τ (M.op (σ x) X0)) x
       have i₂ := eq258581 X0
       grind)
    | exact superpose eq258581 eq17
    | (have j1 := eq258581 X0
       grind)
    | exact resolve eq17 eq258581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq258581
  have eq733435 : x = (τ (M.op (σ x) (σ x))) ∨ x = (τ (M.op (σ x) (σ x))) ∨ x = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq218087
       have i₂ := eq261155 (σ x)
       grind)
    | exact superpose eq261155 eq218087
    | (have j1 := eq261155 (σ x)
       grind)
    | exact resolve eq218087 eq261155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218087 eq261155
  have eq733471 : x = (τ (M.op (σ x) (σ x))) := by grind
  clear eq733435
  have eq733587 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq10 (M.op (σ x) (σ x))
       have i₂ := eq733471
       grind)
    | exact superpose eq733471 eq10
    | exact resolve eq10 eq733471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq733471
  have eq733734 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq125438
       have i₂ := eq733587
       grind)
    | exact superpose eq733587 eq125438
    | exact resolve eq125438 eq733587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125438 eq733587
  have eq734125 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq733734
       have i₂ := eq212328
       grind)
    | exact superpose eq212328 eq733734
    | exact resolve eq733734 eq212328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212328 eq733734
  have eq734126 : False := by grind
  exact eq734126

/-- The `Equation3` cell the obligation pays for. -/
theorem Equation3_StructuralFromFin_Equation224 : Law3.StructuralFromFin Law224 :=
  AutBox.structuralFromFin_boxIte (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    GuardFix_G0V0_Equation224

/-- `Equation433`: `x = x ◇ (y ◇ (x ◇ (z ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if x = y then D(x, y) else (if Y = m(X,X) then Y else m(X,Y))`, writing `X`, `Y` for `x`,
`y`.  The diagonal value `D` does not appear: the obligation is target-free, so `dcell`-style reuse
can spend it on any target whose law the companion satisfies. -/
theorem GuardFix_G0V1_Equation433 :
    AutBox.GuardFix (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law433 := by
  classical
  refine AutBox.guardFix_of (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hoff x y ↦ ?_)
  have hm := (@Law433.models_iff G M).mp hM
  have ht : ∀ a b : G, b ≠ M.op a a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (b) (M.op a a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, b = M.op a a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (b) (M.op a a)).imp id (helse a b)
  have hd := hoff
  clear hthen helse hoff
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X1)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X2 (M.op X0 (M.op X3 X2))) (M.op X1 X0))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 (M.op X2 (M.op X0 (M.op X3 X2))) X0
       have i₂ := eq8 X0 X2 X3
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq8 (M.op X0 X1) X1 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq22 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X1 X2) (M.op X2 X0)) ∨ (k (M.op X1 X2) X0) = (M.op (M.op X1 X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op X1 X2) X2 X1
       have i₂ := eq12 (M.op X1 X2) X0
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq12 X0 (M.op X0 (M.op X2 X1))
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 (M.op X1 X2) X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (M.op X1 X0)
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq18
    | exact resolve eq18 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X0) (M.op X1 X0))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 (M.op X2 X0) X0
       have i₂ := eq18 X2 X0
       grind)
    | exact superpose eq18 eq8
    | exact resolve eq8 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | (have j0 := eq13 (σ (k (τ X0) X1)) (k X0 (σ X1))
       grind)
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | (have j0 := eq13 (σ (k X1 (τ X0))) (k (σ X1) X0)
       grind)
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq13 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq12 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq20 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq20
    | (have j1 := eq13 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq20 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq53 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq9
    | (have j1 := eq28 (k X0 (σ X1)) (k (τ X0) X1)
       grind)
    | exact resolve eq9 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq69 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 X2)) = (M.op (M.op (M.op X1 X2) (M.op X0 X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X0 (M.op (M.op X1 X2) (M.op X0 X2))
       have i₂ := eq27 X2 X0 X1
       grind)
    | exact superpose eq27 eq18
    | exact resolve eq18 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq29 X1 X0
       have i₂ := eq12 X0 (τ X1)
       grind)
    | exact superpose eq12 eq29
    | (have j0 := eq29 X1 (M.op X0 X0)
       have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq29 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq29 X1 X0
       grind)
    | exact superpose eq29 eq9
    | (have j1 := eq29 (k (σ X0) X1) (k X0 (τ X1))
       grind)
    | exact resolve eq9 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq114 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 (M.op X3 X1))) (M.op X0 X2)) = (M.op (M.op (M.op X1 (M.op X2 (M.op X3 X1))) (M.op X0 X2)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq18 X0 (M.op (M.op X1 (M.op X2 (M.op X3 X1))) (M.op X0 X2))
       have i₂ := eq16 X2 X0 X1 X3
       grind)
    | exact superpose eq16 eq18
    | exact resolve eq18 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq206 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq31 x y
       grind)
    | exact superpose eq31 eq14
    | (have j1 := eq31 x y
       grind)
    | (have r₁ := eq14
       have r₂ := eq31 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq14
       have r₂ := eq31 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq14 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 (σ X0) (σ X1)
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq18
    | (have j1 := eq31 X0 X1
       grind)
    | exact resolve eq18 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq289 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k (M.op X0 X0) X1) = (M.op (M.op X0 X0) X1) ∨ (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X0) X1
       have i₂ := eq22 X0 X0 X0
       grind)
    | exact superpose eq22 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq22 X1 X0 X0
       grind)
    | exact resolve eq12 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq294 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X1 X2) (M.op X0 X1)) ∨ (k (M.op X0 X1) X2) = (M.op (M.op X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 (M.op X0 X1) (M.op X1 X2)
       have i₂ := eq22 X2 X0 X1
       grind)
    | exact superpose eq22 eq18
    | (have j1 := eq22 X2 X0 X1
       grind)
    | exact resolve eq18 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq303 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = (M.op (M.op X0 X0) X1) ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq289 X0 X1
       have i₂ := eq24 X0 X0
       grind)
    | exact superpose eq24 eq289
    | (have j0 := eq289 X0 X1
       grind)
    | exact resolve eq289 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289
  have eq316 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (σ X1) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0 X1
       have i₂ := eq12 X0 (σ X1)
       grind)
    | exact superpose eq12 eq53
    | (have j0 := eq53 (M.op X0 (σ X1)) (k (τ X0) X1)
       have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq53 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq329 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (M.op (σ X0) (σ X0)))) ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0
    grind
  have eq591 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ (k X0 X1))) ∨ (σ (k X0 X1)) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 (σ X0) (σ X1)
       have i₂ := eq39 X0 X1
       grind)
    | exact superpose eq39 eq18
    | (have j1 := eq39 X0 X1
       grind)
    | exact resolve eq18 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq1662 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq206
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq206
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq206 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq1664 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by grind
  clear eq1662
  have eq2112 : (σ y) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) := by grind
  clear eq1664
  have eq2686 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ (k X1 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq24 (σ X0) (σ X0)
       have i₂ := eq210 X0 X1
       grind)
    | exact superpose eq210 eq24
    | (have j1 := eq210 X1 X0
       grind)
    | exact resolve eq24 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq2739 : (τ (σ y)) = (k x (τ (σ y))) ∨ x = (τ (σ y)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq78 x (σ y)
       have i₂ := eq2112
       grind)
    | exact superpose eq2112 eq78
    | (have j0 := eq78 (k x (τ (σ y))) (σ y)
       grind)
    | exact resolve eq78 eq2112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq2112
  have eq2750 : y = (k x y) ∨ x = (τ (σ y)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2739
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq2739
    | exact resolve eq2739 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2739
  have eq2752 : x = y ∨ y = (k x y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2750
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq2750
    | exact resolve eq2750 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2750
  have eq2753 : y = (k x y) ∨ x = y ∨ y = (M.op x x) := by grind
  clear eq2752
  have eq2874 : y = (M.op x y) ∨ y = (M.op x x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq2753
       grind)
    | exact superpose eq2753 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq2753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2753
  have eq2881 : y = (M.op x y) ∨ y = (M.op x x) ∨ x = y := by grind
  clear eq2874
  have eq3073 : ∀ X0 : G, (M.op X0 (M.op y (M.op X0 y))) = X0 ∨ y = (M.op x x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq27 y X0 x
       have i₂ := eq2881
       grind)
    | exact superpose eq2881 eq27
    | exact resolve eq27 eq2881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3114 : ∀ X0 : G, y = (M.op x x) ∨ (M.op X0 y) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq3073 X0
       have i₂ := eq18 X0 y
       grind)
    | exact superpose eq18 eq3073
    | exact resolve eq3073 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3073
  have eq3782 : x = y ∨ y = (M.op x x) ∨ x = y ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq2881
       have i₂ := eq3114 x
       grind)
    | exact superpose eq3114 eq2881
    | exact resolve eq2881 eq3114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2881 eq3114
  have eq3783 : y = (M.op x x) ∨ x = y := by grind
  clear eq3782
  have eq4026 : x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq18 x x
       have i₂ := eq3783
       grind)
    | exact superpose eq3783 eq18
    | exact resolve eq18 eq3783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6073 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 X0))) = (M.op (M.op X0 (M.op X0 (M.op X1 X0))) X2) ∨ (k (M.op X2 X0) (M.op X0 (M.op X1 X0))) = (M.op (M.op X2 X0) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq114 X0 X1 X1 x
       have i₂ := eq294 X0 X1 (M.op X1 (M.op x X1))
       grind)
    | exact superpose eq294 eq114
    | (have j1 := eq294 X2 X0 (M.op X0 (M.op X1 X0))
       grind)
    | exact resolve eq114 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq294
  have eq6159 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X2) ∨ (k (M.op X2 X0) (M.op X0 (M.op X1 X0))) = (M.op (M.op X2 X0) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6073 X1 X0 X2
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq6073
    | (have j0 := eq6073 X0 X1 X2
       grind)
    | exact resolve eq6073 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6073
  have eq6160 : ∀ X0 X2 : G, (k (M.op X2 X0) X0) = (M.op (M.op X2 X0) X0) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) X2) := by
    intro X0 X2
    first
    | (have i₁ := eq6159 x X0 X2
       have i₂ := eq18 X0 x
       grind)
    | exact superpose eq18 eq6159
    | (have j0 := eq6159 X0 x X2
       grind)
    | exact resolve eq6159 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6159
  have eq6161 : ∀ X0 X2 : G, (M.op X2 X0) = (k (M.op X2 X0) X0) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) X2) := by
    intro X0 X2
    first
    | (have i₁ := eq6160 X0 X2
       have i₂ := eq24 X0 X2
       grind)
    | exact superpose eq24 eq6160
    | (have j0 := eq6160 X0 X2
       grind)
    | exact resolve eq6160 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq6160
  have eq6940 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X0) X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq303 X0 (k (M.op X0 X0) X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq6947 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq6940 X0
       have j1 := eq6161 X0 X0
       grind)
    | (have r₁ := eq6940 x
       have r₂ := eq6161 x x
       grind)
    | exact resolve eq6940 eq6161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6161 eq6940
  have eq7790 : y = (k y x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq6947 x
       have i₂ := eq3783
       grind)
    | exact superpose eq3783 eq6947
    | exact resolve eq6947 eq3783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3783
  have eq7823 : y = (k y x) ∨ x = y := by grind
  clear eq7790
  have eq34162 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq591 y x
       have i₂ := eq7823
       grind)
    | exact superpose eq7823 eq591
    | (have j0 := eq591 (σ x) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq591 eq7823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591 eq7823
  have eq34343 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq34162
  have eq35376 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq34343
       grind)
    | exact superpose eq34343 eq14
    | exact resolve eq14 eq34343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34343
  have eq35841 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq35376
       have i₂ := eq4026
       grind)
    | exact superpose eq4026 eq35376
    | exact resolve eq35376 eq4026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4026 eq35376
  have eq35849 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq35841
  have eq35850 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq35849
  have eq36153 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq35850
       grind)
    | exact superpose eq35850 eq9
    | exact resolve eq9 eq35850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35850
  have eq36252 : x = y ∨ x = y := by
    first
    | (have i₁ := eq36153
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq36153
    | exact resolve eq36153 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36153
  have eq36253 : x = y := by grind
  clear eq36252
  have eq36864 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq36253
       grind)
    | exact superpose eq36253 eq14
    | exact resolve eq14 eq36253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36253
  have eq54842 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2686 X0 (M.op X0 X0)
       have i₂ := eq6947 X0
       grind)
    | exact superpose eq6947 eq2686
    | (have j0 := eq2686 X0 (M.op X0 X0)
       have j1 := eq6947 X0
       grind)
    | exact resolve eq2686 eq6947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2686 eq6947
  have eq55118 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq54842 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54842
  have eq55302 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ X0)) (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (τ (σ X0)) = (M.op X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq316 (σ X0) (M.op X0 X0)
       have i₂ := eq55118 X0
       grind)
    | exact superpose eq55118 eq316
    | (have j0 := eq316 (σ X0) (M.op X0 X0)
       have j1 := eq55118 X0
       grind)
    | exact resolve eq316 eq55118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316 eq55118
  have eq55433 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (τ (σ X0)) = (M.op X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq55302 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq55302
    | (have j0 := eq55302 X0
       grind)
    | exact resolve eq55302 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55302
  have eq55459 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (τ (σ X0)) = (M.op X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    grind
  clear eq55433
  have eq55460 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (τ (σ X0)) = (M.op X0 X0) := by
    intro X0
    first
    | (have j0 := eq55459 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55459
  have eq55462 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq55460 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq55460
    | (have j0 := eq55460 X0
       grind)
    | exact resolve eq55460 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55460
  have eq55463 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq55462 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55462
  have eq55675 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq36864
       have i₂ := eq55463 x
       grind)
    | exact superpose eq55463 eq36864
    | (have j1 := eq55463 x
       grind)
    | (have r₁ := eq36864
       have r₂ := eq55463 x
       grind)
    | exact resolve eq36864 eq55463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55463
  have eq55846 : x = (M.op x x) := by grind
  clear eq55675
  have eq56241 : ∀ X0 : G, (M.op X0 (M.op x (M.op X0 x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq27 x X0 x
       have i₂ := eq55846
       grind)
    | exact superpose eq55846 eq27
    | exact resolve eq27 eq55846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq56252 : ∀ X0 : G, (M.op x (M.op X0 x)) = (M.op (M.op x (M.op X0 x)) X0) := by
    intro X0
    first
    | (have i₁ := eq69 X0 x x
       have i₂ := eq55846
       grind)
    | exact superpose eq55846 eq69
    | exact resolve eq69 eq55846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq55846
  have eq56355 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq56252 X0
       have i₂ := eq18 X0 x
       grind)
    | exact superpose eq18 eq56252
    | exact resolve eq56252 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56252
  have eq56358 : ∀ X0 : G, (M.op X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq56241 X0
       have i₂ := eq18 X0 x
       grind)
    | exact superpose eq18 eq56241
    | exact resolve eq56241 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq56241
  have eq57515 : ∀ X0 : G, (σ x) = (k (σ x) X0) ∨ (τ X0) = (M.op x x) ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq73 x X0
       have i₂ := eq56355 (τ X0)
       grind)
    | exact superpose eq56355 eq73
    | (have j0 := eq73 x X0
       grind)
    | exact resolve eq73 eq56355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq56355
  have eq57543 : ∀ X0 : G, (τ X0) = x ∨ (σ x) = (k (σ x) X0) ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq57515 X0
       have i₂ := eq56358 x
       grind)
    | exact superpose eq56358 eq57515
    | (have j0 := eq57515 X0
       grind)
    | exact resolve eq57515 eq56358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57515
  have eq57544 : ∀ X0 : G, (σ x) = (k (σ x) X0) ∨ (τ X0) = x := by
    intro X0
    first
    | (have j0 := eq57543 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57543
  have eq62732 : ∀ X0 : G, (τ (σ x)) = (k (τ (σ x)) X0) ∨ (τ (σ x)) = X0 ∨ (τ (σ X0)) = x := by
    intro X0
    first
    | (have i₁ := eq53 (σ x) X0
       have i₂ := eq57544 (σ X0)
       grind)
    | exact superpose eq57544 eq53
    | (have j0 := eq53 (σ x) (k (τ (σ x)) X0)
       have j1 := eq57544 (σ X0)
       grind)
    | exact resolve eq53 eq57544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq57544
  have eq62781 : ∀ X0 : G, x = (k x X0) ∨ (τ (σ x)) = X0 ∨ (τ (σ X0)) = x := by
    intro X0
    first
    | (have i₁ := eq62732 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq62732
    | (have j0 := eq62732 X0
       grind)
    | exact resolve eq62732 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62732
  have eq62811 : ∀ X0 : G, x = X0 ∨ x = (k x X0) ∨ (τ (σ X0)) = x := by
    intro X0
    first
    | (have i₁ := eq62781 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq62781
    | (have j0 := eq62781 X0
       grind)
    | exact resolve eq62781 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62781
  have eq62820 : ∀ X0 : G, x = X0 ∨ x = X0 ∨ x = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq62811 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq62811
    | (have j0 := eq62811 X0
       grind)
    | exact resolve eq62811 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62811
  have eq62821 : ∀ X0 : G, x = (k x X0) ∨ x = X0 := by
    intro X0
    first
    | (have j0 := eq62820 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62820
  have eq64322 : x = (τ (M.op (σ x) (σ x))) ∨ x = (τ (M.op (σ x) (σ x))) ∨ x = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq329 x
       have i₂ := eq62821 (τ (M.op (σ x) (σ x)))
       grind)
    | exact superpose eq62821 eq329
    | (have j0 := eq329 x
       have j1 := eq62821 (τ (M.op (σ x) (σ x)))
       grind)
    | exact resolve eq329 eq62821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329 eq62821
  have eq64327 : x = (τ (M.op (σ x) (σ x))) := by grind
  clear eq64322
  have eq65649 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq10 (M.op (σ x) (σ x))
       have i₂ := eq64327
       grind)
    | exact superpose eq64327 eq10
    | exact resolve eq10 eq64327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64327
  have eq67037 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq36864
       have i₂ := eq65649
       grind)
    | exact superpose eq65649 eq36864
    | exact resolve eq36864 eq65649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36864 eq65649
  have eq67227 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq67037
       have i₂ := eq56358 x
       grind)
    | exact superpose eq56358 eq67037
    | exact resolve eq67037 eq56358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56358 eq67037
  have eq67228 : False := by grind
  exact eq67228

/-- The `Equation3` cell the obligation pays for. -/
theorem Equation3_StructuralFromFin_Equation433 : Law3.StructuralFromFin Law433 :=
  AutBox.structuralFromFin_boxIte (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    GuardFix_G0V1_Equation433

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if x = y then D(x, y) else (if Y = m(X,X) then Y else m(X,Y))`, writing `X`, `Y` for `x`,
`y`.  The diagonal value `D` does not appear: the obligation is target-free, so `dcell`-style reuse
can spend it on any target whose law the companion satisfies. -/
theorem GuardFix_G0V1_Equation434 :
    AutBox.GuardFix (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law434 := by
  classical
  refine AutBox.guardFix_of (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hoff x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, b ≠ M.op a a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (b) (M.op a a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, b = M.op a a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (b) (M.op a a)).imp id (helse a b)
  have hd := hoff
  clear hthen helse hoff
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 (M.op X0 (M.op x x))
       have i₂ := eq8 X0 (M.op X0 (M.op x x)) x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq8 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq25 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op X1 X0) X0
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | (have j0 := eq13 (σ (k (τ X0) X1)) (k X0 (σ X1))
       grind)
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | (have j0 := eq13 (σ (k X1 (τ X0))) (k (σ X1) X0)
       grind)
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq13 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq12 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X1 ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X2 X1
       have i₂ := eq12 X2 X0
       grind)
    | (have i₁ := eq17 X0 X1
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq17
    | (have j1 := eq12 X2 X0
       grind)
    | exact resolve eq17 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k (M.op X0 X0) X1) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X0) X1
       have i₂ := eq17 X0 (M.op X0 X0)
       grind)
    | exact superpose eq17 eq12
    | (have j0 := eq12 X0 X1
       grind)
    | exact resolve eq12 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op X1 X1) X0
       have i₂ := eq17 X1 X0
       grind)
    | exact superpose eq17 eq16
    | exact resolve eq16 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq39 X0 X1
       have i₂ := eq42 X1 X0
       grind)
    | (have i₁ := eq39 X0 (M.op X0 X0)
       have i₂ := eq42 X0 (M.op X0 X0)
       grind)
    | exact superpose eq42 eq39
    | (have j0 := eq39 X0 (k (M.op X0 X0) X1)
       grind)
    | exact resolve eq39 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq48 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq20 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    grind
  have eq82 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq30 X0 X1
       grind)
    | exact superpose eq30 eq9
    | (have j1 := eq30 (k X0 (σ X1)) (k (τ X0) X1)
       grind)
    | exact resolve eq9 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq87 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k (M.op X0 X1) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq48 (M.op X0 X1) X1
       have i₂ := eq25 X1 X0
       grind)
    | exact superpose eq25 eq48
    | (have j0 := eq48 X0 X1
       grind)
    | exact resolve eq48 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq93 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (τ X1) = (k X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X1 X0
       have i₂ := eq20 (τ X1) X0
       grind)
    | exact superpose eq20 eq31
    | (have j0 := eq31 X1 X0
       have j1 := eq20 (τ X1) X0
       grind)
    | exact resolve eq31 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq9
    | (have j1 := eq31 (k (σ X0) X1) (k X0 (τ X1))
       grind)
    | exact resolve eq9 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq161 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq35 (σ y) (σ x) X0
       grind)
    | exact superpose eq35 eq14
    | (have j1 := eq35 (σ y) x X0
       grind)
    | exact resolve eq14 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq216 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq33 x y
       grind)
    | exact superpose eq33 eq14
    | (have j1 := eq33 x y
       grind)
    | (have r₁ := eq14
       have r₂ := eq33 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq14
       have r₂ := eq33 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq14 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq424 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (M.op (σ X0) (σ X0)))) ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0
    grind
  have eq941 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (k x y) := by
    first
    | (have i₁ := eq216
       have i₂ := eq20 y x
       grind)
    | exact superpose eq20 eq216
    | (have j1 := eq20 y x
       grind)
    | exact resolve eq216 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq216
  have eq953 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (k x y) := by grind
  clear eq941
  have eq1326 : ∀ X0 X1 : G, (σ (M.op X0 (τ X1))) = (k (σ (M.op X0 (τ X1))) X1) ∨ (τ X1) = (M.op X0 (τ X1)) ∨ (τ X1) = (k (M.op X0 (τ X1)) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq93 (M.op X0 (τ X1)) X1
       have i₂ := eq25 (τ X1) X0
       grind)
    | exact superpose eq25 eq93
    | (have j0 := eq93 (M.op X0 (τ X1)) X1
       grind)
    | exact resolve eq93 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq1368 : ∀ X0 X1 : G, (σ (M.op X0 (τ X1))) = (k (σ (M.op X0 (τ X1))) X1) ∨ (τ X1) = (k (M.op X0 (τ X1)) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1326 X0 X1
       have j1 := eq87 X0 (τ X1)
       grind)
    | (have r₁ := eq1326 X0 X1
       have r₂ := eq87 X0 (τ X1)
       grind)
    | exact resolve eq1326 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1326
  have eq1843 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq76 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq76
    | exact resolve eq76 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq2380 : (σ y) = (k (σ x) (σ y)) ∨ x = y ∨ y = (k x y) := by grind
  clear eq953
  have eq9199 : (τ (σ y)) = (k x (τ (σ y))) ∨ x = (τ (σ y)) ∨ x = y ∨ y = (k x y) := by
    first
    | (have i₁ := eq99 x (σ y)
       have i₂ := eq2380
       grind)
    | exact superpose eq2380 eq99
    | (have j0 := eq99 (k x (τ (σ y))) (σ y)
       grind)
    | exact resolve eq99 eq2380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2380
  have eq9236 : y = (k x y) ∨ x = (τ (σ y)) ∨ x = y ∨ y = (k x y) := by
    first
    | (have i₁ := eq9199
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq9199
    | exact resolve eq9199 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9199
  have eq9237 : y = (k x y) ∨ x = (τ (σ y)) ∨ x = y := by grind
  clear eq9236
  have eq9257 : x = y ∨ y = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq9237
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq9237
    | exact resolve eq9237 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9237
  have eq9258 : y = (k x y) ∨ x = y := by grind
  clear eq9257
  have eq9489 : y = (M.op x y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq9258
       grind)
    | exact superpose eq9258 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq9258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9493 : ∀ X0 : G, y = (M.op x y) ∨ (M.op X0 y) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq35 y X0 x
       have i₂ := eq9258
       grind)
    | exact superpose eq9258 eq35
    | (have j0 := eq35 y X0 x
       grind)
    | exact resolve eq35 eq9258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq9258
  have eq10171 : ∀ X0 : G, y = (M.op y y) ∨ (M.op X0 y) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq25 y x
       have i₂ := eq9493 X0
       grind)
    | exact superpose eq9493 eq25
    | (have j1 := eq9493 y
       grind)
    | exact resolve eq25 eq9493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9493
  have eq11231 : y ≠ y ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have j0 := eq10171 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10171
  have eq11232 : y = (M.op y y) ∨ x = y := by grind
  clear eq11231
  have eq11504 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq17 y X0
       have i₂ := eq11232
       grind)
    | exact superpose eq11232 eq17
    | exact resolve eq17 eq11232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11232
  have eq11851 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq161 X0
       have i₂ := eq11504 x
       grind)
    | exact superpose eq11504 eq161
    | (have j0 := eq161 X0
       grind)
    | exact resolve eq161 eq11504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161
  have eq11857 : x = y ∨ y = (M.op x x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq9489
       have i₂ := eq11504 x
       grind)
    | exact superpose eq11504 eq9489
    | exact resolve eq9489 eq11504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9489
  have eq11860 : y = (M.op x x) ∨ x = y := by grind
  clear eq11857
  have eq11870 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq11851 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11851
  have eq12580 : (σ y) = (k (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq1843 x
       have i₂ := eq11860
       grind)
    | exact superpose eq11860 eq1843
    | exact resolve eq1843 eq11860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1843 eq11860
  have eq12591 : (σ y) = (k (σ x) (σ y)) ∨ x = y := by grind
  clear eq12580
  have eq15517 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq12591
       have i₂ := eq11870 (σ x)
       grind)
    | exact superpose eq11870 eq12591
    | exact resolve eq12591 eq11870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11870 eq12591
  have eq15534 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq15517
  have eq16221 : (σ (M.op x y)) ≠ (σ y) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq15534
       grind)
    | exact superpose eq15534 eq14
    | exact resolve eq14 eq15534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16245 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq25 (σ y) (σ x)
       have i₂ := eq15534
       grind)
    | exact superpose eq15534 eq25
    | exact resolve eq25 eq15534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq16635 : (σ x) ≠ (σ y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq16221
       have i₂ := eq11504 x
       grind)
    | exact superpose eq11504 eq16221
    | exact resolve eq16221 eq11504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11504 eq16221
  have eq16638 : (σ x) ≠ (σ y) ∨ x = y := by grind
  clear eq16635
  have eq17119 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq17 (σ y) X0
       have i₂ := eq16245
       grind)
    | exact superpose eq16245 eq17
    | exact resolve eq17 eq16245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16245
  have eq17383 : (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq15534
       have i₂ := eq17119 (σ x)
       grind)
    | exact superpose eq17119 eq15534
    | exact resolve eq15534 eq17119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15534 eq17119
  have eq17410 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq17383
  have eq17418 : x = y := by
    first
    | (have r₁ := eq17410
       have r₂ := eq16638
       grind)
    | exact resolve eq17410 eq16638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16638 eq17410
  have eq17621 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq17418
       grind)
    | exact superpose eq17418 eq14
    | exact resolve eq14 eq17418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17418
  have eq38837 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) ∨ (M.op X0 X0) = (τ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) ∨ (M.op X0 X0) = (τ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq43 X0 (τ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))))
       have i₂ := eq424 (M.op X0 X0)
       grind)
    | exact superpose eq424 eq43
    | (have j0 := eq43 X0 (τ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))))
       have j1 := eq424 (M.op X0 X0)
       grind)
    | exact resolve eq43 eq424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq424
  have eq38897 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have j0 := eq38837 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38837
  have eq39253 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))
       have i₂ := eq38897 X0
       grind)
    | exact superpose eq38897 eq10
    | exact resolve eq10 eq38897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40259 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 (σ (M.op X0 X0)) X1
       have i₂ := eq39253 X0
       grind)
    | exact superpose eq39253 eq17
    | exact resolve eq17 eq39253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39253
  have eq43481 : ∀ X0 X1 : G, (τ (σ (M.op X0 (τ (σ X1))))) = (k (τ (σ (M.op X0 (τ (σ X1))))) X1) ∨ (τ (σ (M.op X0 (τ (σ X1))))) = X1 ∨ (τ (σ X1)) = (k (M.op X0 (τ (σ X1))) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq82 (σ (M.op X0 (τ (σ X1)))) X1
       have i₂ := eq1368 X0 (σ X1)
       grind)
    | exact superpose eq1368 eq82
    | (have j0 := eq82 (σ (M.op X0 (τ (σ X1)))) (k (τ (σ (M.op X0 (τ (σ X1))))) X1)
       have j1 := eq1368 X0 (σ X1)
       grind)
    | exact resolve eq82 eq1368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq1368
  have eq43531 : ∀ X0 X1 : G, (M.op X0 (τ (σ X1))) = (k (M.op X0 (τ (σ X1))) X1) ∨ (τ (σ (M.op X0 (τ (σ X1))))) = X1 ∨ (τ (σ X1)) = (k (M.op X0 (τ (σ X1))) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq43481 X0 X1
       have i₂ := eq9 (M.op X0 (τ (σ X1)))
       grind)
    | exact superpose eq9 eq43481
    | (have j0 := eq43481 X0 X1
       grind)
    | exact resolve eq43481 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43481
  have eq43584 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X1) ∨ (τ (σ (M.op X0 (τ (σ X1))))) = X1 ∨ (τ (σ X1)) = (k (M.op X0 (τ (σ X1))) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq43531 X0 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq43531
    | (have j0 := eq43531 X0 X1
       grind)
    | exact resolve eq43531 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43531
  have eq43605 : ∀ X0 X1 : G, (M.op X0 (τ (σ X1))) = X1 ∨ (M.op X0 X1) = (k (M.op X0 X1) X1) ∨ (τ (σ X1)) = (k (M.op X0 (τ (σ X1))) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq43584 X0 X1
       have i₂ := eq9 (M.op X0 (τ (σ X1)))
       grind)
    | exact superpose eq9 eq43584
    | (have j0 := eq43584 X0 X1
       grind)
    | exact resolve eq43584 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43584
  have eq43620 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k (M.op X0 X1) X1) ∨ (τ (σ X1)) = (k (M.op X0 (τ (σ X1))) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq43605 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq43605
    | (have j0 := eq43605 X0 X1
       grind)
    | exact resolve eq43605 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43605
  have eq43635 : ∀ X0 X1 : G, (k (M.op X0 X1) X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq43620 X0 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq43620
    | (have j0 := eq43620 X0 X1
       grind)
    | exact resolve eq43620 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43620
  have eq43646 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X1) ∨ (k (M.op X0 X1) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq43635 X0 X1
       have j1 := eq87 X0 X1
       grind)
    | (have r₁ := eq43635 X0 X1
       have r₂ := eq87 X0 X1
       grind)
    | exact resolve eq43635 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq43635
  have eq67679 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 (M.op X1 X0)) ∨ (k X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq43646 X0 (M.op X1 X0)
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq43646
    | exact resolve eq43646 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43646
  have eq70347 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X1)
       have i₂ := eq67679 X1 X0
       grind)
    | exact superpose eq67679 eq12
    | (have j0 := eq12 X1 (M.op X0 X1)
       have j1 := eq67679 X1 X0
       grind)
    | exact resolve eq12 eq67679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70449 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq67679 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67679
  have eq70537 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq70347 X0 X1
       have i₂ := eq16 X1 X0
       grind)
    | exact superpose eq16 eq70347
    | (have j0 := eq70347 X0 X1
       grind)
    | exact resolve eq70347 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq70347
  have eq70573 : ∀ X0 X1 : G, (k X1 (M.op X0 X1)) = X1 ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq70537 X0 X1
       have j1 := eq70449 X1 X0
       grind)
    | (have r₁ := eq70537 X1 X0
       have r₂ := eq70449 X0 X1
       grind)
    | exact resolve eq70537 eq70449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70537
  have eq71447 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq70449 X0 (M.op X1 X1)
       have i₂ := eq42 X0 X1
       grind)
    | exact superpose eq42 eq70449
    | (have r₁ := eq70449 (M.op X1 X1) (M.op X1 X1)
       have r₂ := eq42 (M.op X1 X1) X1
       grind)
    | exact resolve eq70449 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70449
  have eq77253 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq70573 (M.op X1 X1) X0
       have i₂ := eq42 X0 X1
       grind)
    | exact superpose eq42 eq70573
    | exact resolve eq70573 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq70573
  have eq83268 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (M.op X0 X0)) ∨ (k X0 (M.op (σ (M.op X1 X1)) (σ (M.op X1 X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq38897 X1
       have i₂ := eq77253 (σ (M.op X1 X1)) X0
       grind)
    | (have i₁ := eq38897 X0
       have i₂ := eq77253 X0 (σ (M.op X0 X0))
       grind)
    | exact superpose eq77253 eq38897
    | (have j1 := eq77253 (σ (M.op X1 X1)) X0
       grind)
    | exact resolve eq38897 eq77253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38897 eq77253
  have eq83522 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 X1))) = X0 ∨ (M.op X1 X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq83268 X0 X1
       have i₂ := eq40259 X1 (σ (M.op X1 X1))
       grind)
    | exact superpose eq40259 eq83268
    | (have j0 := eq83268 X0 X1
       grind)
    | exact resolve eq83268 eq40259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83268
  have eq122832 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ (M.op X1 X1)))) ∨ (τ (σ (M.op X1 X1))) = X0 ∨ (M.op X1 X1) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq99 X0 (σ (M.op X1 X1))
       have i₂ := eq83522 (σ X0) X1
       grind)
    | exact superpose eq83522 eq99
    | (have j0 := eq99 (k X0 (τ (σ (M.op X1 X1)))) (σ X0)
       have j1 := eq83522 (σ X0) X1
       grind)
    | exact resolve eq99 eq83522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq83522
  have eq123087 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (M.op X1 X1)) ∨ (τ (σ (M.op X1 X1))) = X0 ∨ (M.op X1 X1) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq122832 X0 X1
       have i₂ := eq9 (M.op X1 X1)
       grind)
    | exact superpose eq9 eq122832
    | (have j0 := eq122832 X0 X1
       grind)
    | exact resolve eq122832 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122832
  have eq123110 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) = X0 ∨ (τ (σ (M.op X1 X1))) = X0 ∨ (M.op X1 X1) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq123087 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq123087
    | (have j0 := eq123087 X0 X1
       grind)
    | exact resolve eq123087 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123087
  have eq123111 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 (M.op X1 X1)) = X0 ∨ (M.op X1 X1) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq123110 X0 X1
       have i₂ := eq9 (M.op X1 X1)
       grind)
    | exact superpose eq9 eq123110
    | (have j0 := eq123110 X0 X1
       grind)
    | exact resolve eq123110 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123110
  have eq123112 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) = X0 ∨ (M.op X1 X1) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq123111 X0 X1
       have j1 := eq71447 X1 X0
       grind)
    | (have r₁ := eq123111 X1 X0
       have r₂ := eq71447 X0 X1
       grind)
    | (have r₁ := eq123111 (M.op X0 X0) X1
       have r₂ := eq71447 X0 (M.op X1 X1)
       grind)
    | (have r₁ := eq123111 (M.op X0 X0) X1
       have r₂ := eq71447 X0 (k (M.op X0 X0) (M.op X1 X1))
       grind)
    | exact resolve eq123111 eq71447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71447 eq123111
  have eq424276 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    grind
  clear eq123112
  have eq426580 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (σ X0) (σ X0))
       have i₂ := eq424276 X0
       grind)
    | exact superpose eq424276 eq10
    | (have j1 := eq424276 X0
       grind)
    | exact resolve eq10 eq424276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424276
  have eq428690 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq17621
       have i₂ := eq426580 x
       grind)
    | exact superpose eq426580 eq17621
    | (have j1 := eq426580 x
       grind)
    | (have r₁ := eq17621
       have r₂ := eq426580 x
       grind)
    | exact resolve eq17621 eq426580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426580
  have eq428891 : x = (M.op x x) := by grind
  clear eq428690
  have eq432028 : ∀ X0 : G, (M.op X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq17 x X0
       have i₂ := eq428891
       grind)
    | exact superpose eq428891 eq17
    | exact resolve eq17 eq428891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq432058 : ∀ X0 : G, (M.op X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq40259 x X0
       have i₂ := eq428891
       grind)
    | exact superpose eq428891 eq40259
    | exact resolve eq40259 eq428891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40259 eq428891
  have eq446460 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq17621
       have i₂ := eq432058 (σ x)
       grind)
    | exact superpose eq432058 eq17621
    | exact resolve eq17621 eq432058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17621 eq432058
  have eq446499 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq446460
       have i₂ := eq432028 x
       grind)
    | exact superpose eq432028 eq446460
    | exact resolve eq446460 eq432028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432028 eq446460
  have eq446500 : False := by grind
  exact eq446500

/-- The `Equation3` cell the obligation pays for. -/
theorem Equation3_StructuralFromFin_Equation434 : Law3.StructuralFromFin Law434 :=
  AutBox.structuralFromFin_boxIte (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    GuardFix_G0V1_Equation434
