import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pxy_pxy_pxx_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = X1 := by
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
  have eq55 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 (M.op (M.op X2 X1) X0)) ∨ (M.op (M.op X2 X1) X0) = (M.op (M.op (M.op X2 X1) X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op (M.op X2 X1) X0)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 X0 (M.op (M.op X2 X1) X0)
       grind)
    | (have r₁ := eq13 X1 (M.op (M.op X2 X1) X1)
       have r₂ := eq9 X1 X1 X2
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq56 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq56 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq56 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq59 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq57 (σ X0)
       grind)
    | exact superpose eq57 eq15
    | exact resolve eq15 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq57 (τ X0)
       grind)
    | exact superpose eq57 eq18
    | exact resolve eq18 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq62 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq62
    | exact resolve eq62 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq68 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq59 X0
       have i₂ := eq57 X0
       grind)
    | exact superpose eq57 eq59
    | exact resolve eq59 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq71 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq65 X0
       have i₂ := eq57 X0
       grind)
    | exact superpose eq57 eq65
    | exact resolve eq65 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq65
  have eq87 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq93 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq87 X0 X1
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq87
    | (have j0 := eq87 X0 X1
       grind)
    | exact resolve eq87 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq129 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = (M.op X1 (M.op (σ (M.op X0 X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 X2 (σ X0) X1 (σ X0)
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq21
    | exact resolve eq21 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq340 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op (σ X1) X0) := by
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
  clear eq93
  have eq374 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq340 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq340
    | (have j0 := eq340 X0 X1
       grind)
    | exact resolve eq340 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340
  have eq378 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq374 X0 X1
       have j1 := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq374 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq374 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374
  have eq381 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq378 X0 X1
       have i₂ := eq71 X0
       grind)
    | exact superpose eq71 eq378
    | (have j0 := eq378 X0 X1
       grind)
    | exact resolve eq378 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378
  have eq464 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (M.op (M.op (M.op X1 X0) X0) X0) ∨ (M.op X0 X0) = (k X0 (M.op (M.op X1 X0) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq568 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq381 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq381
    | exact resolve eq381 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq579 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq381 (σ X0) X1
       grind)
    | exact superpose eq381 eq15
    | (have j1 := eq381 (σ X0) X1
       grind)
    | exact resolve eq15 eq381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381
  have eq590 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq579 X0 X1
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq579
    | (have j0 := eq579 X0 X1
       grind)
    | exact resolve eq579 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579
  have eq605 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq568 (τ X1) X0
       grind)
    | exact superpose eq568 eq18
    | (have j1 := eq568 (τ X1) X0
       grind)
    | exact resolve eq18 eq568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq980 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) ≠ (M.op (M.op X0 X1) X1) ∨ (k X1 (M.op (M.op X0 X1) X1)) = (M.op X1 (M.op (M.op X0 X1) X1)) ∨ (M.op X1 X1) = (k X1 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op (M.op X0 X1) X1)
       have i₂ := eq464 X1 X0
       grind)
    | exact superpose eq464 eq12
    | (have j0 := eq12 X1 (M.op (M.op X0 X1) X1)
       have j1 := eq464 X1 X0
       grind)
    | (have r₁ := eq12 X0 (M.op (M.op X1 X0) X0)
       have r₂ := eq464 X0 X1
       grind)
    | exact resolve eq12 eq464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464
  have eq992 : ∀ X0 X1 : G, (k X1 (M.op (M.op X0 X1) X1)) = (M.op X1 (M.op (M.op X0 X1) X1)) ∨ (M.op X1 X1) = (k X1 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq980 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq980
  have eq1000 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op (M.op X0 X1) X1)) ∨ (M.op X1 X1) = (k X1 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq992 X0 X1
       have i₂ := eq9 X1 X1 X0
       grind)
    | exact superpose eq9 eq992
    | (have j0 := eq992 X0 X1
       grind)
    | exact resolve eq992 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq992
  have eq1001 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1000 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1000
  have eq1092 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (M.op (M.op X1 (σ X0)) (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 (M.op (M.op X1 (σ X0)) (σ X0))
       have i₂ := eq1001 X1 (σ X0)
       grind)
    | exact superpose eq1001 eq31
    | exact resolve eq31 eq1001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq1093 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (M.op (M.op X1 (τ X0)) (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (M.op (M.op X1 (τ X0)) (τ X0))
       have i₂ := eq1001 X1 (τ X0)
       grind)
    | exact superpose eq1001 eq17
    | exact resolve eq17 eq1001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1001
  have eq1103 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (σ (M.op (M.op X1 (τ X0)) (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1093 X0 X1
       have i₂ := eq71 X0
       grind)
    | exact superpose eq71 eq1093
    | exact resolve eq1093 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq1093
  have eq1104 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = (k X0 (τ (M.op (M.op X1 (σ X0)) (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1092 X0 X1
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq1092
    | exact resolve eq1092 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1092
  have eq1123 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (τ (M.op (M.op X1 (σ X0)) (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1104 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq1104
    | exact resolve eq1104 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1104
  have eq1164 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (σ (M.op (M.op X1 (τ X0)) (τ X0)))) ∨ (M.op X0 X0) = (M.op X0 (σ (M.op (M.op X1 (τ X0)) (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq568 (σ (M.op (M.op X1 (τ X0)) (τ X0))) X0
       have i₂ := eq1103 X0 X1
       grind)
    | exact superpose eq1103 eq568
    | (have j0 := eq568 (σ (M.op (M.op X1 (τ X0)) (τ X0))) X0
       grind)
    | exact resolve eq568 eq1103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1103
  have eq1179 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (σ (M.op (M.op X1 (τ X0)) (τ X0)))) := by
    intro X0 X1
    first
    | (have j0 := eq1164 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1164
  have eq1294 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (τ (M.op (M.op X1 (σ X0)) (σ X0)))) ∨ (M.op X0 X0) = (M.op X0 (τ (M.op (M.op X1 (σ X0)) (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq568 (τ (M.op (M.op X1 (σ X0)) (σ X0))) X0
       have i₂ := eq1123 X0 X1
       grind)
    | exact superpose eq1123 eq568
    | (have j0 := eq568 (τ (M.op (M.op X1 (σ X0)) (σ X0))) X0
       grind)
    | exact resolve eq568 eq1123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568 eq1123
  have eq1307 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (τ (M.op (M.op X1 (σ X0)) (σ X0)))) := by
    intro X0 X1
    first
    | (have j0 := eq1294 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1294
  have eq1564 : ∀ X0 X1 X2 X3 : G, (M.op X1 (σ (M.op (M.op X2 (τ X0)) (τ X0)))) = (M.op X1 (M.op (M.op X0 X0) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21 X3 (σ (M.op (M.op X2 (τ X0)) (τ X0))) X1 X0
       have i₂ := eq1179 X0 X2
       grind)
    | exact superpose eq1179 eq21
    | exact resolve eq21 eq1179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1179
  have eq1584 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 (σ (M.op (M.op X2 (τ X0)) (τ X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1564 X0 X1 X2 x
       have i₂ := eq21 x X0 X1 X0
       grind)
    | exact superpose eq21 eq1564
    | exact resolve eq1564 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1564
  have eq1694 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X0 X0) X3)) = (M.op X1 (τ (M.op (M.op X2 (σ X0)) (σ X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21 X3 (τ (M.op (M.op X2 (σ X0)) (σ X0))) X1 X0
       have i₂ := eq1307 X0 X2
       grind)
    | exact superpose eq1307 eq21
    | exact resolve eq21 eq1307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1307
  have eq1713 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 (τ (M.op (M.op X2 (σ X0)) (σ X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1694 X0 X1 X2 x
       have i₂ := eq21 x X0 X1 X0
       grind)
    | exact superpose eq21 eq1694
    | exact resolve eq1694 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1694
  have eq1866 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = (M.op X1 (σ (M.op (M.op X2 X0) X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1584 (σ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1584
    | exact resolve eq1584 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1584
  have eq1987 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 (σ (M.op (M.op X1 X2) X3))) = (M.op X4 (σ (M.op (M.op X0 (M.op (M.op X1 X2) X3)) X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1866 (M.op (M.op X1 X2) X3) X4 X0
       have i₂ := eq21 X3 X2 (M.op X0 (M.op (M.op X1 X2) X3)) X1
       grind)
    | exact superpose eq21 eq1866
    | exact resolve eq1866 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2075 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 (σ (M.op (M.op X1 X2) X3))) = (M.op X4 (σ (M.op (M.op X0 X2) X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1987 X0 X1 X2 X3 X4
       have i₂ := eq21 X3 X2 X0 X1
       grind)
    | exact superpose eq21 eq1987
    | exact resolve eq1987 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1987
  have eq2111 : ∀ X1 X2 X3 X4 : G, (M.op X4 (σ (M.op (M.op X1 X2) X3))) = (M.op X4 (σ X2)) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq2075 x X1 X2 X3 X4
       have i₂ := eq1866 X2 X4 x
       grind)
    | exact superpose eq1866 eq2075
    | exact resolve eq2075 eq1866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1866 eq2075
  have eq3093 : ∀ X0 X1 X2 : G, (M.op X1 (τ X0)) = (M.op X1 (τ (M.op (M.op X2 X0) X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1713 (τ X0) X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1713
    | exact resolve eq1713 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3298 : ∀ X0 X1 X2 X3 : G, (M.op X3 (τ (M.op (σ (M.op X1 X1)) X2))) = (M.op X3 (τ (M.op (M.op X0 (M.op (σ (M.op X1 X1)) X2)) (σ X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3093 (M.op (σ (M.op X1 X1)) X2) X3 X0
       have i₂ := eq129 X1 (M.op X0 (M.op (σ (M.op X1 X1)) X2)) X2
       grind)
    | exact superpose eq129 eq3093
    | exact resolve eq3093 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3093
  have eq3423 : ∀ X0 X1 X2 X3 : G, (M.op X3 (τ (M.op (σ (M.op X1 X1)) X2))) = (M.op X3 (τ (M.op (M.op X0 (σ X1)) (σ X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3298 X0 X1 X2 X3
       have i₂ := eq129 X1 X0 X2
       grind)
    | exact superpose eq129 eq3298
    | exact resolve eq3298 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq3298
  have eq3481 : ∀ X1 X2 X3 : G, (M.op X3 X1) = (M.op X3 (τ (M.op (σ (M.op X1 X1)) X2))) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq3423 x X1 X2 X3
       have i₂ := eq1713 X1 X3 x
       grind)
    | exact superpose eq1713 eq3423
    | exact resolve eq3423 eq1713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3423
  have eq23699 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq590 x y
       grind)
    | exact superpose eq590 eq16
    | (have j1 := eq590 x y
       grind)
    | exact resolve eq16 eq590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590
  have eq35524 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq605 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq605
    | exact resolve eq605 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605
  have eq35677 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq35524 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq35524
    | (have j0 := eq35524 X0 X1
       grind)
    | exact resolve eq35524 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35524
  have eq68010 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq23699
       have i₂ := eq35677 y x
       grind)
    | exact superpose eq35677 eq23699
    | (have j1 := eq35677 y x
       grind)
    | (have r₁ := eq23699
       have r₂ := eq35677 y x
       grind)
    | exact resolve eq23699 eq35677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23699 eq35677
  have eq68013 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq68010
  have eq68180 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x x) X1)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    intro X0 X1
    first
    | (have i₁ := eq21 X1 y X0 x
       have i₂ := eq68013
       grind)
    | exact superpose eq68013 eq21
    | exact resolve eq21 eq68013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68013
  have eq68239 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq68180 X0 x
       have i₂ := eq21 x x X0 x
       grind)
    | exact superpose eq21 eq68180
    | exact resolve eq68180 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq68180
  have eq68255 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (τ (M.op (σ (M.op x x)) (σ y)))) ∨ (M.op X1 y) = (M.op X1 x) := by
    intro X0 X1
    first
    | (have i₁ := eq1713 y X0 (σ x)
       have i₂ := eq68239 X1
       grind)
    | exact superpose eq68239 eq1713
    | (have j1 := eq68239 X1
       grind)
    | exact resolve eq1713 eq68239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1713 eq68239
  have eq68340 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 x) ∨ (M.op X1 y) = (M.op X1 x) := by
    intro X0 X1
    first
    | (have i₁ := eq68255 X0 X1
       have i₂ := eq3481 x (σ y) X0
       grind)
    | exact superpose eq3481 eq68255
    | (have j0 := eq68255 X0 X0
       grind)
    | exact resolve eq68255 eq3481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3481 eq68255
  have eq68821 : ∀ X0 : G, (M.op X0 x) ≠ (M.op X0 x) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq68340 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68340
  have eq68822 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq68821 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68821
  have eq68920 : ∀ X0 X1 X2 : G, (M.op X1 (σ y)) = (M.op X1 (σ (M.op (M.op X0 x) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2111 X0 y X2 X1
       have i₂ := eq68822 X0
       grind)
    | exact superpose eq68822 eq2111
    | exact resolve eq2111 eq68822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69117 : ∀ X1 : G, (M.op X1 (σ x)) = (M.op X1 (σ y)) := by
    intro X1
    first
    | (have i₁ := eq68920 x X1 x
       have i₂ := eq2111 x x x X1
       grind)
    | exact superpose eq2111 eq68920
    | exact resolve eq68920 eq2111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2111 eq68920
  have eq70480 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq69117 (σ x)
       grind)
    | exact superpose eq69117 eq16
    | exact resolve eq16 eq69117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69117
  have eq70567 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq70480
       have i₂ := eq68 x
       grind)
    | exact superpose eq68 eq70480
    | exact resolve eq70480 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq70480
  have eq70730 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq70567
       have i₂ := eq68822 x
       grind)
    | exact superpose eq68822 eq70567
    | exact resolve eq70567 eq68822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68822 eq70567
  have eq70731 : False := by grind
  exact eq70731

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pyy_pxx_pyx_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq50 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x y) X0)) := by
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
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
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
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 X0 X1 X2 X3
       have i₂ := eq14 X2 X1 X0
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq58 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq82 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op y y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op y y) = (M.op x x) ∨ y = (M.op y x) := by
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
  have eq88 : (M.op y y) = (M.op x x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq87
    | exact resolve eq87 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq107 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq107 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq107 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq107 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq110 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq108 (σ X0)
       grind)
    | exact superpose eq108 eq10
    | exact resolve eq10 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq108 x
       grind)
    | exact superpose eq108 eq43
    | exact resolve eq43 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq112 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq74
       have i₂ := eq108 y
       grind)
    | exact superpose eq108 eq74
    | exact resolve eq74 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq113 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq108 sF2
       grind)
    | exact superpose eq108 eq49
    | exact resolve eq49 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq114 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq113
       have i₂ := eq108 x
       grind)
    | exact superpose eq108 eq113
    | exact resolve eq113 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq115 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq112
       have i₂ := eq108 sF3
       grind)
    | exact superpose eq108 eq112
    | exact resolve eq112 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq116 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq111
       have i₂ := eq108 sF2
       grind)
    | exact superpose eq108 eq111
    | exact resolve eq111 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq117 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq110 X0
       have i₂ := eq108 X0
       grind)
    | exact superpose eq108 eq110
    | exact resolve eq110 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq251 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x y) X0)) = (M.op X1 (M.op (M.op X0 y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq253 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x y) X0)) = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq251 X0 X1
       have i₂ := eq14 X1 y X0
       grind)
    | exact superpose eq14 eq251
    | exact resolve eq251 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251
  have eq302 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (τ X0)
       have i₂ := eq108 (τ X0)
       grind)
    | exact superpose eq108 eq34
    | exact resolve eq34 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq313 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq302 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq302
    | exact resolve eq302 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302
  have eq315 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq313 X0
       have i₂ := eq108 X0
       grind)
    | exact superpose eq108 eq313
    | exact resolve eq313 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq313
  have eq554 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = (M.op X1 (M.op (σ (M.op X0 X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X2 (σ X0) X1 (σ X0)
       have i₂ := eq117 X0
       grind)
    | exact superpose eq117 eq54
    | exact resolve eq54 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq719 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq315 X0
       grind)
    | exact superpose eq315 eq16
    | exact resolve eq16 eq315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315
  have eq876 : ∀ X0 X1 X2 : G, (M.op X1 (τ X0)) = (M.op X1 (M.op (τ (M.op X0 X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X2 (τ X0) X1 (τ X0)
       have i₂ := eq719 X0
       grind)
    | exact superpose eq719 eq54
    | exact resolve eq54 eq719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq886 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq76 X0 X1
       have i₂ := eq117 X1
       grind)
    | exact superpose eq117 eq76
    | (have j0 := eq76 X0 X1
       grind)
    | exact resolve eq76 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq887 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq886 X0 X1
       have i₂ := eq117 X0
       grind)
    | exact superpose eq117 eq886
    | (have j0 := eq886 X0 X1
       grind)
    | exact resolve eq886 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq886
  have eq948 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ (M.op y y)) = (σ (M.op X0 X0)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq887 X0 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq887
    | (have j0 := eq887 X0 y
       grind)
    | exact resolve eq887 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq887
  have eq957 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (M.op (σ y) (σ y)) = (σ (M.op X0 X0)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq948 X0
       have i₂ := eq115
       grind)
    | exact superpose eq115 eq948
    | (have j0 := eq948 X0
       grind)
    | exact resolve eq948 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq948
  have eq3925 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq957 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq957
    | (have j0 := eq957 x
       grind)
    | exact resolve eq957 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq957
  have eq3936 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq3925
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq3925
    | exact resolve eq3925 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3925
  have eq3956 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq3936
    | exact resolve eq3936 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3936
  have eq3965 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq3956
       have i₂ := eq116
       grind)
    | exact superpose eq116 eq3956
    | exact resolve eq3956 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3956
  have eq14437 : ∀ X0 X1 : G, (M.op X1 (τ X0)) = (M.op X1 (τ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq876 X0 X1 (τ (M.op X0 X0))
       have i₂ := eq719 (M.op X0 X0)
       grind)
    | exact superpose eq719 eq876
    | exact resolve eq876 eq719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719 eq876
  have eq19930 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x x) X1)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X1 y X0 y
       have i₂ := eq88
       grind)
    | exact superpose eq88 eq54
    | exact resolve eq54 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19935 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq19930 X0 x
       have i₂ := eq54 x x X0 x
       grind)
    | exact superpose eq54 eq19930
    | exact resolve eq19930 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19930
  have eq620106 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq19935 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq19935
    | (have j0 := eq19935 x
       grind)
    | exact resolve eq19935 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19935
  have eq620429 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq620106 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq620106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq620430 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq620429
    | exact resolve eq620429 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620429
  have eq620507 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq620430
       have r₂ := eq27
       grind)
    | exact resolve eq620430 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620430
  have eq620617 : ∀ X0 : G, (M.op X0 (τ (σ y))) = (M.op X0 (τ (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))))) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq620507 eq14437
    | exact resolve eq14437 eq620507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620507
  have eq620629 : ∀ X0 : G, (M.op X0 (τ (σ x))) = (M.op X0 (τ (σ y))) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq620617 x
       have i₂ := eq14437 sF2 x
       grind)
    | exact superpose eq14437 eq620617
    | exact resolve eq620617 eq14437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14437 eq620617
  have eq620711 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (τ (σ x))) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq29 eq620629
    | exact resolve eq620629 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq620629
  have eq620716 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq28 eq620711
    | exact resolve eq620711 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq620711
  have eq622511 : (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq620716 x
       grind)
    | exact superpose eq620716 eq18
    | (have j1 := eq620716 x
       grind)
    | exact resolve eq18 eq620716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620716
  have eq622609 : (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by grind
  clear eq622511
  have eq623519 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq622609 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq622609
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq622609
       grind)
    | exact resolve eq13 eq622609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622609
  have eq623529 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by grind
  clear eq623519
  have eq623610 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq623529 eq620106
    | exact resolve eq620106 eq623529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620106 eq623529
  have eq623621 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by grind
  clear eq623610
  have eq624126 : (τ (σ (M.op x y))) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq623621 eq114
    | exact resolve eq114 eq623621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623621
  have eq624303 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq30 eq624126
    | exact resolve eq624126 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq624126
  have eq624304 : (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by grind
  clear eq624303
  have eq625201 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq116
       have i₂ := eq624304
       grind)
    | exact superpose eq624304 eq116
    | exact resolve eq116 eq624304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq625295 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x y) X1)) = (M.op X0 x) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X1 x X0 x
       have i₂ := eq624304
       grind)
    | exact superpose eq624304 eq54
    | exact resolve eq54 eq624304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624304
  have eq625302 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq253 eq625295
    | exact resolve eq625295 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625295
  have eq625391 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq625201
    | exact resolve eq625201 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625201
  have eq625637 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ (M.op y x)) X1)) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq554 y X0 X1
       have i₂ := eq625302 y
       grind)
    | exact superpose eq625302 eq554
    | exact resolve eq554 eq625302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq625734 : (M.op x x) = (M.op y x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq88
       have i₂ := eq625302 y
       grind)
    | exact superpose eq625302 eq88
    | exact resolve eq88 eq625302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq625302
  have eq625830 : (M.op x x) = (M.op y x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq625734
  have eq625858 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ (M.op y x)) X1)) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq625637 X0 X1
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq625637
    | (have j0 := eq625637 X0 X1
       grind)
    | exact resolve eq625637 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625637
  have eq689500 : y ≠ (M.op x x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  have eq691686 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ (M.op x x)) X1)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq625858 X0 X1
       have i₂ := eq625830
       grind)
    | exact superpose eq625830 eq625858
    | exact resolve eq625858 eq625830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625830 eq625858
  have eq691942 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ (M.op x x)) X1)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have j0 := eq691686 X0 X1
       grind)
    | (have r₁ := eq691686 X0 X1
       have r₂ := eq689500
       grind)
    | exact resolve eq691686 eq689500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689500 eq691686
  have eq691944 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq691942 X0 x
       have i₂ := eq554 x X0 x
       grind)
    | exact superpose eq554 eq691942
    | exact resolve eq691942 eq554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691942
  have eq691945 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq691944 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq691944
    | (have j0 := eq691944 X0
       grind)
    | exact resolve eq691944 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691944
  have eq693652 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq691945
    | (have j0 := eq691945 (σ x)
       grind)
    | exact resolve eq691945 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691945
  have eq693962 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq693652 eq625391
    | exact resolve eq625391 eq693652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693652
  have eq694030 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by grind
  clear eq693962
  have eq694047 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq694030
       have r₂ := eq27
       grind)
    | exact resolve eq694030 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694030
  have eq694142 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq694047 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq694047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694047
  have eq694152 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq694142
    | exact resolve eq694142 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694142
  have eq694228 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq694152
       have r₂ := eq27
       grind)
    | exact resolve eq694152 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694152
  have eq769664 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (M.op (σ x) (σ x)) X1)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | exact superpose eq694228 eq54
    | exact resolve eq54 eq694228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694228
  have eq769680 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq769664 x X0
       have i₂ := eq54 X0 sF2 x sF2
       grind)
    | exact superpose eq54 eq769664
    | exact resolve eq769664 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769664
  have eq769775 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq769680
    | (have j0 := eq769680 (σ x)
       grind)
    | exact resolve eq769680 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769680
  have eq770114 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq769775 eq625391
    | exact resolve eq625391 eq769775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769775
  have eq770190 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq770114
  have eq770207 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq770190
       have r₂ := eq27
       grind)
    | exact resolve eq770190 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770190
  have eq770210 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq770207 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq770207
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq770207
       grind)
    | exact resolve eq13 eq770207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq770211 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) X0)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq770207 eq14
    | exact resolve eq14 eq770207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq770227 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq770210
  have eq770234 : (k x y) = (τ (M.op (σ x) (σ x))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq770227 eq58
    | exact resolve eq58 eq770227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq770227
  have eq770461 : (k x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq114 eq770234
    | exact resolve eq770234 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq770234
  have eq770466 : (k x y) = (M.op x x) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq770461
       have r₂ := eq13 x y
       grind)
    | exact resolve eq770461 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770461
  have eq770470 : (k (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq770466
       grind)
    | exact superpose eq770466 eq44
    | exact resolve eq44 eq770466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq770466
  have eq770696 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq770470
       have i₂ := eq116
       grind)
    | exact superpose eq116 eq770470
    | exact resolve eq770470 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770470
  have eq771013 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq770207 eq770211
    | exact resolve eq770211 eq770207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770207 eq770211
  have eq771253 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq771013
  have eq771262 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq771253
    | exact resolve eq771253 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771253
  have eq771348 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq771262 eq625391
    | exact resolve eq625391 eq771262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625391 eq771262
  have eq771424 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq771348
  have eq771443 : y = (M.op y x) := by
    first
    | (have r₁ := eq771424
       have r₂ := eq27
       grind)
    | exact resolve eq771424 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771424
  have eq771455 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq771443
       grind)
    | exact superpose eq771443 eq14
    | exact resolve eq14 eq771443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq771483 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq771455 x
       have i₂ := eq771443
       grind)
    | exact superpose eq771443 eq771455
    | exact resolve eq771455 eq771443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771455
  have eq771698 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq771483
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq771483
    | exact resolve eq771483 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq771483
  have eq771701 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq116
       have i₂ := eq771698
       grind)
    | exact superpose eq771698 eq116
    | exact resolve eq116 eq771698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq771794 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ (M.op x y)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq554 x X0 X1
       have i₂ := eq771698
       grind)
    | exact superpose eq771698 eq554
    | exact resolve eq554 eq771698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq771805 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x y) X1)) = (M.op X0 x) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X1 x X0 x
       have i₂ := eq771698
       grind)
    | exact superpose eq771698 eq54
    | exact resolve eq54 eq771698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq771698
  have eq771817 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | exact superpose eq253 eq771805
    | exact resolve eq771805 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253 eq771805
  have eq771825 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ (M.op x y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq20 eq771794
    | (have j0 := eq771794 X0 X1
       grind)
    | exact resolve eq771794 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771794
  have eq771907 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq20 eq771701
    | exact resolve eq771701 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq771701
  have eq771913 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ (M.op x y)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq771825 X0 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq771825
    | (have j0 := eq771825 X0 X1
       grind)
    | exact resolve eq771825 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq771825
  have eq772202 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ (M.op y x)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq554 y X0 X1
       have i₂ := eq771817 y
       grind)
    | exact superpose eq771817 eq554
    | exact resolve eq554 eq771817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554
  have eq772339 : (M.op (σ y) (σ y)) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq115
       have i₂ := eq771817 y
       grind)
    | exact superpose eq771817 eq115
    | exact resolve eq115 eq771817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq771817
  have eq772515 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq772339
       have i₂ := eq771443
       grind)
    | exact superpose eq771443 eq772339
    | exact resolve eq772339 eq771443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772339
  have eq772574 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ y) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq772202 X0 X1
       have i₂ := eq771443
       grind)
    | exact superpose eq771443 eq772202
    | exact resolve eq772202 eq771443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771443 eq772202
  have eq772661 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq772515
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq772515
    | exact resolve eq772515 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772515
  have eq772710 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ y) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq772574 X0 X1
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq772574
    | (have j0 := eq772574 X0 X1
       grind)
    | exact resolve eq772574 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq772574
  have eq775147 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq772661 eq3965
    | exact resolve eq3965 eq772661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3965 eq772661
  have eq775300 : (σ (M.op x y)) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq771907 eq775147
    | exact resolve eq775147 eq771907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775147
  have eq775381 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq770696 eq775300
    | exact resolve eq775300 eq770696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770696 eq775300
  have eq775425 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq771907 eq775381
    | exact resolve eq775381 eq771907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775381
  have eq775447 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq775425
       have r₂ := eq27
       grind)
    | exact resolve eq775425 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775425
  have eq776380 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) X0)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq775447 eq14
    | exact resolve eq14 eq775447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775447
  have eq805086 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq772710 eq776380
    | exact resolve eq776380 eq772710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776380
  have eq805253 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq805086 eq26
    | (have j1 := eq805086 (σ x)
       grind)
    | exact resolve eq26 eq805086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq805086
  have eq805421 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq771907 eq805253
    | exact resolve eq805253 eq771907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq805253
  have eq805536 : (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq805421
       have r₂ := eq27
       grind)
    | exact resolve eq805421 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq805421
  have eq805662 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq805536 eq26
    | exact resolve eq26 eq805536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq806228 : ∀ X0 X1 : G, (M.op X0 (σ (M.op x y))) = (M.op X0 (M.op (σ (M.op x y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq805536 eq772710
    | exact resolve eq772710 eq805536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772710 eq805536
  have eq806235 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = (M.op X0 (σ x)) := by
    intro X0
    first
    | exact superpose eq771913 eq806228
    | exact resolve eq806228 eq771913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771913 eq806228
  have eq819643 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq806235 eq771907
    | exact resolve eq771907 eq806235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771907 eq806235
  have eq819663 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq805662 eq819643
    | exact resolve eq819643 eq805662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq805662 eq819643
  have eq819808 : False := by grind
  exact eq819808

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pyy_pxx_pyy_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq50 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x y) X0)) := by
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
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
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
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 X0 X1 X2 X3
       have i₂ := eq14 X2 X1 X0
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq58 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq82 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op y y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op y y) = (M.op x x) ∨ y = (M.op y x) := by
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
  have eq88 : (M.op y y) = (M.op x x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq87
    | exact resolve eq87 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq107 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq107 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq107 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq107 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq110 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq108 (σ X0)
       grind)
    | exact superpose eq108 eq10
    | exact resolve eq10 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq108 x
       grind)
    | exact superpose eq108 eq43
    | exact resolve eq43 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq112 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq74
       have i₂ := eq108 y
       grind)
    | exact superpose eq108 eq74
    | exact resolve eq74 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq113 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq108 sF2
       grind)
    | exact superpose eq108 eq49
    | exact resolve eq49 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq114 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq113
       have i₂ := eq108 x
       grind)
    | exact superpose eq108 eq113
    | exact resolve eq113 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq115 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq112
       have i₂ := eq108 sF3
       grind)
    | exact superpose eq108 eq112
    | exact resolve eq112 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq116 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq111
       have i₂ := eq108 sF2
       grind)
    | exact superpose eq108 eq111
    | exact resolve eq111 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq117 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq110 X0
       have i₂ := eq108 X0
       grind)
    | exact superpose eq108 eq110
    | exact resolve eq110 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq251 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x y) X0)) = (M.op X1 (M.op (M.op X0 y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq253 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x y) X0)) = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq251 X0 X1
       have i₂ := eq14 X1 y X0
       grind)
    | exact superpose eq14 eq251
    | exact resolve eq251 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251
  have eq302 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (τ X0)
       have i₂ := eq108 (τ X0)
       grind)
    | exact superpose eq108 eq34
    | exact resolve eq34 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq313 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq302 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq302
    | exact resolve eq302 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302
  have eq315 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq313 X0
       have i₂ := eq108 X0
       grind)
    | exact superpose eq108 eq313
    | exact resolve eq313 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq313
  have eq552 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = (M.op X1 (M.op (σ (M.op X0 X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X2 (σ X0) X1 (σ X0)
       have i₂ := eq117 X0
       grind)
    | exact superpose eq117 eq54
    | exact resolve eq54 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq716 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq315 X0
       grind)
    | exact superpose eq315 eq16
    | exact resolve eq16 eq315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315
  have eq873 : ∀ X0 X1 X2 : G, (M.op X1 (τ X0)) = (M.op X1 (M.op (τ (M.op X0 X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X2 (τ X0) X1 (τ X0)
       have i₂ := eq716 X0
       grind)
    | exact superpose eq716 eq54
    | exact resolve eq54 eq716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq883 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq76 X0 X1
       have i₂ := eq117 X1
       grind)
    | exact superpose eq117 eq76
    | (have j0 := eq76 X0 X1
       grind)
    | exact resolve eq76 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq884 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq883 X0 X1
       have i₂ := eq117 X0
       grind)
    | exact superpose eq117 eq883
    | (have j0 := eq883 X0 X1
       grind)
    | exact resolve eq883 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq883
  have eq945 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ (M.op y y)) = (σ (M.op X0 X0)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq884 X0 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq884
    | (have j0 := eq884 X0 y
       grind)
    | exact resolve eq884 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq884
  have eq954 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (M.op (σ y) (σ y)) = (σ (M.op X0 X0)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq945 X0
       have i₂ := eq115
       grind)
    | exact superpose eq115 eq945
    | (have j0 := eq945 X0
       grind)
    | exact resolve eq945 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq945
  have eq3922 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq954 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq954
    | (have j0 := eq954 x
       grind)
    | exact resolve eq954 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq954
  have eq3933 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq3922
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq3922
    | exact resolve eq3922 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3922
  have eq3953 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq3933
    | exact resolve eq3933 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3933
  have eq3962 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq3953
       have i₂ := eq116
       grind)
    | exact superpose eq116 eq3953
    | exact resolve eq3953 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3953
  have eq14422 : ∀ X0 X1 : G, (M.op X1 (τ X0)) = (M.op X1 (τ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq873 X0 X1 (τ (M.op X0 X0))
       have i₂ := eq716 (M.op X0 X0)
       grind)
    | exact superpose eq716 eq873
    | exact resolve eq873 eq716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716 eq873
  have eq19885 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x x) X1)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X1 y X0 y
       have i₂ := eq88
       grind)
    | exact superpose eq88 eq54
    | exact resolve eq54 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19890 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq19885 X0 x
       have i₂ := eq54 x x X0 x
       grind)
    | exact superpose eq54 eq19885
    | exact resolve eq19885 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19885
  have eq619900 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq19890 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq19890
    | (have j0 := eq19890 x
       grind)
    | exact resolve eq19890 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19890
  have eq620222 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq619900 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq619900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq620223 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq620222
    | exact resolve eq620222 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620222
  have eq620300 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq620223
       have r₂ := eq27
       grind)
    | exact resolve eq620223 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620223
  have eq620410 : ∀ X0 : G, (M.op X0 (τ (σ y))) = (M.op X0 (τ (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))))) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq620300 eq14422
    | exact resolve eq14422 eq620300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620300
  have eq620422 : ∀ X0 : G, (M.op X0 (τ (σ x))) = (M.op X0 (τ (σ y))) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq620410 x
       have i₂ := eq14422 sF2 x
       grind)
    | exact superpose eq14422 eq620410
    | exact resolve eq620410 eq14422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14422 eq620410
  have eq620504 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (τ (σ x))) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq29 eq620422
    | exact resolve eq620422 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq620422
  have eq620509 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq28 eq620504
    | exact resolve eq620504 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq620504
  have eq622304 : (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq620509 x
       grind)
    | exact superpose eq620509 eq18
    | (have j1 := eq620509 x
       grind)
    | exact resolve eq18 eq620509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620509
  have eq622402 : (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by grind
  clear eq622304
  have eq623311 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq622402 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq622402
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq622402
       grind)
    | exact resolve eq13 eq622402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622402
  have eq623321 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by grind
  clear eq623311
  have eq623402 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq623321 eq619900
    | exact resolve eq619900 eq623321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619900 eq623321
  have eq623413 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by grind
  clear eq623402
  have eq623918 : (τ (σ (M.op x y))) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq623413 eq114
    | exact resolve eq114 eq623413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623413
  have eq624095 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq30 eq623918
    | exact resolve eq623918 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq623918
  have eq624096 : (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by grind
  clear eq624095
  have eq624993 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq116
       have i₂ := eq624096
       grind)
    | exact superpose eq624096 eq116
    | exact resolve eq116 eq624096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq625087 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x y) X1)) = (M.op X0 x) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X1 x X0 x
       have i₂ := eq624096
       grind)
    | exact superpose eq624096 eq54
    | exact resolve eq54 eq624096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624096
  have eq625094 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq253 eq625087
    | exact resolve eq625087 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625087
  have eq625183 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq624993
    | exact resolve eq624993 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624993
  have eq625429 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ (M.op y x)) X1)) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq552 y X0 X1
       have i₂ := eq625094 y
       grind)
    | exact superpose eq625094 eq552
    | exact resolve eq552 eq625094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq625526 : (M.op x x) = (M.op y x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq88
       have i₂ := eq625094 y
       grind)
    | exact superpose eq625094 eq88
    | exact resolve eq88 eq625094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq625094
  have eq625622 : (M.op x x) = (M.op y x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq625526
  have eq625650 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ (M.op y x)) X1)) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq625429 X0 X1
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq625429
    | (have j0 := eq625429 X0 X1
       grind)
    | exact resolve eq625429 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625429
  have eq689195 : y ≠ (M.op x x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  have eq691381 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ (M.op x x)) X1)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq625650 X0 X1
       have i₂ := eq625622
       grind)
    | exact superpose eq625622 eq625650
    | exact resolve eq625650 eq625622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625622 eq625650
  have eq691637 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ (M.op x x)) X1)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have j0 := eq691381 X0 X1
       grind)
    | (have r₁ := eq691381 X0 X1
       have r₂ := eq689195
       grind)
    | exact resolve eq691381 eq689195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689195 eq691381
  have eq691639 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq691637 X0 x
       have i₂ := eq552 x X0 x
       grind)
    | exact superpose eq552 eq691637
    | exact resolve eq691637 eq552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691637
  have eq691640 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq691639 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq691639
    | (have j0 := eq691639 X0
       grind)
    | exact resolve eq691639 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691639
  have eq693340 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq691640
    | (have j0 := eq691640 (σ x)
       grind)
    | exact resolve eq691640 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691640
  have eq693650 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq693340 eq625183
    | exact resolve eq625183 eq693340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693340
  have eq693718 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by grind
  clear eq693650
  have eq693735 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq693718
       have r₂ := eq27
       grind)
    | exact resolve eq693718 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693718
  have eq693830 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq693735 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq693735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693735
  have eq693840 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq693830
    | exact resolve eq693830 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693830
  have eq693916 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq693840
       have r₂ := eq27
       grind)
    | exact resolve eq693840 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693840
  have eq769423 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (M.op (σ x) (σ x)) X1)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | exact superpose eq693916 eq54
    | exact resolve eq54 eq693916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693916
  have eq769439 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq769423 x X0
       have i₂ := eq54 X0 sF2 x sF2
       grind)
    | exact superpose eq54 eq769423
    | exact resolve eq769423 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769423
  have eq769534 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq769439
    | (have j0 := eq769439 (σ x)
       grind)
    | exact resolve eq769439 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769439
  have eq769873 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq769534 eq625183
    | exact resolve eq625183 eq769534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769534
  have eq769949 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq769873
  have eq769966 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq769949
       have r₂ := eq27
       grind)
    | exact resolve eq769949 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769949
  have eq769969 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq769966 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq769966
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq769966
       grind)
    | exact resolve eq13 eq769966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq769970 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) X0)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq769966 eq14
    | exact resolve eq14 eq769966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq769986 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq769969
  have eq769993 : (k x y) = (τ (M.op (σ x) (σ x))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq769986 eq58
    | exact resolve eq58 eq769986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq769986
  have eq770220 : (k x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq114 eq769993
    | exact resolve eq769993 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq769993
  have eq770225 : (k x y) = (M.op x x) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq770220
       have r₂ := eq13 x y
       grind)
    | exact resolve eq770220 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770220
  have eq770229 : (k (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq770225
       grind)
    | exact superpose eq770225 eq44
    | exact resolve eq44 eq770225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq770225
  have eq770455 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq770229
       have i₂ := eq116
       grind)
    | exact superpose eq116 eq770229
    | exact resolve eq770229 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770229
  have eq770772 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq769966 eq769970
    | exact resolve eq769970 eq769966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769966 eq769970
  have eq771012 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq770772
  have eq771021 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq771012
    | exact resolve eq771012 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771012
  have eq771107 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq771021 eq625183
    | exact resolve eq625183 eq771021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625183 eq771021
  have eq771183 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq771107
  have eq771202 : y = (M.op y x) := by
    first
    | (have r₁ := eq771183
       have r₂ := eq27
       grind)
    | exact resolve eq771183 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771183
  have eq771214 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq771202
       grind)
    | exact superpose eq771202 eq14
    | exact resolve eq14 eq771202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq771242 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq771214 x
       have i₂ := eq771202
       grind)
    | exact superpose eq771202 eq771214
    | exact resolve eq771214 eq771202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771214
  have eq771457 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq771242
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq771242
    | exact resolve eq771242 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq771242
  have eq771460 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq116
       have i₂ := eq771457
       grind)
    | exact superpose eq771457 eq116
    | exact resolve eq116 eq771457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq771553 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ (M.op x y)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq552 x X0 X1
       have i₂ := eq771457
       grind)
    | exact superpose eq771457 eq552
    | exact resolve eq552 eq771457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq771564 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x y) X1)) = (M.op X0 x) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X1 x X0 x
       have i₂ := eq771457
       grind)
    | exact superpose eq771457 eq54
    | exact resolve eq54 eq771457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq771457
  have eq771576 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | exact superpose eq253 eq771564
    | exact resolve eq771564 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253 eq771564
  have eq771584 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ (M.op x y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq20 eq771553
    | (have j0 := eq771553 X0 X1
       grind)
    | exact resolve eq771553 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771553
  have eq771666 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq20 eq771460
    | exact resolve eq771460 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq771460
  have eq771672 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ (M.op x y)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq771584 X0 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq771584
    | (have j0 := eq771584 X0 X1
       grind)
    | exact resolve eq771584 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq771584
  have eq771961 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ (M.op y x)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq552 y X0 X1
       have i₂ := eq771576 y
       grind)
    | exact superpose eq771576 eq552
    | exact resolve eq552 eq771576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552
  have eq772098 : (M.op (σ y) (σ y)) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq115
       have i₂ := eq771576 y
       grind)
    | exact superpose eq771576 eq115
    | exact resolve eq115 eq771576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq771576
  have eq772274 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq772098
       have i₂ := eq771202
       grind)
    | exact superpose eq771202 eq772098
    | exact resolve eq772098 eq771202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772098
  have eq772333 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ y) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq771961 X0 X1
       have i₂ := eq771202
       grind)
    | exact superpose eq771202 eq771961
    | exact resolve eq771961 eq771202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771202 eq771961
  have eq772420 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq772274
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq772274
    | exact resolve eq772274 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772274
  have eq772471 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ y) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq772333 X0 X1
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq772333
    | (have j0 := eq772333 X0 X1
       grind)
    | exact resolve eq772333 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq772333
  have eq774906 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq772420 eq3962
    | exact resolve eq3962 eq772420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3962 eq772420
  have eq775059 : (σ (M.op x y)) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq771666 eq774906
    | exact resolve eq774906 eq771666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq774906
  have eq775141 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq770455 eq775059
    | exact resolve eq775059 eq770455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770455 eq775059
  have eq775184 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq771666 eq775141
    | exact resolve eq775141 eq771666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775141
  have eq775206 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq775184
       have r₂ := eq27
       grind)
    | exact resolve eq775184 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775184
  have eq776139 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) X0)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq775206 eq14
    | exact resolve eq14 eq775206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775206
  have eq801301 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq772471 eq776139
    | exact resolve eq776139 eq772471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776139
  have eq801466 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq801301 eq26
    | (have j1 := eq801301 (σ x)
       grind)
    | exact resolve eq26 eq801301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq801301
  have eq801634 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq771666 eq801466
    | exact resolve eq801466 eq771666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq801466
  have eq801749 : (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq801634
       have r₂ := eq27
       grind)
    | exact resolve eq801634 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq801634
  have eq801875 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq801749 eq26
    | exact resolve eq26 eq801749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq802441 : ∀ X0 X1 : G, (M.op X0 (σ (M.op x y))) = (M.op X0 (M.op (σ (M.op x y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq801749 eq772471
    | exact resolve eq772471 eq801749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772471 eq801749
  have eq802448 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = (M.op X0 (σ x)) := by
    intro X0
    first
    | exact superpose eq771672 eq802441
    | exact resolve eq802441 eq771672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771672 eq802441
  have eq815858 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq802448 eq771666
    | exact resolve eq771666 eq802448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771666 eq802448
  have eq815878 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq801875 eq815858
    | exact resolve eq815858 eq801875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq801875 eq815858
  have eq816022 : False := by grind
  exact eq816022

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,X) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pyy_pxy_pxx_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq34 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X2 X1) = X2 ∨ (M.op X1 X1) = (k X1 X2) ∨ (M.op X0 X2) = (k X0 X2) ∨ (M.op X2 X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X2
       have i₂ := eq14 X0 X2
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X2
       have j1 := eq14 X0 X2
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 (M.op X1 X1) X1
       have r₂ := eq14 (M.op X1 X1) (M.op X1 X1)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X2 X1) = X2 ∨ (M.op X1 X1) = (k X1 X2) ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq34 X0 X1 X2
       have j1 := eq12 X0 X2
       grind)
    | (have r₁ := eq34 X0 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq34 X0 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq34 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq59 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
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
  have eq61 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq77 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op X1 (M.op (M.op X0 X0) X3)) ∨ (M.op X2 X0) = (k X2 X0) ∨ (M.op X0 X2) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21 X3 X2 X1 X2
       have i₂ := eq14 X2 X0
       grind)
    | (have i₁ := eq21 X0 X1 X2 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq21
    | (have j1 := eq14 X2 X0
       grind)
    | exact resolve eq21 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op X1 (M.op (M.op X0 X0) X3)) ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq77 X0 X1 X2 X3
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq77 X1 X1 X0 X3
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq77 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq101 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 X2) ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq97 X0 X1 X2 x
       have i₂ := eq21 x X0 X1 X0
       grind)
    | exact superpose eq21 eq97
    | (have j0 := eq97 X0 X1 X2 x
       grind)
    | exact resolve eq97 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq371 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq37 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq372 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq371 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq371 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq371 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371
  have eq946 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq372 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372
  have eq948 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq946 X0 X1
       have j1 := eq101 X1 X1 X0
       grind)
    | (have r₁ := eq946 x X0
       have r₂ := eq101 X0 x x
       grind)
    | (have r₁ := eq946 X0 x
       have r₂ := eq101 X0 X0 x
       grind)
    | exact resolve eq946 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq946
  have eq983 : ∀ X0 X1 X2 X3 : G, (k (σ X2) (k (k X0 (σ X1)) (σ X3))) = (σ (k X2 (k (k (τ X0) X1) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq59 (k X0 (σ X1)) X3 X2
       have i₂ := eq61 X0 X1
       grind)
    | exact superpose eq61 eq59
    | exact resolve eq59 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq61
  have eq1010 : ∀ X0 X1 X2 X3 : G, (k (σ X2) (k (k X0 (σ X1)) (σ X3))) = (σ (M.op X2 (k (k (τ X0) X1) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq983 X0 X1 X2 X3
       have i₂ := eq948 X2 (k (k (τ X0) X1) X3)
       grind)
    | exact superpose eq948 eq983
    | exact resolve eq983 eq948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq983
  have eq1023 : ∀ X0 X1 X2 X3 : G, (k (σ X2) (k (k X0 (σ X1)) (σ X3))) = (σ (M.op X2 (M.op (k (τ X0) X1) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1010 X0 X1 X2 X3
       have i₂ := eq948 (k (τ X0) X1) X3
       grind)
    | exact superpose eq948 eq1010
    | exact resolve eq1010 eq948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1010
  have eq1036 : ∀ X0 X1 X2 X3 : G, (k (σ X2) (k (k X0 (σ X1)) (σ X3))) = (σ (M.op X2 (M.op (M.op (τ X0) X1) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1023 X0 X1 X2 X3
       have i₂ := eq948 (τ X0) X1
       grind)
    | exact superpose eq948 eq1023
    | exact resolve eq1023 eq948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1023
  have eq1048 : ∀ X0 X1 X2 X3 : G, (k (σ X2) (k (k X0 (σ X1)) (σ X3))) = (σ (M.op X2 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1036 X0 X1 X2 X3
       have i₂ := eq21 X3 X1 X2 (τ X0)
       grind)
    | exact superpose eq21 eq1036
    | exact resolve eq1036 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1036
  have eq1059 : ∀ X0 X1 X2 X3 : G, (σ (M.op X2 X1)) = (M.op (σ X2) (k (k X0 (σ X1)) (σ X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1048 X0 X1 X2 X3
       have i₂ := eq948 (σ X2) (k (k X0 (σ X1)) (σ X3))
       grind)
    | exact superpose eq948 eq1048
    | exact resolve eq1048 eq948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1048
  have eq1068 : ∀ X0 X1 X2 X3 : G, (σ (M.op X2 X1)) = (M.op (σ X2) (M.op (k X0 (σ X1)) (σ X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1059 X0 X1 X2 X3
       have i₂ := eq948 (k X0 (σ X1)) (σ X3)
       grind)
    | exact superpose eq948 eq1059
    | exact resolve eq1059 eq948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1059
  have eq1072 : ∀ X0 X1 X2 X3 : G, (σ (M.op X2 X1)) = (M.op (σ X2) (M.op (M.op X0 (σ X1)) (σ X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1068 X0 X1 X2 X3
       have i₂ := eq948 X0 (σ X1)
       grind)
    | exact superpose eq948 eq1068
    | exact resolve eq1068 eq948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq948 eq1068
  have eq1076 : ∀ X1 X2 : G, (M.op (σ X2) (σ X1)) = (σ (M.op X2 X1)) := by
    intro X1 X2
    first
    | (have i₁ := eq1072 x X1 X2 x
       have i₂ := eq21 (σ x) (σ X1) (σ X2) x
       grind)
    | exact superpose eq21 eq1072
    | exact resolve eq1072 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1072
  have eq1077 : False := by grind
  exact eq1077

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pyy_pxy_pyx_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq55 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq55 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq55 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq58 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq56 (σ X0)
       grind)
    | exact superpose eq56 eq15
    | exact resolve eq15 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq56 (τ X0)
       grind)
    | exact superpose eq56 eq18
    | exact resolve eq18 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq61 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq61
    | exact resolve eq61 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq67 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq58 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq58
    | exact resolve eq58 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq70 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq64 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq64
    | exact resolve eq64 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq64
  have eq79 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (M.op (σ (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq9
    | exact resolve eq9 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq91 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq84 X0 X1
       have i₂ := eq67 X1
       grind)
    | exact superpose eq67 eq84
    | (have j0 := eq84 X0 X1
       grind)
    | exact resolve eq84 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq93 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq91 X0 X1
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq91
    | (have j0 := eq91 X0 X1
       grind)
    | exact resolve eq91 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq103 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq10
    | exact resolve eq10 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = (M.op X1 (M.op (σ (M.op X0 X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 X2 (σ X0) X1 (σ X0)
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq21
    | exact resolve eq21 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq131 X0 X1 (σ (M.op X0 X0))
       have i₂ := eq67 (M.op X0 X0)
       grind)
    | exact superpose eq67 eq131
    | exact resolve eq131 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq346 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq93 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq93
    | (have j0 := eq93 (τ X0) X1
       grind)
    | exact resolve eq93 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq364 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq346 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq346
    | (have j0 := eq346 X0 X1
       grind)
    | exact resolve eq346 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq346
  have eq370 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq364 X0 X1
       have j1 := eq12 (σ X1) X0
       grind)
    | (have r₁ := eq364 X1 X1
       have r₂ := eq12 (σ X1) X1
       grind)
    | exact resolve eq364 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364
  have eq374 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq370 X0 X1
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq370
    | (have j0 := eq370 X0 X1
       grind)
    | exact resolve eq370 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370
  have eq577 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq374 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq374
    | (have j0 := eq374 X1 (τ X0)
       grind)
    | exact resolve eq374 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq584 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq374 (σ X1) X0
       grind)
    | exact superpose eq374 eq15
    | (have j1 := eq374 (σ X1) X0
       grind)
    | exact resolve eq15 eq374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374
  have eq605 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq584 X0 X1
       have i₂ := eq67 X1
       grind)
    | exact superpose eq67 eq584
    | (have j0 := eq584 X0 X1
       grind)
    | exact resolve eq584 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584
  have eq610 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq577 X0 X1
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq577
    | (have j0 := eq577 X0 X1
       grind)
    | exact resolve eq577 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq577
  have eq636 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq610 (τ X0) X1
       grind)
    | exact superpose eq610 eq17
    | (have j1 := eq610 X1 (τ X0)
       grind)
    | exact resolve eq17 eq610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq610
  have eq643 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq636 X0 X1
       have i₂ := eq103 X0
       grind)
    | exact superpose eq103 eq636
    | (have j0 := eq636 X0 X1
       grind)
    | exact resolve eq636 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq636
  have eq2292 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq643 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq643
    | (have j0 := eq643 (σ X0) X1
       grind)
    | exact resolve eq643 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643
  have eq2376 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2292 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2292
    | (have j0 := eq2292 X0 X1
       grind)
    | exact resolve eq2292 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2292
  have eq2383 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ (M.op X0 X0))) ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2376 X0 X1
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq2376
    | (have j0 := eq2376 X0 X1
       grind)
    | exact resolve eq2376 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2376
  have eq2386 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2383 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq2383
    | (have j0 := eq2383 X0 X1
       grind)
    | exact resolve eq2383 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2383
  have eq2879 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq605 x y
       grind)
    | exact superpose eq605 eq16
    | (have j1 := eq605 x y
       grind)
    | exact resolve eq16 eq605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605
  have eq3039 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq2879
       have i₂ := eq2386 x y
       grind)
    | exact superpose eq2386 eq2879
    | (have j1 := eq2386 x y
       grind)
    | (have r₁ := eq2879
       have r₂ := eq2386 x y
       grind)
    | exact resolve eq2879 eq2386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2386 eq2879
  have eq3040 : (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq3039
  have eq3051 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op (M.op x x) (M.op x x)))) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq186 y x
       have i₂ := eq3040
       grind)
    | exact superpose eq3040 eq186
    | exact resolve eq186 eq3040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3063 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x x) X1)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    intro X0 X1
    first
    | (have i₁ := eq21 X1 y X0 y
       have i₂ := eq3040
       grind)
    | exact superpose eq3040 eq21
    | exact resolve eq21 eq3040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3040
  have eq3068 : ∀ X0 : G, (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq3063 X0 x
       have i₂ := eq21 x x X0 x
       grind)
    | exact superpose eq21 eq3063
    | exact resolve eq3063 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3063
  have eq3079 : ∀ X0 : G, (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq3051 X0
       have i₂ := eq186 x X0
       grind)
    | exact superpose eq186 eq3051
    | exact resolve eq3051 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186 eq3051
  have eq3189 : ∀ X0 : G, (M.op y y) = (τ (σ (M.op x x))) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq3068 X0
       grind)
    | exact superpose eq3068 eq10
    | (have j1 := eq3068 X0
       grind)
    | exact resolve eq10 eq3068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3068
  have eq3236 : ∀ X0 : G, (M.op x x) = (M.op y y) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq3189 X0
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq3189
    | (have j0 := eq3189 X0
       grind)
    | exact resolve eq3189 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3189
  have eq3263 : ∀ X0 X1 X2 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x x) X1)) ∨ (M.op X2 y) = (M.op X2 x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 X1 y X0 y
       have i₂ := eq3236 X2
       grind)
    | exact superpose eq3236 eq21
    | (have j1 := eq3236 X2
       grind)
    | exact resolve eq21 eq3236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3236
  have eq3269 : ∀ X0 X2 : G, (M.op X0 y) = (M.op X0 x) ∨ (M.op X2 y) = (M.op X2 x) := by
    intro X0 X2
    first
    | (have i₁ := eq3263 X0 x X2
       have i₂ := eq21 x x X0 x
       grind)
    | exact superpose eq21 eq3263
    | (have j0 := eq3263 X0 x X0
       grind)
    | exact resolve eq3263 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq3263
  have eq3437 : ∀ X0 : G, (M.op X0 x) ≠ (M.op X0 x) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq3269 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3269
  have eq3438 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq3437 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3437
  have eq6359 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ (M.op x x)) X0)) ∨ (M.op X1 (σ y)) = (M.op X1 (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq79 y X0
       have i₂ := eq3079 X1
       grind)
    | exact superpose eq3079 eq79
    | (have j1 := eq3079 X1
       grind)
    | exact resolve eq79 eq3079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3079
  have eq6428 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (M.op X1 (σ y)) = (M.op X1 (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq6359 X0 X1
       have i₂ := eq79 x X0
       grind)
    | exact superpose eq79 eq6359
    | (have j0 := eq6359 X0 X0
       grind)
    | exact resolve eq6359 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq6359
  have eq7013 : ∀ X0 : G, (M.op X0 (σ x)) ≠ (M.op X0 (σ x)) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq6428 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6428
  have eq7014 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq7013 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7013
  have eq7051 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7014 (σ x)
       grind)
    | exact superpose eq7014 eq16
    | exact resolve eq16 eq7014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7014
  have eq7086 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq7051
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq7051
    | exact resolve eq7051 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq7051
  have eq7108 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq7086
       have i₂ := eq3438 x
       grind)
    | exact superpose eq3438 eq7086
    | exact resolve eq7086 eq3438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3438 eq7086
  have eq7109 : False := by grind
  exact eq7109

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyx_pxx_pyy_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq50 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x y) X0)) := by
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
  have eq51 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
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
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 X0 X1 X2 X3
       have i₂ := eq14 X2 X1 X0
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq74 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq76 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq82 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
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
  have eq87 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
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
  have eq89 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq87
    | exact resolve eq87 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq90 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq89
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq89
    | exact resolve eq89 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq103 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq16
    | exact resolve eq16 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq110 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq110 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq110 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq113 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq111 (σ X0)
       grind)
    | exact superpose eq111 eq10
    | exact resolve eq10 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq111 x
       grind)
    | exact superpose eq111 eq43
    | exact resolve eq43 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq115 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq74
       have i₂ := eq111 y
       grind)
    | exact superpose eq111 eq74
    | exact resolve eq74 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq116 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq111 sF2
       grind)
    | exact superpose eq111 eq49
    | exact resolve eq49 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq117 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq116
       have i₂ := eq111 x
       grind)
    | exact superpose eq111 eq116
    | exact resolve eq116 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq118 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq115
       have i₂ := eq111 sF3
       grind)
    | exact superpose eq111 eq115
    | exact resolve eq115 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq119 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq114
       have i₂ := eq111 sF2
       grind)
    | exact superpose eq111 eq114
    | exact resolve eq114 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq120 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq113 X0
       have i₂ := eq111 X0
       grind)
    | exact superpose eq111 eq113
    | exact resolve eq113 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq126 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq103
       have i₂ := eq111 sF3
       grind)
    | exact superpose eq111 eq103
    | exact resolve eq103 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq127 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq126
       have i₂ := eq111 y
       grind)
    | exact superpose eq111 eq126
    | exact resolve eq126 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq126
  have eq255 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x y) X0)) = (M.op X1 (M.op (M.op X0 y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq257 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x y) X0)) = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq255 X0 X1
       have i₂ := eq14 X1 y X0
       grind)
    | exact superpose eq14 eq255
    | exact resolve eq255 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq262 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ x) (σ y)) X0)) = (M.op X1 (M.op (M.op X0 (σ y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq265 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ x) (σ y)) X0)) = (M.op X1 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq262 x X0
       have i₂ := eq14 X0 sF3 x
       grind)
    | exact superpose eq14 eq262
    | exact resolve eq262 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262
  have eq560 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = (M.op X1 (M.op (σ (M.op X0 X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X2 (σ X0) X1 (σ X0)
       have i₂ := eq120 X0
       grind)
    | exact superpose eq120 eq54
    | exact resolve eq54 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq946 : ∀ X0 X1 X2 : G, (M.op X2 (σ X0)) = (M.op X2 (M.op (M.op (σ X0) (σ X1)) X2)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (σ X0) (σ X1)
       have i₂ := eq76 X0 X1
       grind)
    | (have i₁ := eq14 X0 (σ X1) (σ X0)
       have i₂ := eq76 X0 X1
       grind)
    | exact superpose eq76 eq14
    | (have j1 := eq76 X0 X1
       grind)
    | exact resolve eq14 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq954 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 (σ X0)) = (M.op X2 (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq946 X0 X1 X2
       have i₂ := eq14 X2 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq946
    | (have j0 := eq946 X0 X1 X2
       grind)
    | exact resolve eq946 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq946
  have eq6582 : ∀ X0 X1 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (M.op X1 (σ y)) = (M.op X1 (σ X0)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq954 X0 y X1
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq954
    | (have j0 := eq954 X0 y X1
       grind)
    | exact resolve eq954 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq954
  have eq16609 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq90 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16610 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq16609
    | exact resolve eq16609 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16609
  have eq16621 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq16610
       have r₂ := eq27
       grind)
    | exact resolve eq16610 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16610
  have eq16625 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq16621
    | exact resolve eq16621 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16621
  have eq16628 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq16625 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq16625
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq16625
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq16625
       grind)
    | exact resolve eq12 eq16625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16631 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | exact superpose eq16625 eq54
    | exact resolve eq54 eq16625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16636 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by grind
  have eq16639 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq265 eq16631
    | exact resolve eq16631 eq265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265 eq16631
  have eq16642 : (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq16628
       have r₂ := eq26
       grind)
    | exact resolve eq16628 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16628
  have eq16646 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq16639
    | (have j0 := eq16639 (σ x)
       grind)
    | exact resolve eq16639 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16674 : (M.op y y) = (τ (M.op (σ y) (σ x))) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq16639 eq127
    | exact resolve eq127 eq16639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq16639
  have eq16996 : (M.op y y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq16625 eq16674
    | exact resolve eq16674 eq16625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16625 eq16674
  have eq17047 : (M.op y y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq16996
  have eq17056 : (M.op y y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq17047
       have r₂ := eq16636
       grind)
    | exact resolve eq17047 eq16636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17047
  have eq17057 : (M.op (σ y) (σ y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq118
       have i₂ := eq17056
       grind)
    | exact superpose eq17056 eq118
    | exact resolve eq118 eq17056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17056
  have eq17094 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq17057
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq17057
    | exact resolve eq17057 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17057
  have eq17442 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq16642
       have r₂ := eq16636
       grind)
    | exact resolve eq16642 eq16636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16636 eq16642
  have eq17448 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq17442 eq90
    | exact resolve eq90 eq17442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17442
  have eq17457 : (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq17448
  have eq17473 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq17457 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq17457
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq17457
       grind)
    | exact resolve eq13 eq17457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17457
  have eq17482 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq17473
  have eq18025 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq17482 eq90
    | exact resolve eq90 eq17482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17482
  have eq18035 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq18025
  have eq18124 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq18035 eq17094
    | exact resolve eq17094 eq18035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17094 eq18035
  have eq18148 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq18124
  have eq18159 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq18148
       have r₂ := eq27
       grind)
    | exact resolve eq18148 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18148
  have eq18240 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq18159 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq18159
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq18159
       grind)
    | exact resolve eq13 eq18159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18159
  have eq18249 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq18240
  have eq20209 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq18249 eq90
    | exact resolve eq90 eq18249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq18249
  have eq20219 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by grind
  clear eq20209
  have eq20488 : (τ (σ (M.op x y))) = (M.op x x) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20219 eq117
    | exact resolve eq117 eq20219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq20497 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20219 eq16646
    | exact resolve eq16646 eq20219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16646
  have eq20524 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by grind
  clear eq20497
  have eq20532 : (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq20524
       have r₂ := eq27
       grind)
    | exact resolve eq20524 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20524
  have eq20541 : (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq30 eq20488
    | exact resolve eq20488 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq20488
  have eq20550 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) X0)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq20532 eq14
    | exact resolve eq14 eq20532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20821 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x y) X1)) = (M.op X0 x) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X1 x X0 y
       have i₂ := eq20541
       grind)
    | exact superpose eq20541 eq54
    | exact resolve eq54 eq20541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20541
  have eq20829 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq257 eq20821
    | exact resolve eq20821 eq257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20821
  have eq23487 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq20829 x
       grind)
    | exact superpose eq20829 eq18
    | (have j1 := eq20829 x
       grind)
    | exact resolve eq18 eq20829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20829
  have eq23506 : (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by grind
  clear eq23487
  have eq23516 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq119
       have i₂ := eq23506
       grind)
    | exact superpose eq23506 eq119
    | exact resolve eq119 eq23506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23528 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ (M.op x y)) X1)) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq560 x X0 X1
       have i₂ := eq23506
       grind)
    | exact superpose eq23506 eq560
    | exact resolve eq560 eq23506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23534 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x y) X1)) = (M.op X0 x) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X1 x X0 x
       have i₂ := eq23506
       grind)
    | exact superpose eq23506 eq54
    | exact resolve eq54 eq23506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23506
  have eq23543 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq257 eq23534
    | exact resolve eq23534 eq257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23534
  have eq23549 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ (M.op x y)) X1)) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | exact superpose eq20 eq23528
    | (have j0 := eq23528 X0 X1
       grind)
    | exact resolve eq23528 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23528
  have eq23559 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq23516
    | exact resolve eq23516 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23516
  have eq23561 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ (M.op x y)) X1)) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq23549 X0 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq23549
    | (have j0 := eq23549 X0 X1
       grind)
    | exact resolve eq23549 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23549
  have eq23904 : (M.op (σ y) (σ y)) = (σ (M.op y x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq118
       have i₂ := eq23543 y
       grind)
    | exact superpose eq23543 eq118
    | exact resolve eq118 eq23543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq23543
  have eq132824 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20532 eq20550
    | exact resolve eq20550 eq20532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20532 eq20550
  have eq132930 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by grind
  clear eq132824
  have eq132937 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq132930
    | exact resolve eq132930 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132930
  have eq132955 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq132937 eq20219
    | exact resolve eq20219 eq132937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20219 eq132937
  have eq133206 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by grind
  clear eq132955
  have eq133218 : (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq133206
       have r₂ := eq27
       grind)
    | exact resolve eq133206 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133206
  have eq133224 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq23904
       have i₂ := eq133218
       grind)
    | exact superpose eq133218 eq23904
    | exact resolve eq23904 eq133218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23904
  have eq133251 : y ≠ (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq133218
  have eq133271 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq133224
    | exact resolve eq133224 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133224
  have eq134118 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq133271
       have r₂ := eq133251
       grind)
    | exact resolve eq133271 eq133251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133251 eq133271
  have eq134147 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ (M.op x y)) X0)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq134118 eq14
    | exact resolve eq14 eq134118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134118
  have eq135176 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq134147 eq23561
    | exact resolve eq23561 eq134147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23561 eq134147
  have eq135214 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq135176 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135176
  have eq135249 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq135214
    | (have j0 := eq135214 (σ x)
       grind)
    | exact resolve eq135214 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135214
  have eq136213 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq135249 eq23559
    | exact resolve eq23559 eq135249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23559 eq135249
  have eq136448 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq136213
  have eq136467 : y = (M.op y x) := by
    first
    | (have r₁ := eq136448
       have r₂ := eq27
       grind)
    | exact resolve eq136448 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136448
  have eq136473 : y ≠ y ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq136467
       grind)
    | exact superpose eq136467 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq136467
       grind)
    | exact resolve eq13 eq136467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136474 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq136467
       grind)
    | exact superpose eq136467 eq14
    | exact resolve eq14 eq136467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136482 : (k x y) = (M.op x x) := by grind
  clear eq136473
  have eq136488 : (k (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq136482
       grind)
    | exact superpose eq136482 eq44
    | exact resolve eq44 eq136482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136482
  have eq136517 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq136488
       have i₂ := eq119
       grind)
    | exact superpose eq119 eq136488
    | exact resolve eq136488 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136488
  have eq136549 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq136474 x
       have i₂ := eq136467
       grind)
    | exact superpose eq136467 eq136474
    | exact resolve eq136474 eq136467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136474
  have eq136622 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq136549
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq136549
    | exact resolve eq136549 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq136549
  have eq136628 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq119
       have i₂ := eq136622
       grind)
    | exact superpose eq136622 eq119
    | exact resolve eq119 eq136622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq136690 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x y) X1)) = (M.op X0 x) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X1 x X0 x
       have i₂ := eq136622
       grind)
    | exact superpose eq136622 eq54
    | exact resolve eq54 eq136622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136622
  have eq136697 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | exact superpose eq257 eq136690
    | exact resolve eq136690 eq257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257 eq136690
  have eq136717 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq20 eq136628
    | exact resolve eq136628 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq136628
  have eq136818 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ (M.op y x)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq560 y X0 X1
       have i₂ := eq136697 y
       grind)
    | exact superpose eq136697 eq560
    | exact resolve eq560 eq136697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560 eq136697
  have eq136902 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ y) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq136818 X0 X1
       have i₂ := eq136467
       grind)
    | exact superpose eq136467 eq136818
    | exact resolve eq136818 eq136467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136467 eq136818
  have eq136929 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ y) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq136902 X0 X1
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq136902
    | (have j0 := eq136902 X0 X1
       grind)
    | exact resolve eq136902 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq136902
  have eq152050 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq6582 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6582
    | (have j0 := eq6582 x X0
       grind)
    | exact resolve eq6582 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq6582
  have eq152081 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq152050 X0
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq152050
    | (have j0 := eq152050 X0
       grind)
    | exact resolve eq152050 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq152050
  have eq152159 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq136517 eq152081
    | (have j0 := eq152081 (σ x)
       grind)
    | exact resolve eq152081 eq136517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136517 eq152081
  have eq152207 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq136717 eq152159
    | (have j0 := eq152159 X0
       grind)
    | exact resolve eq152159 eq136717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152159
  have eq152249 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq152207
    | (have j0 := eq152207 X0
       grind)
    | exact resolve eq152207 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152207
  have eq152289 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have j0 := eq152249 X0
       grind)
    | (have r₁ := eq152249 X0
       have r₂ := eq27
       grind)
    | exact resolve eq152249 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152249
  have eq152489 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq152289 eq26
    | (have j1 := eq152289 (σ x)
       grind)
    | exact resolve eq26 eq152289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152289
  have eq152538 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq136717 eq152489
    | exact resolve eq152489 eq136717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152489
  have eq152557 : (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq152538
       have r₂ := eq27
       grind)
    | exact resolve eq152538 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152538
  have eq152573 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq152557 eq54
    | exact resolve eq54 eq152557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq152557
  have eq152581 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | exact superpose eq136929 eq152573
    | exact resolve eq152573 eq136929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136929 eq152573
  have eq153302 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq152581 eq26
    | (have j1 := eq152581 (σ x)
       grind)
    | exact resolve eq26 eq152581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq152581
  have eq153341 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq136717 eq153302
    | exact resolve eq153302 eq136717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136717 eq153302
  have eq153371 : False := by grind
  exact eq153371

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyx_pxy_pyx_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
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
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq88 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq354 : ∀ X0 X1 : G, (σ X1) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq88 X0 X1
       grind)
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq88 X0 X1
       grind)
    | exact superpose eq88 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq88 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq88 X0 X1
       grind)
    | exact resolve eq12 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq356 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq88 X0 X1
       grind)
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
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq88 X0 X1
       grind)
    | exact resolve eq13 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq363 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq356 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356
  have eq371 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq363 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq363 X1 X1
       have r₂ := eq12 (σ X1) (σ X1)
       grind)
    | (have r₁ := eq363 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq363 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363
  have eq373 : ∀ X0 X1 : G, (σ X1) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq354 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq354 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq354 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354
  have eq385 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq371 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq371
    | (have j0 := eq371 X0 X1
       grind)
    | exact resolve eq371 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371
  have eq386 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq385 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385
  have eq387 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq373 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq373
    | (have j0 := eq373 X0 X1
       grind)
    | exact resolve eq373 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373
  have eq388 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) ≠ (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq387 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387
  have eq393 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq388 X0 X1
       have j1 := eq386 X0 X1
       grind)
    | (have r₁ := eq388 X0 X1
       have r₂ := eq386 X0 X1
       grind)
    | exact resolve eq388 eq386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386 eq388
  have eq394 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq393 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq393
    | exact resolve eq393 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq405 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq393 x y
       grind)
    | exact superpose eq393 eq16
    | exact resolve eq16 eq393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393
  have eq496 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq394 X0 (τ X1)
       grind)
    | exact superpose eq394 eq18
    | exact resolve eq18 eq394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq394
  have eq517 : ∀ X0 X1 : G, (M.op X0 X1) = (k (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq496 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq496
    | exact resolve eq496 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496
  have eq527 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq517 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq517
    | exact resolve eq517 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517
  have eq554 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq405
       have i₂ := eq527 x y
       grind)
    | exact superpose eq527 eq405
    | exact resolve eq405 eq527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405 eq527
  have eq555 : False := by grind
  exact eq555

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyx_pxy_pyy_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  clear eq22
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
  have eq50 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x y) X0)) := by
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
  have eq51 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
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
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 X0 X1 X2 X3
       have i₂ := eq14 X2 X1 X0
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq74 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  clear eq24 eq36
  have eq76 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq16
    | exact resolve eq16 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq76 x y
       grind)
    | exact superpose eq76 eq44
    | (have j1 := eq76 x y
       grind)
    | exact resolve eq44 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq105 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq99
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq99
    | exact resolve eq99 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq108 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq20 eq105
    | exact resolve eq105 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq109 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq108
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq108
    | exact resolve eq108 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq116 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq116 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq116 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq116 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq120 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq117 x
       grind)
    | exact superpose eq117 eq43
    | exact resolve eq43 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq121 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq74
       have i₂ := eq117 y
       grind)
    | exact superpose eq117 eq74
    | exact resolve eq74 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq123 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq86
       have i₂ := eq117 sF3
       grind)
    | exact superpose eq117 eq86
    | exact resolve eq86 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq124 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq123
       have i₂ := eq117 y
       grind)
    | exact superpose eq117 eq123
    | exact resolve eq123 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq126 : (σ (M.op y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq121
       have i₂ := eq117 sF3
       grind)
    | exact superpose eq117 eq121
    | exact resolve eq121 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq127 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq120
       have i₂ := eq117 sF2
       grind)
    | exact superpose eq117 eq120
    | exact resolve eq120 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq120
  have eq262 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ x) (σ y)) X0)) = (M.op X1 (M.op (M.op X0 (σ y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq265 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ x) (σ y)) X0)) = (M.op X1 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq262 x X0
       have i₂ := eq14 X0 sF3 x
       grind)
    | exact superpose eq14 eq262
    | exact resolve eq262 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262
  have eq939 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq109 eq76
    | (have j0 := eq76 (σ x) (σ y)
       grind)
    | exact resolve eq76 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq940 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq939
    | exact resolve eq939 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq939
  have eq943 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq940
       have r₂ := eq27
       grind)
    | exact resolve eq940 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq940
  have eq945 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq943
    | exact resolve eq943 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq943
  have eq949 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq945 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq945
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq945
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq945
       grind)
    | exact resolve eq12 eq945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq951 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq945 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq952 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) = (M.op X0 (σ x)) ∨ (M.op x y) = (M.op y x) := by
    intro X0
    first
    | exact superpose eq945 eq14
    | exact resolve eq14 eq945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq953 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (M.op x y) = (M.op y x) := by
    intro X0
    first
    | exact superpose eq51 eq952
    | exact resolve eq952 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq952
  have eq954 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq951
    | exact resolve eq951 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq951
  have eq956 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq949
       have r₂ := eq26
       grind)
    | exact resolve eq949 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq949
  have eq971 : (M.op y y) = (τ (M.op (σ y) (σ x))) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq953 eq124
    | exact resolve eq124 eq953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq953
  have eq1003 : (M.op y y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq945 eq971
    | exact resolve eq971 eq945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq945 eq971
  have eq1017 : (M.op y y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq1003
  have eq1019 : (M.op (σ y) (σ y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq126
       have i₂ := eq1017
       grind)
    | exact superpose eq1017 eq126
    | exact resolve eq126 eq1017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1017
  have eq1031 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq1019
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq1019
    | exact resolve eq1019 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1019
  have eq1050 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq956 eq109
    | exact resolve eq109 eq956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq956
  have eq1053 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1050
  have eq1060 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1053 eq1031
    | exact resolve eq1031 eq1053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1031 eq1053
  have eq1072 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1060
  have eq1079 : (M.op x y) = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1072
       have r₂ := eq27
       grind)
    | exact resolve eq1072 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1072
  have eq1086 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) X0)) = (M.op X0 x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq1079
       grind)
    | exact superpose eq1079 eq14
    | exact resolve eq14 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1087 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq50 eq1086
    | exact resolve eq1086 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1086
  have eq1093 : (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1087 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1087
    | (have j0 := eq1087 x
       grind)
    | exact resolve eq1087 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1105 : (σ (M.op y x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq126
       have i₂ := eq1087 y
       grind)
    | exact superpose eq1087 eq126
    | exact resolve eq126 eq1087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1087
  have eq1114 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq127
       have i₂ := eq1093
       grind)
    | exact superpose eq1093 eq127
    | exact resolve eq127 eq1093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1093
  have eq1128 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1114
    | exact resolve eq1114 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1114
  have eq1184 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ (M.op x y)) X1)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq1128 eq54
    | exact resolve eq54 eq1128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1246 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1105
       have i₂ := eq1079
       grind)
    | exact superpose eq1079 eq1105
    | exact resolve eq1105 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1079 eq1105
  have eq1261 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1246
  have eq1263 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1261
    | exact resolve eq1261 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1261
  have eq1270 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ (M.op x y)) X1)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq1263 eq54
    | exact resolve eq54 eq1263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1263
  have eq1387 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1270 eq1184
    | exact resolve eq1184 eq1270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1184 eq1270
  have eq1402 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq1387 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1387
  have eq1462 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1402
    | (have j0 := eq1402 (σ x)
       grind)
    | exact resolve eq1402 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1402
  have eq1494 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1462 eq1128
    | exact resolve eq1128 eq1462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1128 eq1462
  have eq1504 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1494
  have eq1511 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1504
       have r₂ := eq27
       grind)
    | exact resolve eq1504 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1504
  have eq1513 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq1511 eq954
    | (have r₁ := eq954
       have r₂ := eq1511
       grind)
    | exact resolve eq954 eq1511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq954
  have eq1515 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq1511 eq265
    | exact resolve eq265 eq1511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq1517 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq1511 eq27
    | exact resolve eq27 eq1511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq1518 : (σ y) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq1513
  have eq1773 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq1518 eq109
    | exact resolve eq109 eq1518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq1518
  have eq1776 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq1773
  have eq1782 : (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq1776
       have r₂ := eq1517
       grind)
    | exact resolve eq1776 eq1517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1776
  have eq1791 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) X0)) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq1782
       grind)
    | exact superpose eq1782 eq14
    | exact resolve eq14 eq1782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1792 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | exact superpose eq50 eq1791
    | exact resolve eq1791 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq1791
  have eq1853 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq1792 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1792
    | (have j0 := eq1792 x
       grind)
    | exact resolve eq1792 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1867 : (σ (M.op y x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq126
       have i₂ := eq1792 y
       grind)
    | exact superpose eq1792 eq126
    | exact resolve eq126 eq1792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126 eq1792
  have eq1875 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1867
       have i₂ := eq1782
       grind)
    | exact superpose eq1782 eq1867
    | exact resolve eq1867 eq1782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1782 eq1867
  have eq1880 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq20 eq1875
    | exact resolve eq1875 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1875
  have eq1884 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq127
       have i₂ := eq1853
       grind)
    | exact superpose eq1853 eq127
    | exact resolve eq127 eq1853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq1853
  have eq1898 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq20 eq1884
    | exact resolve eq1884 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1884
  have eq1967 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq1880 eq1515
    | exact resolve eq1515 eq1880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1515
  have eq1971 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ (M.op x y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq1880 eq54
    | exact resolve eq54 eq1880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1880
  have eq1990 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ (M.op x y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq1898 eq54
    | exact resolve eq54 eq1898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq2095 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1967 eq26
    | (have j1 := eq1967 (σ x)
       grind)
    | exact resolve eq26 eq1967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq2105 : (σ y) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1511 eq2095
    | exact resolve eq2095 eq1511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1511 eq2095
  have eq2342 : ∀ X0 X1 : G, (M.op X0 (M.op (σ (M.op x y)) X1)) = (M.op X0 (σ (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq1967 eq1971
    | exact resolve eq1971 eq1967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1967 eq1971
  have eq2518 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq2342 eq1990
    | exact resolve eq1990 eq2342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1990 eq2342
  have eq2681 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq2518 eq1898
    | exact resolve eq1898 eq2518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1898 eq2518
  have eq2692 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2105 eq2681
    | exact resolve eq2681 eq2105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2105 eq2681
  have eq2699 : False := by grind
  exact eq2699
