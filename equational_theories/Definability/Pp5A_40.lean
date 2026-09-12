import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxx_pxy_pxy_pxx_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 := by
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
  have eq19 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 (M.op X0 X0)) X2 X0
       have i₂ := eq9 X0 (M.op X1 (M.op X0 X0)) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op X0 X0) X0 x
       have i₂ := eq9 X0 x (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq32 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
    | (have i₁ := eq26 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq26
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq44 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq44 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq44 X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq44 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq47 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq45 (σ X0)
       grind)
    | exact superpose eq45 eq15
    | exact resolve eq15 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq45 (τ X0)
       grind)
    | exact superpose eq45 eq18
    | exact resolve eq18 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq49 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq49
    | exact resolve eq49 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq54 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq47 X0
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq47
    | exact resolve eq47 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq57 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq52 X0
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq52
    | exact resolve eq52 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq83 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq77 X0 X1
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq77
    | (have j0 := eq77 X0 X1
       grind)
    | exact resolve eq77 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq86 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq83 X0 X1
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq83
    | (have j0 := eq83 X0 X1
       grind)
    | exact resolve eq83 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq89 : ∀ X0 X1 : G, (σ (M.op (k (τ X0) X1) (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq54 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq54
    | exact resolve eq54 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq13
    | exact resolve eq13 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq20 (σ X0)
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq20
    | exact resolve eq20 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq94 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) (M.op X1 (M.op X2 (σ (M.op X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X1 X2
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq9
    | exact resolve eq9 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq106 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq57 X0
       grind)
    | exact superpose eq57 eq10
    | exact resolve eq10 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) = (M.op (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 (M.op X3 X1) X2 (M.op X0 (M.op X1 X1))
       have i₂ := eq19 X1 X0 X3
       grind)
    | exact superpose eq19 eq19
    | exact resolve eq19 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq147 : ∀ X0 X1 X2 : G, (M.op X1 (τ (M.op X0 X0))) = (M.op (M.op X1 (τ (M.op X0 X0))) (M.op X2 (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 (τ X0) X1 X2
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq19
    | exact resolve eq19 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq149 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (k (τ X0) X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (τ X0) X1
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq12
    | (have j0 := eq12 (τ X0) X1
       grind)
    | exact resolve eq12 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq151 : ∀ X0 X1 X2 : G, (τ X0) = (M.op (τ X0) (M.op X1 (M.op X2 (τ (M.op X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (τ X0) X1 X2
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq9
    | exact resolve eq9 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq158 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (M.op (k (τ X0) X1) (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (σ (M.op (k (τ X0) X1) (k (τ X0) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq86 (k (τ X0) X1) X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq86
    | exact resolve eq86 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq161 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq86 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq86
    | (have j0 := eq86 X1 X1
       grind)
    | exact resolve eq86 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq179 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq161 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq161
    | (have j0 := eq161 X0 X1
       grind)
    | exact resolve eq161 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161
  have eq182 : ∀ X0 X1 X2 : G, (M.op (k X0 (σ X1)) (k X0 (σ X1))) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (σ (M.op (k (τ X0) X1) (k (τ X0) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq158 X0 X1 X2
       have i₂ := eq89 X0 X1
       grind)
    | exact superpose eq89 eq158
    | (have j0 := eq158 X0 X1 X2
       grind)
    | exact resolve eq158 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq185 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq179 X0 X1
       have j1 := eq92 X1 X0
       grind)
    | (have r₁ := eq179 X0 X0
       have r₂ := eq92 X0 X1
       grind)
    | exact resolve eq179 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq188 : ∀ X0 X1 X2 : G, (M.op (k X0 (σ X1)) (k X0 (σ X1))) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq182 X0 X1 X2
       have i₂ := eq89 X0 X1
       grind)
    | exact superpose eq89 eq182
    | (have j0 := eq182 X0 X1 X2
       grind)
    | exact resolve eq182 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq182
  have eq292 : ∀ X0 X1 X2 : G, (τ (τ X0)) = (M.op (τ (τ X0)) (M.op X1 (M.op X2 (τ (τ (M.op X0 X0)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq151 (τ X0) X1 X2
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq151
    | exact resolve eq151 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151
  have eq416 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq185 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq185
    | exact resolve eq185 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq423 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq185 (σ X1) X0
       grind)
    | exact superpose eq185 eq15
    | (have j1 := eq185 (σ X1) X0
       grind)
    | exact resolve eq15 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq426 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X0 X1
       have i₂ := eq185 X1 X0
       grind)
    | exact superpose eq185 eq32
    | (have j1 := eq185 X1 X0
       grind)
    | exact resolve eq32 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq185
  have eq439 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq416 X0 X1
       have i₂ := eq57 X0
       grind)
    | exact superpose eq57 eq416
    | (have j0 := eq416 X0 X1
       grind)
    | exact resolve eq416 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416
  have eq450 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq439 X0 (τ X1)
       grind)
    | exact superpose eq439 eq18
    | (have j1 := eq439 X0 (τ X1)
       grind)
    | exact resolve eq18 eq439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq439
  have eq702 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2))) x
       have i₂ := eq118 x X2 X0 X1
       grind)
    | exact superpose eq118 eq9
    | exact resolve eq9 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq735 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) (M.op X1 X0)) X2 X0
       have i₂ := eq702 (M.op (M.op X1 X0) (M.op X1 X0)) X1 X0
       grind)
    | exact superpose eq702 eq9
    | exact resolve eq9 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1393 : ∀ X0 X1 X2 : G, (M.op X1 (τ (τ (M.op X0 X0)))) = (M.op (M.op X1 (τ (τ (M.op X0 X0)))) (M.op X2 (τ (τ X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 (τ (τ (M.op X0 X0)))) X2 (τ (τ X0))
       have i₂ := eq292 X0 (M.op X1 (τ (τ (M.op X0 X0)))) X1
       grind)
    | exact superpose eq292 eq9
    | exact resolve eq9 eq292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292
  have eq1912 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq450 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq450
    | exact resolve eq450 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450
  have eq1973 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1912 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1912
    | (have j0 := eq1912 X0 X1
       grind)
    | exact resolve eq1912 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1912
  have eq2049 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) ≠ (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq188 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq2267 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 (M.op X2 (σ (M.op X0 X0)))))) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq426 X0 (M.op X1 (M.op X2 (σ (M.op X0 X0))))
       have i₂ := eq94 X0 X1 X2
       grind)
    | exact superpose eq94 eq426
    | exact resolve eq426 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq426
  have eq2307 : ∀ X0 X1 X2 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k X0 (τ (M.op X1 (M.op X2 (σ (M.op X0 X0)))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2267 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2267
    | (have j0 := eq2267 X0 X1 X2
       grind)
    | exact resolve eq2267 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2267
  have eq2905 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq702 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))) X1 X2
       have i₂ := eq735 (M.op X1 X2) X0 (M.op X1 X2)
       grind)
    | exact superpose eq735 eq702
    | exact resolve eq702 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702 eq735
  have eq2990 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X3 (M.op X1 (M.op X2 X0)))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 (M.op X0 (M.op X1 X2)) X2 X2
       have i₂ := eq2905 X0 X1 X2
       grind)
    | exact superpose eq2905 eq19
    | exact resolve eq19 eq2905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq2991 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op X1 (M.op X2 X0)) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X1 (M.op X2 X0)) X3 X0
       have i₂ := eq2905 X1 X2 X0
       grind)
    | exact superpose eq2905 eq9
    | exact resolve eq9 eq2905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2905
  have eq3312 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (σ X0))) = (M.op (M.op X1 (M.op X2 (σ X0))) (σ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2991 (σ X0) X1 X2 (σ (M.op X0 X0))
       have i₂ := eq93 X0
       grind)
    | exact superpose eq93 eq2991
    | exact resolve eq2991 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq6536 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq423 x y
       grind)
    | exact superpose eq423 eq16
    | (have j1 := eq423 x y
       grind)
    | exact resolve eq16 eq423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6603 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq423 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423
  have eq6654 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq6536
       have i₂ := eq1973 y x
       grind)
    | exact superpose eq1973 eq6536
    | (have j1 := eq1973 y x
       grind)
    | (have r₁ := eq6536
       have r₂ := eq1973 y x
       grind)
    | exact resolve eq6536 eq1973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6536
  have eq6655 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq6654
  have eq6809 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op x x) ∨ x = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq6655
       grind)
    | exact superpose eq6655 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq6655
       grind)
    | exact resolve eq13 eq6655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6828 : (k x y) = (M.op x x) ∨ x = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq6809
  have eq10785 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (σ (τ X0)) ∨ (τ X0) = (k (τ X0) (τ (M.op X1 (M.op X2 (M.op X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2307 (τ X0) X1 X2
       have i₂ := eq57 X0
       grind)
    | exact superpose eq57 eq2307
    | exact resolve eq2307 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq10807 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (τ (σ X0)) ∨ (k X0 (τ (M.op X1 (M.op X2 (σ (M.op X0 X0)))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq2307 X0 X1 X2
       grind)
    | exact superpose eq2307 eq10
    | (have j1 := eq2307 X0 X1 X2
       grind)
    | exact resolve eq10 eq2307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2307
  have eq10887 : ∀ X0 X1 X2 : G, (k X0 (τ (M.op X1 (M.op X2 (σ (M.op X0 X0)))))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10807 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq10807
    | (have j0 := eq10807 X0 X1 X2
       grind)
    | exact resolve eq10807 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10807
  have eq10896 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (τ X0) = (k (τ X0) (τ (M.op X1 (M.op X2 (M.op X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10785 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq10785
    | (have j0 := eq10785 X0 X1 X2
       grind)
    | exact resolve eq10785 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10785
  have eq10903 : ∀ X0 X1 X2 : G, (τ X0) = (τ (k X0 (M.op X1 (M.op X2 (M.op X0 X0))))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10896 X0 X1 X2
       have i₂ := eq35 (M.op X1 (M.op X2 (M.op X0 X0))) X0
       grind)
    | exact superpose eq35 eq10896
    | (have j0 := eq10896 X0 X1 X2
       grind)
    | exact resolve eq10896 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq10896
  have eq10922 : ∀ X0 X1 X2 X3 : G, (k X2 (τ (M.op X3 (M.op X0 (M.op X1 (σ X2)))))) = X2 ∨ (M.op X2 X2) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq10887 X2 X3 (M.op X0 (M.op X1 (σ X2)))
       have i₂ := eq3312 X2 X0 X1
       grind)
    | exact superpose eq3312 eq10887
    | (have j0 := eq10887 X2 X1 X2
       grind)
    | exact resolve eq10887 eq3312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3312 eq10887
  have eq11390 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (M.op X1 (M.op X2 (M.op X0 X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 (k X0 (M.op X1 (M.op X2 (M.op X0 X0))))
       have i₂ := eq10903 X0 X1 X2
       grind)
    | exact superpose eq10903 eq11
    | (have j1 := eq10903 X0 X1 X2
       grind)
    | exact resolve eq11 eq10903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10903
  have eq11525 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11390 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq11390
    | (have j0 := eq11390 X0 X1 X2
       grind)
    | exact resolve eq11390 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11390
  have eq11598 : ∀ X0 X1 X2 X3 : G, (k X2 (M.op X3 (M.op X0 (M.op X1 X2)))) = X2 ∨ (M.op X2 X2) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq11525 X2 X3 (M.op X0 (M.op X1 X2))
       have i₂ := eq2991 X2 X0 X1 X2
       grind)
    | exact superpose eq2991 eq11525
    | (have j0 := eq11525 X2 X1 X2
       grind)
    | exact resolve eq11525 eq2991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2991 eq11525
  have eq13699 : ∀ X0 X1 X2 X3 : G, (σ (τ X0)) = (k X0 (σ (τ (M.op X1 (M.op X2 (M.op X3 (σ (τ X0)))))))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq17 X0 (τ (M.op X1 (M.op X2 (M.op X3 (σ (τ X0))))))
       have i₂ := eq10922 X2 X3 (τ X0) X1
       grind)
    | exact superpose eq10922 eq17
    | (have j1 := eq10922 X0 X1 (τ X0) X3
       grind)
    | exact resolve eq17 eq10922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10922
  have eq13775 : ∀ X0 X1 X2 X3 : G, (σ (τ X0)) = (k X0 (M.op X1 (M.op X2 (M.op X3 (σ (τ X0)))))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13699 X0 X1 X2 X3
       have i₂ := eq11 (M.op X1 (M.op X2 (M.op X3 (σ (τ X0)))))
       grind)
    | exact superpose eq11 eq13699
    | (have j0 := eq13699 X0 X1 X2 X3
       grind)
    | exact resolve eq13699 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13699
  have eq13830 : ∀ X0 X1 X2 X3 : G, (k X0 (M.op X1 (M.op X2 (M.op X3 X0)))) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13775 X0 X1 X2 X3
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq13775
    | (have j0 := eq13775 X0 X1 X2 X3
       grind)
    | exact resolve eq13775 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13775
  have eq13875 : ∀ X0 X1 X2 X3 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (k X0 (M.op X1 (M.op X2 (M.op X3 X0)))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13830 X0 X1 X2 X3
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq13830
    | (have j0 := eq13830 X0 X1 X2 X3
       grind)
    | exact resolve eq13830 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13830
  have eq13932 : ∀ X0 X1 X2 X3 X4 : G, (τ X0) ≠ (τ X0) ∨ (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (k X0 (M.op X2 (M.op X3 (M.op X4 X0)))) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq149 X0 X1
       have i₂ := eq13875 X0 X2 X3 X4
       grind)
    | exact superpose eq13875 eq149
    | (have j0 := eq149 X0 X1
       have j1 := eq13875 X0 X2 X3 X4
       grind)
    | (have r₁ := eq149 X0 X1
       have r₂ := eq13875 X0 X1 X2 X3
       grind)
    | exact resolve eq149 eq13875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149 eq13875
  have eq14029 : ∀ X0 X1 X2 X3 X4 : G, (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (k X0 (M.op X2 (M.op X3 (M.op X4 X0)))) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have j0 := eq13932 X0 X1 X2 X3 X4
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13932
  have eq31924 : ∀ X0 X1 X2 X3 X4 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k X0 (M.op X2 (M.op X3 (M.op X4 X0)))) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq14029 X0 X1 X2 X3 X4
       grind)
    | exact superpose eq14029 eq17
    | (have j1 := eq14029 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq17 eq14029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14029
  have eq44888 : ∀ X0 X1 X2 X3 X4 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (k (σ (τ X0)) X1) = (M.op (σ (τ X0)) X1) ∨ (k X0 (M.op X2 (M.op X3 (M.op X4 X0)))) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq92 (τ X0) X1
       have i₂ := eq31924 X0 (τ X0) X2 X3 X4
       grind)
    | exact superpose eq31924 eq92
    | (have j0 := eq92 (τ X0) X1
       have j1 := eq31924 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq92 eq31924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq31924
  have eq45078 : ∀ X0 X1 X2 X3 X4 : G, (k X0 X0) ≠ X0 ∨ (k (σ (τ X0)) X1) = (M.op (σ (τ X0)) X1) ∨ (k X0 (M.op X2 (M.op X3 (M.op X4 X0)))) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq44888 X0 X1 X2 X3 X4
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq44888
    | (have j0 := eq44888 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq44888 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44888
  have eq45159 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X0) ≠ X0 ∨ (k (σ (τ X0)) X1) = (M.op (σ (τ X0)) X1) ∨ (k X0 (M.op X2 (M.op X3 (M.op X4 X0)))) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq45078 X0 X1 X2 X3 X4
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq45078
    | (have j0 := eq45078 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq45078 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq45078
  have eq45192 : ∀ X0 X1 X2 X3 X4 : G, (k (σ (τ X0)) X1) = (M.op (σ (τ X0)) X1) ∨ (k X0 (M.op X2 (M.op X3 (M.op X4 X0)))) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have j0 := eq45159 X0 X1 X2 X3 X4
       have j1 := eq11598 X3 X4 X0 X2
       grind)
    | (have r₁ := eq45159 X2 X1 X2 X3 X4
       have r₂ := eq11598 X0 X1 X2 X3
       grind)
    | exact resolve eq45159 eq11598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11598 eq45159
  have eq45208 : ∀ X0 X1 X2 X3 X4 : G, (k X0 (M.op X2 (M.op X3 (M.op X4 X0)))) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq45192 X0 X1 X2 X3 X4
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq45192
    | (have j0 := eq45192 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq45192 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45192
  have eq45480 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X3 X0)))) ≠ X0 ∨ (M.op X0 (M.op X1 (M.op X2 (M.op X3 X0)))) = (k X0 (M.op X1 (M.op X2 (M.op X3 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq45208 X0 (M.op X1 (M.op X2 (M.op X3 X0))) X2 X3 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45208
  have eq45481 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X3 X0)))) = (k X0 (M.op X1 (M.op X2 (M.op X3 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq45480 X0 X1 X2 X3
       grind)
    | (have r₁ := eq45480 X0 X3 X1 X2
       have r₂ := eq2990 X0 X1 X2 X3
       grind)
    | exact resolve eq45480 eq2990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45480
  have eq45527 : ∀ X0 X1 X2 X3 : G, (k X0 (M.op X1 (M.op X2 (M.op X3 X0)))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq45481 X0 X1 X2 X3
       have i₂ := eq2990 X0 X2 X3 X1
       grind)
    | exact superpose eq2990 eq45481
    | exact resolve eq45481 eq2990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2990 eq45481
  have eq45919 : ∀ X0 X1 X2 X3 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 (M.op X2 (M.op X3 (τ X0)))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq17 X0 (M.op X1 (M.op X2 (M.op X3 (τ X0))))
       have i₂ := eq45527 (τ X0) X1 X2 X3
       grind)
    | exact superpose eq45527 eq17
    | exact resolve eq17 eq45527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45527
  have eq45984 : ∀ X0 X1 X2 X3 : G, (k X0 (σ (M.op X1 (M.op X2 (M.op X3 (τ X0)))))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq45919 X0 X1 X2 X3
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq45919
    | exact resolve eq45919 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45919
  have eq46447 : ∀ X0 X1 X2 : G, (k X1 (σ (M.op X2 (M.op X0 (τ (M.op X1 X1)))))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq45984 X1 X2 (M.op X0 (τ (M.op X1 X1))) x
       have i₂ := eq147 X1 X0 x
       grind)
    | exact superpose eq147 eq45984
    | exact resolve eq45984 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq46448 : ∀ X0 X1 X2 : G, (τ X1) = (k (τ X1) (σ (M.op X2 (M.op X0 (τ (τ (M.op X1 X1))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq45984 (τ X1) X2 (M.op X0 (τ (τ (M.op X1 X1)))) x
       have i₂ := eq1393 X1 X0 x
       grind)
    | exact superpose eq1393 eq45984
    | exact resolve eq45984 eq1393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1393 eq45984
  have eq48540 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op X1 (M.op X2 (τ (M.op (τ X0) (τ X0)))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X0 (σ (M.op X1 (M.op X2 (τ (M.op (τ X0) (τ X0))))))
       have i₂ := eq46447 X2 (τ X0) X1
       grind)
    | exact superpose eq46447 eq17
    | exact resolve eq17 eq46447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46447
  have eq48617 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op X1 (M.op X2 (τ (τ (M.op X0 X0)))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq48540 X0 X1 X2
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq48540
    | exact resolve eq48540 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq48540
  have eq48684 : ∀ X0 X1 X2 : G, (k X0 (σ (σ (M.op X1 (M.op X2 (τ (τ (M.op X0 X0)))))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq48617 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq48617
    | exact resolve eq48617 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48617
  have eq58241 : ∀ X0 X1 X2 X3 : G, (M.op X0 (σ X3)) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 (σ X3)) = (σ (k (k (τ X0) (σ (M.op X1 (M.op X2 (τ (τ (M.op X0 X0))))))) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2049 X0 (σ (M.op X1 (M.op X2 (τ (τ (M.op X0 X0)))))) X2
       have i₂ := eq48684 X0 X1 X2
       grind)
    | exact superpose eq48684 eq2049
    | exact resolve eq2049 eq48684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2049 eq48684
  have eq58398 : ∀ X0 X3 : G, (σ (k (τ X0) X3)) = (M.op X0 (σ X3)) ∨ (M.op X0 (σ X3)) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X3
    first
    | (have i₁ := eq58241 X0 x x X3
       have i₂ := eq46448 x X0 x
       grind)
    | exact superpose eq46448 eq58241
    | (have j0 := eq58241 X0 x x X3
       grind)
    | exact resolve eq58241 eq46448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46448 eq58241
  have eq58462 : ∀ X0 X3 : G, (k X0 (σ X3)) = (M.op X0 (σ X3)) ∨ (M.op X0 (σ X3)) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X3
    first
    | (have i₁ := eq58398 X0 X3
       have i₂ := eq17 X0 X3
       grind)
    | exact superpose eq17 eq58398
    | (have j0 := eq58398 X0 X3
       grind)
    | exact resolve eq58398 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq58398
  have eq58503 : ∀ X0 X3 : G, (M.op X0 (σ X3)) ≠ X0 ∨ (k X0 (σ X3)) = (M.op X0 (σ X3)) := by
    intro X0 X3
    first
    | (have j0 := eq58462 X0 X3
       have j1 := eq12 X0 (σ X3)
       grind)
    | (have r₁ := eq58462 X0 X3
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq58462 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58462
  have eq58574 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq58503 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq58503
    | exact resolve eq58503 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58503
  have eq58738 : x ≠ (M.op x x) ∨ (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq58574 y x
       have i₂ := eq6655
       grind)
    | exact superpose eq6655 eq58574
    | (have j0 := eq58574 x x
       grind)
    | exact resolve eq58574 eq6655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6655
  have eq58806 : (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq58738
       have r₂ := eq6828
       grind)
    | exact resolve eq58738 eq6828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6828 eq58738
  have eq62736 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq6603 x y
       have i₂ := eq58806
       grind)
    | exact superpose eq58806 eq6603
    | (have j0 := eq6603 x y
       grind)
    | exact resolve eq6603 eq58806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6603 eq58806
  have eq62748 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq62736
  have eq62749 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq62748
  have eq62762 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq62749
       grind)
    | exact superpose eq62749 eq16
    | exact resolve eq16 eq62749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62763 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq91 x (σ y)
       have i₂ := eq62749
       grind)
    | exact superpose eq62749 eq91
    | (have j0 := eq91 x (σ y)
       grind)
    | (have r₁ := eq91 x (σ y)
       have r₂ := eq62749
       grind)
    | exact resolve eq91 eq62749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq62823 : (σ x) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq58574 (σ y) (σ x)
       have i₂ := eq62749
       grind)
    | exact superpose eq62749 eq58574
    | exact resolve eq58574 eq62749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58574 eq62749
  have eq62824 : (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq62763
  have eq62825 : (σ (k x y)) = (σ (M.op x x)) ∨ (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq62823
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq62823
    | exact resolve eq62823 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62823
  have eq62838 : (σ (k x y)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq62824
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq62824
    | exact resolve eq62824 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62824
  have eq62842 : (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq62838
       have r₂ := eq62825
       grind)
    | exact resolve eq62838 eq62825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62825 eq62838
  have eq63309 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq1973 y x
       have i₂ := eq62842
       grind)
    | exact superpose eq62842 eq1973
    | (have j0 := eq1973 y x
       grind)
    | exact resolve eq1973 eq62842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1973 eq62842
  have eq63442 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq63309
       have r₂ := eq62762
       grind)
    | exact resolve eq63309 eq62762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63309
  have eq63702 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq62762
       have i₂ := eq63442
       grind)
    | exact superpose eq63442 eq62762
    | exact resolve eq62762 eq63442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62762 eq63442
  have eq63748 : False := by grind
  exact eq63748

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(Y,Y) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_x_pxy_pyy_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq63 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op X0 X0) X0 x
       have i₂ := eq9 X0 x (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq282 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq283 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq282 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282
  have eq285 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq283 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq283 X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq283 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283
  have eq296 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq285 (σ X0)
       grind)
    | exact superpose eq285 eq15
    | exact resolve eq15 eq285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq315 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq296 X0
       have i₂ := eq285 X0
       grind)
    | exact superpose eq285 eq296
    | exact resolve eq296 eq285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285 eq296
  have eq358 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op X1 X1) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) X1
       have i₂ := eq315 X0
       grind)
    | exact superpose eq315 eq14
    | (have j0 := eq14 (σ X0) X1
       grind)
    | exact resolve eq14 eq315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq360 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq315 X0
       grind)
    | exact superpose eq315 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq361 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq63 (σ X0)
       have i₂ := eq315 X0
       grind)
    | exact superpose eq315 eq63
    | exact resolve eq63 eq315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq364 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq358 X0 X1
       have j1 := eq360 X0 X1
       grind)
    | (have r₁ := eq358 X0 X1
       have r₂ := eq360 X0 X1
       grind)
    | exact resolve eq358 eq360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358 eq360
  have eq468 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq364 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq364
    | exact resolve eq364 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq474 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq364 X0 (σ X1)
       grind)
    | exact superpose eq364 eq15
    | (have j1 := eq364 X0 (σ X1)
       grind)
    | exact resolve eq15 eq364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364
  have eq498 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq474 X0 X1
       have i₂ := eq315 X1
       grind)
    | exact superpose eq315 eq474
    | (have j0 := eq474 X0 X1
       grind)
    | exact resolve eq474 eq315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315 eq474
  have eq527 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq468 (τ X0) X1
       grind)
    | exact superpose eq468 eq18
    | (have j1 := eq468 (τ X0) X1
       grind)
    | exact resolve eq18 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq468
  have eq779 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq527 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq527
    | exact resolve eq527 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527
  have eq836 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq779 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq779
    | (have j0 := eq779 X0 X1
       grind)
    | exact resolve eq779 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779
  have eq1177 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq498 x y
       grind)
    | exact superpose eq498 eq16
    | (have j1 := eq498 x y
       grind)
    | exact resolve eq16 eq498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498
  have eq1248 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1177
       have i₂ := eq836 x y
       grind)
    | exact superpose eq836 eq1177
    | (have j1 := eq836 x y
       grind)
    | (have r₁ := eq1177
       have r₂ := eq836 x y
       grind)
    | exact resolve eq1177 eq836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq836 eq1177
  have eq1249 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq1248
  have eq1257 : x = (M.op x y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq63 y
       have i₂ := eq1249
       grind)
    | exact superpose eq1249 eq63
    | exact resolve eq63 eq1249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1259 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq361 y
       have i₂ := eq1249
       grind)
    | exact superpose eq1249 eq361
    | exact resolve eq361 eq1249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1249
  have eq1272 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1259
       grind)
    | exact superpose eq1259 eq16
    | exact resolve eq16 eq1259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1259
  have eq1290 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1272
       have i₂ := eq1257
       grind)
    | exact superpose eq1257 eq1272
    | exact resolve eq1272 eq1257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1257 eq1272
  have eq1291 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq1290
  have eq1292 : (σ x) = (σ (M.op y y)) := by grind
  clear eq1291
  have eq1298 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq361 y
       have i₂ := eq1292
       grind)
    | exact superpose eq1292 eq361
    | exact resolve eq361 eq1292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361
  have eq1299 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq1292
       grind)
    | exact superpose eq1292 eq10
    | exact resolve eq10 eq1292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1292
  have eq1345 : x = (M.op y y) := by
    first
    | (have i₁ := eq1299
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1299
    | exact resolve eq1299 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1299
  have eq1352 : x = (M.op x y) := by
    first
    | (have i₁ := eq63 y
       have i₂ := eq1345
       grind)
    | exact superpose eq1345 eq63
    | exact resolve eq63 eq1345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq1345
  have eq1370 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1298
       grind)
    | exact superpose eq1298 eq16
    | exact resolve eq16 eq1298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1298
  have eq1377 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1370
       have i₂ := eq1352
       grind)
    | exact superpose eq1352 eq1370
    | exact resolve eq1370 eq1352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1352 eq1370
  have eq1378 : False := by grind
  exact eq1378

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_pyy_pxy_pyy_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = X1 := by
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
  have eq73 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq108 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq73 X1 X0
       grind)
    | (have i₁ := eq13 (σ X1) (σ X1)
       have i₂ := eq73 X0 X1
       grind)
    | exact superpose eq73 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq73 X1 X0
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq73 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq73 X0 X0
       grind)
    | exact resolve eq13 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq73 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq118 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq108 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq119 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq118 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq121 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq119 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq119
    | (have j0 := eq119 X0 X1
       grind)
    | exact resolve eq119 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq124 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq121 X0 X1
       have j1 := eq116 X1 X0
       grind)
    | (have r₁ := eq121 X1 X0
       have r₂ := eq116 X0 X1
       grind)
    | (have r₁ := eq121 (k X0 X1) X1
       have r₂ := eq116 X0 X1
       grind)
    | (have r₁ := eq121 X1 X1
       have r₂ := eq116 X1 X1
       grind)
    | exact resolve eq121 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq121
  have eq590 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq124 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq124
    | exact resolve eq124 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq604 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq124 y x
       grind)
    | exact superpose eq124 eq16
    | (have j1 := eq124 y x
       grind)
    | exact resolve eq16 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq625 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq590 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq590
    | (have j0 := eq590 X0 X1
       grind)
    | exact resolve eq590 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq590
  have eq626 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq625 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq625
    | exact resolve eq625 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625
  have eq680 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq626 (τ X1) X0
       grind)
    | exact superpose eq626 eq19
    | (have j1 := eq626 (τ X1) X0
       grind)
    | exact resolve eq19 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq626
  have eq1191 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq680 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq680
    | exact resolve eq680 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680
  have eq1250 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1191 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1191
    | (have j0 := eq1191 X0 X1
       grind)
    | exact resolve eq1191 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1191
  have eq1368 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq604
       have i₂ := eq1250 y x
       grind)
    | exact superpose eq1250 eq604
    | (have j1 := eq1250 (σ y) (σ x)
       grind)
    | (have r₁ := eq604
       have r₂ := eq1250 y x
       grind)
    | exact resolve eq604 eq1250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1369 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1368
  have eq1404 : (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1369
  have eq1497 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq604
       have i₂ := eq1404
       grind)
    | exact superpose eq1404 eq604
    | exact resolve eq604 eq1404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604 eq1404
  have eq1498 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1497
  have eq1499 : (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1498
  have eq1564 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq1499
  have eq1586 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq1564
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq1564
    | exact resolve eq1564 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1564
  have eq1793 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1586
       grind)
    | exact superpose eq1586 eq16
    | exact resolve eq16 eq1586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1586
  have eq1802 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1793
       have i₂ := eq1250 y x
       grind)
    | exact superpose eq1250 eq1793
    | (have j1 := eq1250 y x
       grind)
    | (have r₁ := eq1793
       have r₂ := eq1250 y x
       grind)
    | exact resolve eq1793 eq1250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1250
  have eq1803 : y = (M.op x x) := by grind
  clear eq1802
  have eq1905 : (M.op x y) = (k x y) := by grind
  clear eq1803
  have eq2050 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1793
       have i₂ := eq1905
       grind)
    | exact superpose eq1905 eq1793
    | exact resolve eq1793 eq1905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1793 eq1905
  have eq2053 : False := by grind
  exact eq2053

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,Y) else if m(Y,Y) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_x_pxy_pyy_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq20 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq21 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 (M.op X0 X0)) X2 X0
       have i₂ := eq9 X0 (M.op X1 (M.op X0 X0)) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op X0 X0) X0 x
       have i₂ := eq9 X0 x (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k (τ X0) X1) X2
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq15
    | exact resolve eq15 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq47 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq79 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    grind
  have eq82 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq79 X0
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq79
    | (have j0 := eq79 X0
       grind)
    | exact resolve eq79 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq79
  have eq83 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq82 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq95 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) = (M.op (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21 (M.op X3 X1) X2 (M.op X0 (M.op X1 X1))
       have i₂ := eq21 X1 X0 X3
       grind)
    | exact superpose eq21 eq21
    | exact resolve eq21 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq123 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (M.op X0 (σ X1)) (σ X2)) ∨ (M.op (σ X1) (σ X1)) = X0 ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27 X0 X1 X2
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq27
    | (have j1 := eq14 X0 (σ X1)
       grind)
    | exact resolve eq27 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq217 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq47 x y
       grind)
    | exact superpose eq47 eq16
    | (have j1 := eq47 x y
       grind)
    | exact resolve eq16 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq225 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq83 (σ x)
       have i₂ := eq47 x x
       grind)
    | exact superpose eq47 eq83
    | (have j1 := eq47 X0 X0
       grind)
    | exact resolve eq83 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq232 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq225 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq240 : ∀ X0 : G, (σ (k X0 X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq232 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq232
    | (have j0 := eq232 X0
       grind)
    | exact resolve eq232 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq1426 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2))) x
       have i₂ := eq95 x X2 X0 X1
       grind)
    | exact superpose eq95 eq9
    | exact resolve eq9 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq1461 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X0 x
       have i₂ := eq1426 x X1 X0
       grind)
    | exact superpose eq1426 eq9
    | exact resolve eq9 eq1426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1426
  have eq1504 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq217
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq217
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq217 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1505 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1504
  have eq15920 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k (τ (σ X0)) X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq83 (σ X0)
       have i₂ := eq123 (σ X0) X0 X0
       grind)
    | exact superpose eq123 eq83
    | (have j1 := eq123 (σ X0) X0 x
       grind)
    | exact resolve eq83 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq15930 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k (τ (σ X0)) X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq15920 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15920
  have eq15943 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15930 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15930
    | (have j0 := eq15930 X0
       grind)
    | exact resolve eq15930 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15930
  have eq22464 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq240 X0
       have i₂ := eq15943 X0
       grind)
    | exact superpose eq15943 eq240
    | (have j0 := eq240 X0
       have j1 := eq15943 X0
       grind)
    | exact resolve eq240 eq15943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240 eq15943
  have eq22539 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq22464 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22464
  have eq25300 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  clear eq22539
  have eq25338 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq25300 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq25300
    | (have j0 := eq25300 X0
       grind)
    | exact resolve eq25300 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25300
  have eq25339 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq25338 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25338
  have eq25823 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq25339 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25339
    | exact resolve eq25339 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25896 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ X0) (σ (k X0 X0))) := by
    intro X0
    grind
  have eq25932 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1461 (σ X0) (σ X0)
       have i₂ := eq25339 X0
       grind)
    | exact superpose eq25339 eq1461
    | exact resolve eq1461 eq25339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25968 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq25896 X0
       have i₂ := eq15 X0 (k X0 X0)
       grind)
    | exact superpose eq15 eq25896
    | exact resolve eq25896 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25896
  have eq25999 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq25823 X0
       have i₂ := eq20 X0 (τ X0)
       grind)
    | exact superpose eq20 eq25823
    | exact resolve eq25823 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq25823
  have eq26023 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq25999 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25999
    | exact resolve eq25999 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25999
  have eq28625 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq25932 X0
       have i₂ := eq26023 X0
       grind)
    | exact superpose eq26023 eq25932
    | exact resolve eq25932 eq26023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25932
  have eq30952 : ∀ X0 : G, (σ (k X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq25968 X0
       have i₂ := eq26023 X0
       grind)
    | exact superpose eq26023 eq25968
    | exact resolve eq25968 eq26023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25968
  have eq31061 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  clear eq30952
  have eq32353 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq31061 x
       have i₂ := eq1505
       grind)
    | exact superpose eq1505 eq31061
    | exact resolve eq31061 eq1505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1505
  have eq32400 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq32353
       have r₂ := eq16
       grind)
    | exact resolve eq32353 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32353
  have eq32468 : (σ y) = (σ (k x x)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq32400
       have i₂ := eq25339 x
       grind)
    | exact superpose eq25339 eq32400
    | exact resolve eq32400 eq25339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32400
  have eq32499 : (σ y) = (σ (M.op x x)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq32468
       have i₂ := eq26023 x
       grind)
    | exact superpose eq26023 eq32468
    | exact resolve eq32468 eq26023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32468
  have eq32529 : (σ x) = (σ (k y y)) ∨ (σ y) = (σ (M.op x x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq32499
       have i₂ := eq25339 y
       grind)
    | exact superpose eq25339 eq32499
    | exact resolve eq32499 eq25339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32499
  have eq32551 : x = (M.op y y) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq32529
       have i₂ := eq26023 y
       grind)
    | exact superpose eq26023 eq32529
    | exact resolve eq32529 eq26023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32529
  have eq67610 : x = (k x y) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq83 y
       have i₂ := eq32551
       grind)
    | exact superpose eq32551 eq83
    | exact resolve eq83 eq32551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq67677 : x = (M.op x y) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1461 y y
       have i₂ := eq32551
       grind)
    | exact superpose eq32551 eq1461
    | exact resolve eq1461 eq32551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32551
  have eq70399 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq217
       have i₂ := eq67610
       grind)
    | exact superpose eq67610 eq217
    | exact resolve eq217 eq67610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217 eq67610
  have eq70404 : (σ x) = (σ (k y y)) ∨ (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq70399
       have i₂ := eq25339 y
       grind)
    | exact superpose eq25339 eq70399
    | exact resolve eq70399 eq25339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70399
  have eq70405 : (σ x) = (σ (M.op y y)) ∨ (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq70404
       have i₂ := eq26023 y
       grind)
    | exact superpose eq26023 eq70404
    | exact resolve eq70404 eq26023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70404
  have eq70406 : (σ x) = (σ (M.op y y)) ∨ (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq70405
  have eq70407 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq70406
       have i₂ := eq25339 x
       grind)
    | exact superpose eq25339 eq70406
    | exact resolve eq70406 eq25339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25339 eq70406
  have eq70408 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq70407
       have i₂ := eq26023 x
       grind)
    | exact superpose eq26023 eq70407
    | exact resolve eq70407 eq26023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26023 eq70407
  have eq70409 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq70408
  have eq248773 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq70409
       have i₂ := eq67677
       grind)
    | exact superpose eq67677 eq70409
    | exact resolve eq70409 eq67677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67677 eq70409
  have eq248774 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq248773
  have eq248775 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq248774
  have eq250708 : (M.op x x) = (τ (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq248775
       grind)
    | exact superpose eq248775 eq10
    | exact resolve eq10 eq248775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248775
  have eq250988 : y = (M.op x x) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq250708
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq250708
    | exact resolve eq250708 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250708
  have eq251270 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq31061 x
       have i₂ := eq250988
       grind)
    | exact superpose eq250988 eq31061
    | exact resolve eq31061 eq250988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31061 eq250988
  have eq251352 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq251270
       have r₂ := eq16
       grind)
    | exact resolve eq251270 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251270
  have eq253321 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq28625 y
       have i₂ := eq251352
       grind)
    | exact superpose eq251352 eq28625
    | exact resolve eq28625 eq251352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28625
  have eq253342 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq251352
       grind)
    | exact superpose eq251352 eq10
    | exact resolve eq10 eq251352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251352
  have eq253622 : x = (M.op y y) := by
    first
    | (have i₁ := eq253342
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq253342
    | exact resolve eq253342 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253342
  have eq254030 : x = (M.op x y) := by
    first
    | (have i₁ := eq1461 y y
       have i₂ := eq253622
       grind)
    | exact superpose eq253622 eq1461
    | exact resolve eq1461 eq253622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1461 eq253622
  have eq257288 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq253321
       grind)
    | exact superpose eq253321 eq16
    | exact resolve eq16 eq253321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253321
  have eq257375 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq257288
       have i₂ := eq254030
       grind)
    | exact superpose eq254030 eq257288
    | exact resolve eq257288 eq254030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254030 eq257288
  have eq257376 : False := by grind
  exact eq257376

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pxy_y_pxy_y_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq45 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq35
    | (have j0 := eq35 (M.op x y)
       grind)
    | exact resolve eq35 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq55 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq72 : y ≠ (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ y = (k x y) := by
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
  have eq73 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
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
  have eq111 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq80 x y
       grind)
    | exact superpose eq80 eq44
    | (have j1 := eq80 x y
       grind)
    | exact resolve eq44 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq55
       have i₂ := eq80 sF2 sF3
       grind)
    | exact superpose eq80 eq55
    | (have j1 := eq80 (σ x) (σ y)
       grind)
    | exact resolve eq55 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq117 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq116
    | exact resolve eq116 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq119 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq111
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq111
    | exact resolve eq111 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq121 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq117
    | exact resolve eq117 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq122 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq119
    | exact resolve eq119 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq123 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq122
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq122
    | exact resolve eq122 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq190 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq123 eq80
    | (have j0 := eq80 (σ x) (σ y)
       grind)
    | exact resolve eq80 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq190
    | exact resolve eq190 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq194 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq191
       have r₂ := eq27
       grind)
    | exact resolve eq191 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq196 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq194
    | exact resolve eq194 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq198 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq196 eq27
    | exact resolve eq27 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq481 : (k (σ x) (σ y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq121
       grind)
    | exact superpose eq121 eq44
    | exact resolve eq44 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq121
  have eq484 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq481
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq481
    | exact resolve eq481 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481
  have eq525 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq196 eq73
    | (have r₁ := eq73
       have r₂ := eq196
       grind)
    | exact resolve eq73 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq196
  have eq526 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq525
  have eq531 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq526 eq123
    | exact resolve eq123 eq526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526
  have eq535 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq531
  have eq542 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq535
       have r₂ := eq198
       grind)
    | exact resolve eq535 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198 eq535
  have eq546 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq542 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542
  have eq549 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq80 (σ x) (σ y)
       grind)
    | (have r₁ := eq546
       have r₂ := eq80 (σ x) (σ y)
       grind)
    | exact resolve eq546 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546
  have eq552 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq549
    | exact resolve eq549 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq549
  have eq578 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq552 eq123
    | exact resolve eq123 eq552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq552
  have eq581 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq578
  have eq585 : y = (M.op x y) := by
    first
    | (have r₁ := eq581
       have r₂ := eq27
       grind)
    | exact resolve eq581 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581
  have eq587 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq585 eq20
    | exact resolve eq20 eq585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq589 : y ≠ y ∨ y = (M.op y x) ∨ y = (k x y) := by
    first
    | exact superpose eq585 eq72
    | (have r₁ := eq72
       have r₂ := eq585
       grind)
    | exact resolve eq72 eq585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq596 : y = (M.op y x) ∨ y = (k x y) := by grind
  clear eq589
  have eq604 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq587
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq587
    | exact resolve eq587 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587
  have eq711 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq604 eq484
    | exact resolve eq484 eq604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484
  have eq717 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have r₁ := eq711
       have r₂ := eq27
       grind)
    | exact resolve eq711 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711
  have eq735 : (k x (M.op x y)) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq717 eq59
    | exact resolve eq59 eq717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq717
  have eq737 : (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq585 eq735
    | exact resolve eq735 eq585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735
  have eq944 : y = (M.op y x) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq596
       have i₂ := eq737
       grind)
    | exact superpose eq737 eq596
    | exact resolve eq596 eq737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596
  have eq947 : y ≠ (M.op x y) ∨ (M.op x y) = (k x y) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq944
       grind)
    | exact superpose eq944 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq944
  have eq950 : (M.op x y) = (k x y) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have j1 := eq80 x y
       grind)
    | (have r₁ := eq947
       have r₂ := eq80 x y
       grind)
    | exact resolve eq947 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq947
  have eq953 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq950
       have i₂ := eq737
       grind)
    | exact superpose eq737 eq950
    | exact resolve eq950 eq737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq737 eq950
  have eq954 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq953
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq953
    | exact resolve eq953 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq953
  have eq955 : y = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq585 eq954
    | exact resolve eq954 eq585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585 eq954
  have eq956 : y = (τ (M.op (σ x) (σ y))) := by grind
  clear eq955
  have eq958 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq956 eq15
    | exact resolve eq15 eq956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq956
  have eq973 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq958
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq958
    | exact resolve eq958 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq958
  have eq980 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq604 eq973
    | exact resolve eq973 eq604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604 eq973
  have eq984 : False := by grind
  exact eq984

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxy_y_pxy_y_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (M.op X1 X1) := by
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
  have eq66 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq66 (σ X0)
       grind)
    | exact superpose eq66 eq15
    | exact resolve eq15 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq70 X0
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq70
    | exact resolve eq70 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq70
  have eq102 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq81 X0
       grind)
    | exact superpose eq81 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq597 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
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
  have eq616 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq597 X0 X1
       have i₂ := eq81 X1
       grind)
    | exact superpose eq81 eq597
    | (have j0 := eq597 X0 X1
       grind)
    | exact resolve eq597 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq597
  have eq2975 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq616 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq616
    | exact resolve eq616 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616
  have eq3078 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2975 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq2975
    | (have j0 := eq2975 X0 X1
       grind)
    | exact resolve eq2975 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq2975
  have eq3082 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3078 X0 X1
       have j1 := eq102 X1 X0
       grind)
    | (have r₁ := eq3078 X1 X0
       have r₂ := eq102 X0 X1
       grind)
    | exact resolve eq3078 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq3078
  have eq3084 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3082 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3082
    | exact resolve eq3082 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3082
  have eq3188 : ∀ X0 X1 : G, (M.op (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq3084 X1 (σ X0)
       grind)
    | exact superpose eq3084 eq28
    | (have j1 := eq3084 X1 (σ X0)
       grind)
    | exact resolve eq28 eq3084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq3298 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k (σ X1) X0) = X0 ∨ (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq3188 X0 X1
       grind)
    | exact superpose eq3188 eq13
    | (have j0 := eq13 (σ X1) X0
       have j1 := eq3188 X1 X0
       grind)
    | (have r₁ := eq13 (σ X0) X1
       have r₂ := eq3188 X0 X1
       grind)
    | exact resolve eq13 eq3188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3300 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k (σ X1) X0) = X0 ∨ (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq3188 X0 X1
       grind)
    | exact superpose eq3188 eq12
    | (have j1 := eq3188 X1 X0
       grind)
    | exact resolve eq12 eq3188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3188
  have eq3325 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k (σ X1) X0) = X0 ∨ (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq3298 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3298
  have eq3336 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq3325 X0 X1
       have j1 := eq3300 X0 X1
       grind)
    | (have r₁ := eq3325 X0 X1
       have r₂ := eq3300 X0 X1
       grind)
    | exact resolve eq3325 eq3300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3300 eq3325
  have eq3836 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (k (τ X0) (τ X1)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3336 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3336
    | exact resolve eq3336 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3880 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X1) X0
       have i₂ := eq3336 (σ X0) X1
       grind)
    | exact superpose eq3336 eq22
    | (have j1 := eq3336 (σ X0) X1
       grind)
    | exact resolve eq22 eq3336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq3336
  have eq3925 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3880 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq3880
    | (have j0 := eq3880 X0 X1
       grind)
    | exact resolve eq3880 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3880
  have eq3936 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3836 X0 X1
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq3836
    | (have j0 := eq3836 X0 X1
       grind)
    | exact resolve eq3836 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3836
  have eq3955 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3925 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3925
    | (have j0 := eq3925 X0 X1
       grind)
    | exact resolve eq3925 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3925
  have eq3962 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 X0) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3955 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3955
    | (have j0 := eq3955 X0 X1
       grind)
    | exact resolve eq3955 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3955
  have eq3992 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq3936 X0 X1
       grind)
    | exact superpose eq3936 eq11
    | (have j1 := eq3936 X0 X1
       grind)
    | exact resolve eq11 eq3936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3936
  have eq4101 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3992 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq3992
    | (have j0 := eq3992 X0 X1
       grind)
    | exact resolve eq3992 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3992
  have eq4200 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq4101 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4101
  have eq4266 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3962 X0 X1
       have i₂ := eq3084 X0 X1
       grind)
    | exact superpose eq3084 eq3962
    | (have j1 := eq3084 X1 X0
       grind)
    | exact resolve eq3962 eq3084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4273 : ∀ X0 X1 : G, (τ X1) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X0)) (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq3962 (τ X0) (τ X1)
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq3962
    | exact resolve eq3962 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq3962
  have eq4372 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq4266 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4266
  have eq4451 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op (σ (τ X0)) X1)) ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4273 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq4273
    | (have j0 := eq4273 X0 X1
       grind)
    | exact resolve eq4273 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4273
  have eq4506 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4451 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4451
    | (have j0 := eq4451 X0 X1
       grind)
    | exact resolve eq4451 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4451
  have eq4869 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4200 X1 X0
       have i₂ := eq4372 X1 X0
       grind)
    | exact superpose eq4372 eq4200
    | (have j0 := eq4200 X1 X0
       have j1 := eq4372 X1 X0
       grind)
    | (have r₁ := eq4200 X0 X1
       have r₂ := eq4372 X0 X1
       grind)
    | exact resolve eq4200 eq4372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4200 eq4372
  have eq4927 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (M.op X1 X0) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq4869 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4869
  have eq5071 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ X1) X0) ∨ (M.op X1 (τ X0)) = (τ (M.op (σ X1) (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq4927 (τ X0) X1
       grind)
    | exact superpose eq4927 eq18
    | (have j1 := eq4927 (τ X0) X1
       grind)
    | exact resolve eq18 eq4927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq4927
  have eq5212 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (M.op X1 (τ X0)) = (τ (M.op (σ X1) (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq5071 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5071
    | (have j0 := eq5071 X0 X1
       grind)
    | exact resolve eq5071 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5071
  have eq5272 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (M.op X1 (τ X0)) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5212 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5212
    | (have j0 := eq5212 X0 X1
       grind)
    | exact resolve eq5212 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5212
  have eq5348 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq4506 X0 X1
       grind)
    | exact superpose eq4506 eq11
    | (have j1 := eq4506 X0 X1
       grind)
    | exact resolve eq11 eq4506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4506
  have eq5458 : ∀ X0 X1 : G, (τ X1) = (τ (k X0 X1)) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5348 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq5348
    | (have j0 := eq5348 X0 X1
       grind)
    | exact resolve eq5348 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5348
  have eq5571 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = (τ (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5458 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq5458
    | exact resolve eq5458 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5458
  have eq5720 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5571 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq5571
    | (have j0 := eq5571 X0 X1
       grind)
    | exact resolve eq5571 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5571
  have eq5725 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5720 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq5720
    | (have j0 := eq5720 X0 X1
       grind)
    | exact resolve eq5720 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5720
  have eq5858 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5725 x y
       grind)
    | exact superpose eq5725 eq16
    | (have j1 := eq5725 x y
       grind)
    | exact resolve eq16 eq5725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5725
  have eq5969 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq5858
       have i₂ := eq3084 y x
       grind)
    | exact superpose eq3084 eq5858
    | (have j1 := eq3084 y x
       grind)
    | exact resolve eq5858 eq3084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5858
  have eq5975 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq5969
  have eq5976 : y = (M.op x y) := by grind
  clear eq5975
  have eq6973 : ∀ X0 X1 : G, (M.op (σ X1) X0) = X0 ∨ (M.op (σ X1) X0) = X0 ∨ (M.op X1 (τ X0)) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3084 X0 (σ X1)
       have i₂ := eq5272 X0 X1
       grind)
    | exact superpose eq5272 eq3084
    | (have j0 := eq3084 X0 (σ X1)
       have j1 := eq5272 X0 X1
       grind)
    | exact resolve eq3084 eq5272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3084 eq5272
  have eq7003 : ∀ X0 X1 : G, (M.op (σ X1) X0) = X0 ∨ (M.op X1 (τ X0)) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq6973 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6973
  have eq7476 : (σ (M.op x y)) ≠ (σ y) ∨ (τ (M.op (σ x) (σ y))) = (M.op x (τ (σ y))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7003 (σ y) x
       grind)
    | exact superpose eq7003 eq16
    | (have j1 := eq7003 (σ y) x
       grind)
    | exact resolve eq16 eq7003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7003
  have eq7580 : (σ y) ≠ (σ y) ∨ (τ (M.op (σ x) (σ y))) = (M.op x (τ (σ y))) := by
    first
    | (have i₁ := eq7476
       have i₂ := eq5976
       grind)
    | exact superpose eq5976 eq7476
    | exact resolve eq7476 eq5976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7476
  have eq7581 : (τ (M.op (σ x) (σ y))) = (M.op x (τ (σ y))) := by grind
  clear eq7580
  have eq7628 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq7581
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq7581
    | exact resolve eq7581 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7581
  have eq7657 : y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq7628
       have i₂ := eq5976
       grind)
    | exact superpose eq5976 eq7628
    | exact resolve eq7628 eq5976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7628
  have eq7693 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 (M.op (σ x) (σ y))
       have i₂ := eq7657
       grind)
    | exact superpose eq7657 eq11
    | exact resolve eq11 eq7657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7657
  have eq7767 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7693
       grind)
    | exact superpose eq7693 eq16
    | exact resolve eq16 eq7693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7693
  have eq7783 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq7767
       have i₂ := eq5976
       grind)
    | exact superpose eq5976 eq7767
    | exact resolve eq7767 eq5976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5976 eq7767
  have eq7784 : False := by grind
  exact eq7784

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,Y) else if m(X,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxx_pyy_pxy_pyx_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
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
  have eq50 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X1 (M.op X0 X0)) X2 X0
       have i₂ := eq14 X0 (M.op X1 (M.op X0 X0)) X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq14 (M.op X0 X0) X0 x
       have i₂ := eq14 X0 x (M.op X0 X0)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op X1 (M.op X2 (M.op X0 X0)))
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have r₁ := eq13 X0 (M.op X1 (M.op X2 (M.op X0 X0)))
       have r₂ := eq14 X0 X1 X2
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq63 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq66 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 (M.op X1 X1) X1
       have r₂ := eq13 (M.op X1 X1) (M.op X1 X1)
       grind)
    | (have r₁ := eq11 X0 (M.op X0 X0)
       have r₂ := eq13 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact resolve eq11 eq13
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
  clear eq36
  have eq98 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq16
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
    | (have r₁ := eq107 x
       have r₂ := eq13 x x
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
  have eq112 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq108 y
       grind)
    | exact superpose eq108 eq73
    | exact resolve eq73 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
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
  have eq119 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq98
       have i₂ := eq108 sF3
       grind)
    | exact superpose eq108 eq98
    | exact resolve eq98 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq120 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq119
       have i₂ := eq108 y
       grind)
    | exact superpose eq108 eq119
    | exact resolve eq119 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq131 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq135 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq132
       have i₂ := eq108 sF1
       grind)
    | exact superpose eq108 eq132
    | exact resolve eq132 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq138 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq135
       have i₂ := eq108 sF0
       grind)
    | exact superpose eq108 eq135
    | exact resolve eq135 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq160 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq138 eq16
    | exact resolve eq16 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq200 : (σ (k (k x y) y)) = (k (k (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq40 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq40
    | exact resolve eq40 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq44
  have eq343 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
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
  have eq354 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq343 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq343
    | exact resolve eq343 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343
  have eq356 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq354 X0
       have i₂ := eq108 X0
       grind)
    | exact superpose eq108 eq354
    | exact resolve eq354 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354
  have eq488 : (σ (M.op (k x x) (k x x))) = (M.op (k (σ x) (σ x)) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq117 (k x x)
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq117
    | exact resolve eq117 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq505 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq117 X0
       grind)
    | exact superpose eq117 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq506 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) (M.op X1 (M.op X2 (σ (M.op X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (σ X0) X1 X2
       have i₂ := eq117 X0
       grind)
    | exact superpose eq117 eq14
    | exact resolve eq14 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq513 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (σ (M.op (k x x) (k x x))) := by
    first
    | (have i₁ := eq488
       have i₂ := eq108 sF2
       grind)
    | exact superpose eq108 eq488
    | exact resolve eq488 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488
  have eq516 : (σ (M.op (M.op x x) (M.op x x))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq513
       have i₂ := eq108 x
       grind)
    | exact superpose eq108 eq513
    | exact resolve eq513 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513
  have eq521 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X2 (M.op X3 (M.op X0 X0))) (M.op X2 (M.op X3 (M.op X0 X0))))) = (M.op (M.op X1 (M.op (M.op X2 (M.op X3 (M.op X0 X0))) (M.op X2 (M.op X3 (M.op X0 X0))))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq50 (M.op X2 (M.op X3 (M.op X0 X0))) X1 X0
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq50
    | exact resolve eq50 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq523 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) = (M.op (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq50 (M.op X3 X1) X2 (M.op X0 (M.op X1 X1))
       have i₂ := eq50 X1 X0 X3
       grind)
    | exact superpose eq50 eq50
    | exact resolve eq50 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq525 : ∀ X0 : G, (M.op X0 (M.op y y)) = (M.op (M.op X0 (M.op y y)) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq50 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq50
    | (have j0 := eq50 y X0 x
       grind)
    | exact resolve eq50 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq683 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq356 X0
       grind)
    | exact superpose eq356 eq16
    | exact resolve eq16 eq356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356
  have eq916 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq51 (τ X0)
       have i₂ := eq683 X0
       grind)
    | exact superpose eq683 eq51
    | exact resolve eq51 eq683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq683
  have eq928 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x y) (M.op x y))) = (M.op (M.op X1 (M.op (M.op x y) (M.op x y))) (M.op X0 (M.op y y))) := by
    intro X0 X1
    first
    | exact superpose eq525 eq50
    | exact resolve eq50 eq525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq525
  have eq2184 : (k (k (σ x) (σ y)) (σ y)) = (σ (k (M.op x y) y)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq200
       have i₂ := eq66 x y
       grind)
    | exact superpose eq66 eq200
    | (have j1 := eq66 x y
       grind)
    | exact resolve eq200 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq2200 : (σ (k (M.op x y) y)) = (k (k (σ x) (σ y)) (σ y)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq2184
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2184
    | exact resolve eq2184 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2184
  have eq2201 : (k (σ (M.op x y)) (σ y)) = (k (k (σ x) (σ y)) (σ y)) ∨ (M.op x x) = (M.op y y) := by
    first
    | exact superpose eq131 eq2200
    | exact resolve eq2200 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2200
  have eq6117 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2))) x
       have i₂ := eq523 x X2 X0 X1
       grind)
    | exact superpose eq523 eq14
    | exact resolve eq14 eq523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8232 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X4 (M.op X0 (M.op (M.op X1 (M.op X2 (M.op (M.op X3 X3) (M.op X3 X3)))) (M.op X1 (M.op X2 (M.op (M.op X3 X3) (M.op X3 X3)))))))) = X3 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 X3 X4 (M.op X0 (M.op (M.op X1 (M.op X2 (M.op (M.op X3 X3) (M.op X3 X3)))) (M.op X1 (M.op X2 (M.op (M.op X3 X3) (M.op X3 X3))))))
       have i₂ := eq521 (M.op X3 X3) X0 X1 X2
       grind)
    | exact superpose eq521 eq14
    | exact resolve eq14 eq521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521
  have eq12127 : ∀ X0 : G, y = (M.op y (M.op X0 (M.op (M.op x y) (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq6117 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6117
    | (have j0 := eq6117 X0 x y
       grind)
    | exact resolve eq6117 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12143 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq64 (M.op X1 X0) X0 x
       have i₂ := eq6117 x X1 X0
       grind)
    | exact superpose eq6117 eq64
    | exact resolve eq64 eq6117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12187 : (M.op x y) = (k (M.op x y) y) := by
    first
    | exact superpose eq12127 eq64
    | exact resolve eq64 eq12127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12193 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (k (M.op (M.op x y) (M.op x y)) (M.op X0 y)) := by
    intro X0
    first
    | exact superpose eq12127 eq64
    | exact resolve eq64 eq12127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq12194 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) (M.op X0 y)) := by
    intro X0
    first
    | exact superpose eq12127 eq14
    | exact resolve eq14 eq12127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12127
  have eq12206 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq12187 eq131
    | exact resolve eq131 eq12187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq12187
  have eq12226 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq20 eq12206
    | exact resolve eq12206 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12206
  have eq12514 : (M.op (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq12226
       have i₂ := eq66 sF1 sF3
       grind)
    | exact superpose eq66 eq12226
    | (have j1 := eq66 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq12226 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13270 : (M.op y y) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq12514 eq120
    | exact resolve eq120 eq12514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13318 : (M.op y y) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq160 eq13270
    | exact resolve eq13270 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13270
  have eq22253 : ∀ X0 X1 : G, (M.op y y) = (M.op (M.op y y) (M.op X1 (M.op X0 (M.op (M.op x y) (M.op x y))))) := by
    intro X0 X1
    first
    | exact superpose eq928 eq14
    | exact resolve eq14 eq928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq928
  have eq79334 : (σ (M.op x y)) = (k (k (σ x) (σ y)) (σ y)) ∨ (M.op x x) = (M.op y y) := by
    first
    | exact superpose eq12226 eq2201
    | exact resolve eq2201 eq12226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2201 eq12226
  have eq79335 : (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq79334
       have i₂ := eq66 sF2 sF3
       grind)
    | exact superpose eq66 eq79334
    | (have j1 := eq66 x y
       grind)
    | exact resolve eq79334 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq79334
  have eq79342 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq79335
       have i₂ := eq12143 sF3 sF2
       grind)
    | exact superpose eq12143 eq79335
    | exact resolve eq79335 eq12143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12143 eq79335
  have eq79343 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq79342
    | exact resolve eq79342 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79342
  have eq79344 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have r₁ := eq79343
       have r₂ := eq27
       grind)
    | exact resolve eq79343 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79343
  have eq79672 : (M.op y y) = (τ (M.op (σ x) (σ x))) ∨ (M.op x x) = (M.op y y) := by
    first
    | exact superpose eq79344 eq120
    | exact resolve eq120 eq79344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq79344
  have eq79760 : (M.op x x) = (M.op y y) ∨ (M.op x x) = (M.op y y) := by
    first
    | exact superpose eq114 eq79672
    | exact resolve eq79672 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79672
  have eq79761 : (M.op x x) = (M.op y y) := by grind
  clear eq79760
  have eq79770 : (M.op (σ y) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq115
       have i₂ := eq79761
       grind)
    | exact superpose eq79761 eq115
    | exact resolve eq115 eq79761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79810 : ∀ X0 X1 : G, (M.op x x) = (M.op (M.op x x) (M.op X0 (M.op X1 (M.op (M.op x y) (M.op x y))))) := by
    intro X0 X1
    first
    | (have i₁ := eq22253 X0 X1
       have i₂ := eq79761
       grind)
    | exact superpose eq79761 eq22253
    | exact resolve eq22253 eq79761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79820 : (M.op (M.op x y) (M.op x y)) = (k (M.op (M.op x y) (M.op x y)) (M.op x x)) := by
    first
    | (have i₁ := eq12193 y
       have i₂ := eq79761
       grind)
    | exact superpose eq79761 eq12193
    | exact resolve eq12193 eq79761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12193
  have eq79821 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) (M.op x x)) := by
    first
    | (have i₁ := eq12194 y
       have i₂ := eq79761
       grind)
    | exact superpose eq79761 eq12194
    | exact resolve eq12194 eq79761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12194
  have eq79830 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ y = (M.op y X0) ∨ (k y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq12 y X0
       have i₂ := eq79761
       grind)
    | exact superpose eq79761 eq12
    | (have j0 := eq12 y X0
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq79761
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq79761
       grind)
    | exact resolve eq12 eq79761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79832 : ∀ X0 X1 : G, y = (M.op y (M.op X0 (M.op X1 (M.op x x)))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 y X0 X1
       have i₂ := eq79761
       grind)
    | exact superpose eq79761 eq14
    | exact resolve eq14 eq79761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79840 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (M.op X0 (M.op X1 (σ (M.op x x))))) := by
    intro X0 X1
    first
    | (have i₁ := eq506 y X0 X1
       have i₂ := eq79761
       grind)
    | exact superpose eq79761 eq506
    | exact resolve eq506 eq79761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79871 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (M.op X0 (M.op X1 (M.op (σ x) (σ x))))) := by
    intro X0 X1
    first
    | (have i₁ := eq79840 X0 X1
       have i₂ := eq116
       grind)
    | exact superpose eq116 eq79840
    | exact resolve eq79840 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79840
  have eq79896 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq79770
       have i₂ := eq116
       grind)
    | exact superpose eq116 eq79770
    | exact resolve eq79770 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79770
  have eq79903 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (M.op X0 (M.op X1 (M.op (σ x) (σ x))))) := by
    intro X0 X1
    first
    | (have i₁ := eq79871 X0 X1
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq79871
    | (have j0 := eq79871 X0 X1
       grind)
    | exact resolve eq79871 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79871
  have eq79914 : (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq12514 eq79896
    | exact resolve eq79896 eq12514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12514
  have eq81147 : (M.op y y) = (k (M.op y y) (M.op x x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq13318 eq79820
    | exact resolve eq79820 eq13318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13318 eq79820
  have eq81154 : (M.op x x) = (k (M.op x x) (M.op x x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq81147
       have i₂ := eq79761
       grind)
    | exact superpose eq79761 eq81147
    | exact resolve eq81147 eq79761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81147
  have eq81157 : (M.op x x) = (M.op (M.op x x) (M.op x x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq81154
       have i₂ := eq108 (M.op x x)
       grind)
    | exact superpose eq108 eq81154
    | exact resolve eq81154 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq81154
  have eq81170 : ∀ X0 : G, x = (M.op x (M.op X0 (M.op (M.op x y) (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq79821 eq14
    | exact resolve eq14 eq79821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79821
  have eq83804 : ∀ X0 X1 : G, y = (M.op y (M.op X0 (M.op (M.op X1 x) (M.op X1 x)))) := by
    intro X0 X1
    first
    | (have i₁ := eq79832 (M.op X0 (M.op (M.op X1 x) (M.op X1 x))) x
       have i₂ := eq523 x x X0 X1
       grind)
    | exact superpose eq523 eq79832
    | exact resolve eq79832 eq523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83859 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (M.op X0 (M.op (M.op X1 (σ x)) (M.op X1 (σ x))))) := by
    intro X0 X1
    first
    | (have i₁ := eq79903 (M.op x (M.op (M.op x sF2) (M.op x sF2))) X0
       have i₂ := eq523 X0 sF2 x x
       grind)
    | exact superpose eq523 eq79903
    | exact resolve eq79903 eq523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79903
  have eq86187 : (M.op x x) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq79914 eq114
    | exact resolve eq114 eq79914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq79914
  have eq86266 : (M.op x x) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq160 eq86187
    | exact resolve eq86187 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160 eq86187
  have eq89235 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op X0 (M.op X1 (σ (M.op x x))))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq86266 eq506
    | exact resolve eq506 eq86266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506 eq86266
  have eq89281 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op X0 (M.op X1 (M.op (σ x) (σ x))))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq89235 X0 X1
       have i₂ := eq116
       grind)
    | exact superpose eq116 eq89235
    | exact resolve eq89235 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89235
  have eq89329 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op X0 (M.op X1 (M.op (σ x) (σ x))))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq20 eq89281
    | (have j0 := eq89281 X0 X1
       grind)
    | exact resolve eq89281 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89281
  have eq114673 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op X0 x) y) := by
    intro X0
    first
    | (have i₁ := eq14 (M.op X0 x) y x
       have i₂ := eq83804 x X0
       grind)
    | exact superpose eq83804 eq14
    | exact resolve eq14 eq83804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83804
  have eq116307 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op (M.op X0 (σ x)) (σ y)) := by
    intro X0
    first
    | exact superpose eq83859 eq14
    | exact resolve eq14 eq83859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186874 : ∀ X0 X1 : G, (M.op x x) = (M.op (M.op x x) (M.op X0 (M.op (M.op X1 (M.op x y)) (M.op X1 (M.op x y))))) := by
    intro X0 X1
    first
    | (have i₁ := eq79810 (M.op x (M.op (M.op x sF0) (M.op x sF0))) X0
       have i₂ := eq523 X0 sF0 x x
       grind)
    | exact superpose eq523 eq79810
    | exact resolve eq79810 eq523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79810
  have eq194325 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) X0) ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq505 y X0
       have i₂ := eq115
       grind)
    | exact superpose eq115 eq505
    | (have j0 := eq505 y X0
       grind)
    | (have r₁ := eq505 y (σ y)
       have r₂ := eq115
       grind)
    | exact resolve eq505 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq505
  have eq194328 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) X0) ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq79896 eq194325
    | (have j0 := eq194325 X0
       grind)
    | (have r₁ := eq194325 (σ x)
       have r₂ := eq79896
       grind)
    | exact resolve eq194325 eq79896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194325
  have eq194353 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) ∨ (M.op X0 X0) ≠ (M.op (σ x) (σ x)) ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq194328 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq194328
    | (have j0 := eq194328 X0
       grind)
    | exact resolve eq194328 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194328
  have eq194376 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) X0) ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq194353 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq194353
    | (have j0 := eq194353 X0
       grind)
    | exact resolve eq194353 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq194353
  have eq280267 : (σ (M.op x x)) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq516
       have i₂ := eq81157
       grind)
    | exact superpose eq81157 eq516
    | exact resolve eq516 eq81157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516 eq81157
  have eq280383 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq280267
       have i₂ := eq116
       grind)
    | exact superpose eq116 eq280267
    | exact resolve eq280267 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq280267
  have eq309386 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (M.op (σ x) (σ x)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq280383 eq83859
    | exact resolve eq83859 eq280383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83859 eq280383
  have eq311001 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2⟩ := hcon
    have f311001_14 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op X0 (M.op X1 (M.op (σ x) (σ x))))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
      intro X0 X1
      grind
    have f311001_15 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (M.op (σ x) (σ x)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
      intro X0
      grind
    have f311001_26 : (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ y)) := by grind
    have f311001_28 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (M.op (σ x) (σ x)))) := by
      intro X0
      first
      | (have j0 := f311001_15 X0
         grind)
      | (have r₁ := f311001_15 X0
         have r₂ := f311001_26
         grind)
      | exact resolve f311001_15 f311001_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f311001_29 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op X0 (M.op X1 (M.op (σ x) (σ x))))) := by
      intro X0 X1
      first
      | (have j0 := f311001_14 X0 X1
         grind)
      | (have r₁ := f311001_14 X0 X1
         have r₂ := f311001_26
         grind)
      | exact resolve f311001_14 f311001_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f311001_110 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
      first
      | (have i₁ := f311001_29 (σ y) x
         have i₂ := f311001_28 x
         grind)
      | exact superpose f311001_28 f311001_29
      | exact resolve f311001_29 f311001_28
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f311001_118 : False := by
      first
      | (have r₁ := f311001_110
         have r₂ := f311001_26
         grind)
      | exact resolve f311001_110 f311001_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f311001_118
  clear eq89329 eq309386
  have eq311038 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq311001
  have eq445111 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op x y) (M.op X0 (M.op X1 (M.op (M.op y y) (M.op y y))))) := by
    intro X0 X1
    first
    | exact superpose eq22253 eq8232
    | exact resolve eq8232 eq22253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22253
  have eq445246 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op x y) (M.op X0 (M.op X1 (M.op (M.op x x) (M.op x x))))) := by
    intro X0 X1
    first
    | (have i₁ := eq445111 X0 X1
       have i₂ := eq79761
       grind)
    | exact superpose eq79761 eq445111
    | exact resolve eq445111 eq79761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445111
  have eq445434 : ∀ X0 X1 X2 : G, (M.op x y) = (M.op (M.op x y) (M.op X2 (M.op X0 (M.op (M.op X1 x) (M.op X1 x))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq445246 X2 (M.op X0 (M.op (M.op X1 x) (M.op X1 x)))
       have i₂ := eq523 (M.op x x) x X0 X1
       grind)
    | exact superpose eq523 eq445246
    | exact resolve eq445246 eq523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445246
  have eq445685 : ∀ X0 X1 X2 : G, (M.op x y) = (M.op (M.op x y) (M.op X0 (M.op (M.op X1 (M.op X2 x)) (M.op X1 (M.op X2 x))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq445434 x X2 (M.op X0 (M.op (M.op X1 (M.op X2 x)) (M.op X1 (M.op X2 x))))
       have i₂ := eq523 x (M.op X2 x) X0 X1
       grind)
    | exact superpose eq523 eq445434
    | exact resolve eq445434 eq523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523 eq445434
  have eq496241 : ∀ X0 X1 : G, (M.op X0 (M.op X1 x)) = (M.op (M.op X0 (M.op X1 x)) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq445685 eq14
    | exact resolve eq14 eq445685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445685
  have eq497947 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op (M.op X0 (M.op x y)) (M.op x x)) := by
    intro X0
    first
    | exact superpose eq186874 eq14
    | exact resolve eq14 eq186874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186874
  have eq498039 : ∀ X0 X1 : G, (M.op X0 (M.op X1 x)) = (M.op (M.op X0 (M.op X1 x)) (M.op x x)) := by
    intro X0 X1
    first
    | exact superpose eq496241 eq497947
    | exact resolve eq497947 eq496241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496241
  have eq498064 : ∀ X0 X1 : G, y = (M.op y (M.op X1 (M.op X0 (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq497947 eq79832
    | exact resolve eq79832 eq497947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79832 eq497947
  have eq499603 : ∀ X0 X1 X2 : G, (M.op x y) = (M.op (M.op x y) (M.op X0 (M.op X1 (M.op (M.op X2 y) (M.op X2 y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq498064 eq8232
    | exact resolve eq8232 eq498064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498064
  have eq514987 : ∀ X0 X1 X2 : G, (M.op X0 y) = (M.op (M.op X0 y) (M.op X1 (M.op X2 (M.op (M.op x y) (M.op x y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq499603 eq8232
    | exact resolve eq8232 eq499603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8232 eq499603
  have eq516721 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op X0 y) x) := by
    intro X0
    first
    | exact superpose eq81170 eq514987
    | exact resolve eq514987 eq81170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81170 eq514987
  have eq516838 : ∀ X0 X1 : G, (M.op X1 (M.op X0 y)) = (M.op (M.op X1 (M.op X0 y)) (M.op x x)) := by
    intro X0 X1
    first
    | (have i₁ := eq498039 X0 (M.op X0 y)
       have i₂ := eq516721 X0
       grind)
    | exact superpose eq516721 eq498039
    | exact resolve eq498039 eq516721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498039 eq516721
  have eq831745 : (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have j0 := eq194376 (σ x)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194376
  have eq831755 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq831745
    | exact resolve eq831745 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831745
  have eq4183506 : y = (M.op y x) ∨ (M.op x y) = (k y x) := by
    first
    | (have j0 := eq79830 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79830
  have eq4183516 : (M.op x y) = (k y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq4183506
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4183506
    | exact resolve eq4183506 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4183506
  have eq4183530 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq72
       have i₂ := eq4183516
       grind)
    | exact superpose eq4183516 eq72
    | exact resolve eq72 eq4183516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq4183516
  have eq4183739 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq4183530
    | exact resolve eq4183530 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4183530
  have eq4183803 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq4183739 eq831755
    | exact resolve eq831755 eq4183739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831755 eq4183739
  have eq4183964 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq4183803
       have r₂ := eq27
       grind)
    | exact resolve eq4183803 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4183803
  have eq4184027 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq4183964 eq116307
    | exact resolve eq116307 eq4183964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116307 eq4183964
  have eq4184174 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq79896 eq4184027
    | exact resolve eq4184027 eq79896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79896 eq4184027
  have eq4191197 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ x))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq4184174 eq916
    | exact resolve eq916 eq4184174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq916 eq4184174
  have eq4191368 : (τ (σ y)) = (M.op (τ (σ y)) x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq28 eq4191197
    | exact resolve eq4191197 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq4191197
  have eq4191481 : y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq4191368
    | exact resolve eq4191368 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq4191368
  have eq4191482 : y = (M.op y x) := by grind
  clear eq4191481
  have eq4191532 : y = (M.op y y) := by
    first
    | (have i₁ := eq114673 y
       have i₂ := eq4191482
       grind)
    | exact superpose eq4191482 eq114673
    | exact resolve eq114673 eq4191482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114673 eq4191482
  have eq4191668 : y = (M.op x x) := by
    first
    | (have i₁ := eq4191532
       have i₂ := eq79761
       grind)
    | exact superpose eq79761 eq4191532
    | exact resolve eq4191532 eq79761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4191532
  have eq4192852 : ∀ X0 : G, x = (M.op x (M.op X0 (M.op y y))) := by
    intro X0
    first
    | (have i₁ := eq6117 X0 x x
       have i₂ := eq4191668
       grind)
    | exact superpose eq4191668 eq6117
    | exact resolve eq6117 eq4191668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6117
  have eq4192868 : ∀ X0 : G, x = (M.op x (M.op X0 (M.op x x))) := by
    intro X0
    first
    | (have i₁ := eq4192852 X0
       have i₂ := eq79761
       grind)
    | exact superpose eq79761 eq4192852
    | exact resolve eq4192852 eq79761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79761 eq4192852
  have eq4193338 : ∀ X0 : G, x = (M.op x (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq4192868 X0
       have i₂ := eq4191668
       grind)
    | exact superpose eq4191668 eq4192868
    | exact resolve eq4192868 eq4191668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4192868
  have eq4195409 : x = (M.op x (M.op x x)) := by
    first
    | (have i₁ := eq516838 x x
       have i₂ := eq4193338 x
       grind)
    | exact superpose eq4193338 eq516838
    | exact resolve eq516838 eq4193338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516838 eq4193338
  have eq4195610 : x = (M.op x y) := by
    first
    | (have i₁ := eq4195409
       have i₂ := eq4191668
       grind)
    | exact superpose eq4191668 eq4195409
    | exact resolve eq4195409 eq4191668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4191668 eq4195409
  have eq4195662 : x = (M.op x y) := by
    first
    | (have i₁ := eq4195610
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4195610
    | exact resolve eq4195610 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq4195610
  have eq4195712 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq4195662 eq20
    | exact resolve eq20 eq4195662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq4195662
  have eq4198380 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq4195712
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4195712
    | exact resolve eq4195712 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq4195712
  have eq4204626 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq4198380 eq26
    | exact resolve eq26 eq4198380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq4198380
  have eq4206391 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq311038 eq4204626
    | exact resolve eq4204626 eq311038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311038 eq4204626
  have eq4206830 : False := by grind
  exact eq4206830

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxy_pyx_pxy_pyx_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 := by
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
  have eq73 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq226 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq73 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq73 X0 X1
       grind)
    | exact superpose eq73 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq73 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq73 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq73 X0 X1
       grind)
    | exact resolve eq13 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq232 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq226 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq233 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq232 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq238 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq233 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq233 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq233 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq248 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq238 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq238
    | (have j0 := eq238 X0 X1
       grind)
    | exact resolve eq238 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238
  have eq249 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq248 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248
  have eq254 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq249 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq249
    | exact resolve eq249 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq249 x y
       grind)
    | exact superpose eq249 eq16
    | exact resolve eq16 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq351 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq254 X0 (τ X1)
       grind)
    | exact superpose eq254 eq18
    | exact resolve eq18 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq254
  have eq366 : ∀ X0 X1 : G, (M.op X0 X1) = (k (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq351 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq351
    | exact resolve eq351 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351
  have eq375 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq366 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq366
    | exact resolve eq366 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366
  have eq396 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq266
       have i₂ := eq375 x y
       grind)
    | exact superpose eq375 eq266
    | exact resolve eq266 eq375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266 eq375
  have eq397 : False := by grind
  exact eq397
