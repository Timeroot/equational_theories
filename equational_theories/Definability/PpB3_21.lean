import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if m(X,X) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_x_pyy_pxx_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X0 := by
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
  have eq33 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq36 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    grind
  have eq64 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq70 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq64 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq64
    | exact resolve eq64 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op X0 X0) X1) X0) X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 X1 (M.op X0 X0) X0 X2
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq64
    | exact resolve eq64 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq9
    | exact resolve eq9 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq89 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq76 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq76
    | exact resolve eq76 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq451 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X0) (σ X0)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq461 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 ∨ (M.op (τ X0) (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X1 X1
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq477 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq451 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq451
    | (have j0 := eq451 X1 X1
       have j1 := eq14 (σ X1) (σ X1)
       grind)
    | exact resolve eq451 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq478 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  have eq501 : ∀ X0 X1 X2 : G, (σ (k (k X1 X0) X2)) = (k (M.op (σ X0) (σ X1)) (σ X2)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k X1 X0) X2
       have i₂ := eq451 X1 X0
       grind)
    | exact superpose eq451 eq15
    | (have j1 := eq451 X1 X1
       grind)
    | exact resolve eq15 eq451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq643 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq74 X0 (M.op X0 X1) X2
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq74
    | exact resolve eq74 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq2045 : ∀ X0 : G, (k (σ (τ X0)) X0) = (k (k (σ (τ X0)) X0) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq25 X0
       have i₂ := eq461 X0 (τ X0)
       grind)
    | exact superpose eq461 eq25
    | (have j1 := eq461 X0 (τ X0)
       grind)
    | exact resolve eq25 eq461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq461
  have eq2052 : ∀ X0 : G, (k (σ (τ X0)) X0) = (k (k (σ (τ X0)) X0) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq2045 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2045
  have eq2054 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq2052 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2052
    | (have j0 := eq2052 X0
       grind)
    | exact resolve eq2052 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2052
  have eq2073 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (k (τ X0) (τ X0))
       have i₂ := eq2054 (τ X0)
       grind)
    | exact superpose eq2054 eq19
    | (have j1 := eq2054 (τ X0)
       grind)
    | exact resolve eq19 eq2054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2054
  have eq2079 : ∀ X0 : G, (k X0 (σ (τ X0))) = (k (k X0 (σ (τ X0))) X0) ∨ (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2073 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq2073
    | (have j0 := eq2073 X0
       grind)
    | exact resolve eq2073 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2073
  have eq2095 : ∀ X0 : G, (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq2079 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2079
    | (have j0 := eq2079 X0
       grind)
    | exact resolve eq2079 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2079
  have eq6365 : ∀ X0 X1 : G, (M.op (M.op (M.op (τ (τ X0)) X1) (τ (τ X0))) X1) = X1 ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq76 (τ (τ X0)) X1
       have i₂ := eq2095 X0
       grind)
    | exact superpose eq2095 eq76
    | (have j1 := eq2095 X0
       grind)
    | exact resolve eq76 eq2095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6415 : ∀ X0 X1 : G, (τ (τ X0)) = (M.op (M.op (τ (τ X0)) (M.op (τ (τ X0)) X1)) (τ (τ X0))) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq643 (τ (τ X0)) (τ (τ X0)) x
       have i₂ := eq2095 X0
       grind)
    | exact superpose eq2095 eq643
    | (have j1 := eq2095 X0
       grind)
    | exact resolve eq643 eq2095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2095
  have eq6435 : ∀ X0 X1 : G, (τ (τ X0)) = (M.op (M.op (τ (τ X0)) X1) (τ (τ X0))) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq6415 X0 X1
       have i₂ := eq89 (τ (τ X0)) X1
       grind)
    | exact superpose eq89 eq6415
    | (have j0 := eq6415 X0 X1
       grind)
    | exact resolve eq6415 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6415
  have eq11395 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op (τ (τ X0)) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq6435 eq6365
    | (have j0 := eq6365 X0 X1
       have j1 := eq6435 X0 X1
       grind)
    | exact resolve eq6365 eq6435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6365
  have eq11556 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ (τ X0)) = (M.op X1 (τ (τ X0))) := by
    intro X0 X1
    first
    | exact superpose eq11395 eq6435
    | (have j0 := eq6435 X0 X1
       have j1 := eq11395 X0 X1
       grind)
    | exact resolve eq6435 eq11395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6435 eq11395
  have eq12885 : ∀ X0 X1 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (τ (τ (σ X0))) = (M.op X1 (τ (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (k (σ X0) (σ X0)) X0
       have i₂ := eq11556 (σ X0) X1
       grind)
    | exact superpose eq11556 eq23
    | (have j1 := eq11556 (σ X0) X1
       grind)
    | exact resolve eq23 eq11556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11556
  have eq12933 : ∀ X0 X1 : G, (k (τ (σ X0)) X0) = (k (k (τ (σ X0)) X0) X0) ∨ (τ (τ (σ X0))) = (M.op X1 (τ (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq12885 X1 X1
       have i₂ := eq23 (σ X1) X1
       grind)
    | exact superpose eq23 eq12885
    | (have j0 := eq12885 X0 X1
       grind)
    | exact resolve eq12885 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12885
  have eq12973 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ (τ (σ X0))) = (M.op X1 (τ (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq12933 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq12933
    | (have j0 := eq12933 X0 X1
       grind)
    | exact resolve eq12933 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12933
  have eq13009 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ X0) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12973 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq12973
    | (have j0 := eq12973 X0 X1
       grind)
    | exact resolve eq12973 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12973
  have eq13083 : ∀ X0 X1 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (τ (σ X0)) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (k (σ X0) (σ X0)) X0
       have i₂ := eq13009 (σ X0) X1
       grind)
    | exact superpose eq13009 eq23
    | (have j1 := eq13009 (σ X0) X1
       grind)
    | exact resolve eq23 eq13009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13009
  have eq13131 : ∀ X0 X1 : G, (k (τ (σ X0)) X0) = (k (k (τ (σ X0)) X0) X0) ∨ (τ (σ X0)) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq13083 X1 X1
       have i₂ := eq23 (σ X1) X1
       grind)
    | exact superpose eq23 eq13083
    | (have j0 := eq13083 X0 X1
       grind)
    | exact resolve eq13083 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13083
  have eq13171 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ (σ X0)) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq13131 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13131
    | (have j0 := eq13131 X0 X1
       grind)
    | exact resolve eq13131 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13131
  have eq13207 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13171 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13171
    | (have j0 := eq13171 X0 X1
       grind)
    | exact resolve eq13171 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13171
  have eq13281 : ∀ X0 X1 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (k (σ X0) (σ X0)) X0
       have i₂ := eq13207 (σ X0) X1
       grind)
    | exact superpose eq13207 eq23
    | (have j1 := eq13207 (σ X0) X1
       grind)
    | exact resolve eq23 eq13207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13207
  have eq13329 : ∀ X0 X1 : G, (k (τ (σ X0)) X0) = (k (k (τ (σ X0)) X0) X0) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13281 X1 X1
       have i₂ := eq23 (σ X1) X1
       grind)
    | exact superpose eq23 eq13281
    | (have j0 := eq13281 X0 X1
       grind)
    | exact resolve eq13281 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq13281
  have eq13369 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13329 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13329
    | (have j0 := eq13329 X0 X1
       grind)
    | exact resolve eq13329 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13329
  have eq19513 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  clear eq501
  have eq19529 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq19513 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19513
  have eq19544 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq13369 eq19529
    | (have j0 := eq19529 X0
       have j1 := eq13369 X0 (σ X0)
       grind)
    | exact resolve eq19529 eq13369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13369 eq19529
  have eq19587 : ∀ X0 : G, (M.op (σ (τ X0)) (σ (τ X0))) = (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq19544 (τ X0)
       grind)
    | exact superpose eq19544 eq19
    | (have j1 := eq19544 (τ X0)
       grind)
    | exact resolve eq19 eq19544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq19544
  have eq19663 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq19587 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq19587
    | (have j0 := eq19587 X0
       grind)
    | exact resolve eq19587 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19587
  have eq19680 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq19663 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq19663
    | (have j0 := eq19663 X0
       grind)
    | exact resolve eq19663 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19663
  have eq19697 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq19680 (τ X0)
       have i₂ := eq33 X0 X0
       grind)
    | exact superpose eq33 eq19680
    | (have j0 := eq19680 (τ X0)
       grind)
    | exact resolve eq19680 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq19680
  have eq20033 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq19697 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19697
  have eq20071 : ∀ X0 : G, (τ (σ X0)) ≠ (k X0 (τ (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq20033 (σ X0)
       have i₂ := eq30 X0 (σ X0)
       grind)
    | exact superpose eq30 eq20033
    | (have j0 := eq20033 (σ X0)
       grind)
    | exact resolve eq20033 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq20033
  have eq20089 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq20071 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq20071
    | (have j0 := eq20071 X0
       grind)
    | exact resolve eq20071 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20071
  have eq20108 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq20089 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq20089
    | (have j0 := eq20089 X0
       grind)
    | exact resolve eq20089 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20089
  have eq24368 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq477 x y
       grind)
    | exact superpose eq477 eq16
    | (have j1 := eq477 y y
       grind)
    | (have r₁ := eq16
       have r₂ := eq477 x y
       grind)
    | exact resolve eq16 eq477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477
  have eq24519 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq24368
  have eq54938 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq24519
       grind)
    | exact superpose eq24519 eq36
    | exact resolve eq36 eq24519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24519
  have eq55138 : y = (k y y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq54938
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq54938
    | exact resolve eq54938 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54938
  have eq55151 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq20108 y
       grind)
    | (have r₁ := eq55138
       have r₂ := eq20108 y
       grind)
    | exact resolve eq55138 eq20108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20108 eq55138
  have eq55154 : (τ (σ y)) = (k (τ (σ y)) x) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq55151
       grind)
    | exact superpose eq55151 eq36
    | exact resolve eq36 eq55151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55241 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq89 (σ x) (σ x)
       have i₂ := eq55151
       grind)
    | exact superpose eq55151 eq89
    | exact resolve eq89 eq55151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55151
  have eq55345 : y = (k y x) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq55154
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq55154
    | exact resolve eq55154 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55154
  have eq55355 : y = (M.op x y) ∨ y = (M.op y y) ∨ y = (M.op x x) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq55345
       grind)
    | exact superpose eq55345 eq14
    | (have j0 := eq14 y y
       grind)
    | exact resolve eq14 eq55345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55345
  have eq55356 : y = (M.op y y) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq55355
  have eq56645 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq55241
       grind)
    | exact superpose eq55241 eq16
    | exact resolve eq16 eq55241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55241
  have eq56770 : (σ y) ≠ (σ y) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq55356 eq56645
    | exact resolve eq56645 eq55356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55356 eq56645
  have eq56771 : y = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq56770
  have eq56796 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq76 y X0
       have i₂ := eq56771
       grind)
    | exact superpose eq56771 eq76
    | exact resolve eq76 eq56771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56801 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq478 y
       have i₂ := eq56771
       grind)
    | exact superpose eq56771 eq478
    | exact resolve eq478 eq56771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56881 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq643 y y x
       have i₂ := eq56771
       grind)
    | exact superpose eq56771 eq643
    | exact resolve eq643 eq56771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56771
  have eq56936 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq56801
  have eq56955 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq56881 X0
       have i₂ := eq89 y X0
       grind)
    | exact superpose eq89 eq56881
    | exact resolve eq56881 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56881
  have eq57293 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq76 (σ y) X0
       have i₂ := eq56936
       grind)
    | exact superpose eq56936 eq76
    | exact resolve eq76 eq56936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57378 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (M.op (σ y) X0)) (σ y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq643 (σ y) (σ y) x
       have i₂ := eq56936
       grind)
    | exact superpose eq56936 eq643
    | exact resolve eq643 eq56936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56936
  have eq57452 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq57378 X0
       have i₂ := eq89 (σ y) X0
       grind)
    | exact superpose eq89 eq57378
    | exact resolve eq57378 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57378
  have eq57975 : ∀ X0 : G, y = (M.op x x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | exact superpose eq56955 eq56796
    | exact resolve eq56796 eq56955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56796
  have eq57976 : ∀ X0 : G, y = (M.op x x) ∨ y = (M.op X0 y) := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f57976_12 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ y = (M.op x x) := by
      intro X0
      grind
    have f57976_13 : ∀ X0 : G, y = (M.op x x) ∨ (M.op y X0) = X0 := by
      intro X0
      grind
    have f57976_21 : y ≠ (M.op x x) := by grind
    have f57976_22 : y ≠ (M.op X0 y) := by grind
    have f57976_24 : ∀ X0 : G, (M.op y X0) = X0 := by
      intro X0
      first
      | (have j0 := f57976_13 X0
         grind)
      | (have r₁ := f57976_13 X0
         have r₂ := f57976_21
         grind)
      | exact resolve f57976_13 f57976_21
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f57976_25 : ∀ X0 : G, y = (M.op (M.op y X0) y) := by
      intro X0
      first
      | (have j0 := f57976_12 X0
         grind)
      | (have r₁ := f57976_12 X0
         have r₂ := f57976_21
         grind)
      | exact resolve f57976_12 f57976_21
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f57976_26 : ∀ X0 : G, y = (M.op X0 y) := by
      intro X0
      first
      | (have i₁ := f57976_25 X0
         have i₂ := f57976_24 X0
         grind)
      | exact superpose f57976_24 f57976_25
      | exact resolve f57976_25 f57976_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f57976_27 : y ≠ y := by
      first
      | (have i₁ := f57976_22
         have i₂ := f57976_26 X0
         grind)
      | exact superpose f57976_26 f57976_22
      | (have r₁ := f57976_22
         have r₂ := f57976_26 X0
         grind)
      | exact resolve f57976_22 f57976_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f57976_28 : False := by grind
    exact f57976_28
  clear eq56955 eq57975
  have eq58209 : ∀ X0 : G, y = (M.op x y) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq89 x x
       have i₂ := eq57976 X0
       grind)
    | exact superpose eq57976 eq89
    | (have j1 := eq57976 x
       grind)
    | exact resolve eq89 eq57976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57976
  have eq59453 : y ≠ y ∨ y = (M.op x y) := by
    first
    | (have j0 := eq58209 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58209
  have eq59454 : y = (M.op x y) := by grind
  clear eq59453
  have eq59483 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq59454
       grind)
    | exact superpose eq59454 eq16
    | exact resolve eq16 eq59454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59487 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op (M.op x X0) y) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq64 X0 x y X1
       have i₂ := eq59454
       grind)
    | exact superpose eq59454 eq64
    | exact resolve eq64 eq59454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq59454
  have eq65708 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq57452 eq57293
    | exact resolve eq57293 eq57452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57293
  have eq65709 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ y = (M.op x x) := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f65709_12 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ y)) ∨ y = (M.op x x) := by
      intro X0
      grind
    have f65709_13 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ y = (M.op x x) := by
      intro X0
      grind
    have f65709_21 : (σ y) ≠ (M.op X0 (σ y)) := by grind
    have f65709_22 : y ≠ (M.op x x) := by grind
    have f65709_24 : ∀ X0 : G, (M.op (σ y) X0) = X0 := by
      intro X0
      first
      | (have j0 := f65709_13 X0
         grind)
      | (have r₁ := f65709_13 X0
         have r₂ := f65709_22
         grind)
      | exact resolve f65709_13 f65709_22
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f65709_25 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ y)) := by
      intro X0
      first
      | (have j0 := f65709_12 X0
         grind)
      | (have r₁ := f65709_12 X0
         have r₂ := f65709_22
         grind)
      | exact resolve f65709_12 f65709_22
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f65709_26 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
      intro X0
      first
      | (have i₁ := f65709_25 X0
         have i₂ := f65709_24 X0
         grind)
      | exact superpose f65709_24 f65709_25
      | exact resolve f65709_25 f65709_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f65709_27 : (σ y) ≠ (σ y) := by
      first
      | (have i₁ := f65709_21
         have i₂ := f65709_26 X0
         grind)
      | exact superpose f65709_26 f65709_21
      | (have r₁ := f65709_21
         have r₂ := f65709_26 X0
         grind)
      | exact resolve f65709_21 f65709_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f65709_28 : False := by grind
    exact f65709_28
  clear eq57452 eq65708
  have eq66848 : (σ y) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq59483
       have i₂ := eq65709 (σ x)
       grind)
    | exact superpose eq65709 eq59483
    | (have r₁ := eq59483
       have r₂ := eq65709 (σ x)
       grind)
    | exact resolve eq59483 eq65709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65709
  have eq66879 : y = (M.op x x) := by grind
  clear eq66848
  have eq67810 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq478 x
       have i₂ := eq66879
       grind)
    | exact superpose eq66879 eq478
    | exact resolve eq478 eq66879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478 eq66879
  have eq67991 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq67810
       have r₂ := eq59483
       grind)
    | exact resolve eq67810 eq59483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67810
  have eq76131 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq67991
       grind)
    | exact superpose eq67991 eq36
    | exact resolve eq36 eq67991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq67991
  have eq76366 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq76131
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq76131
    | exact resolve eq76131 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76131
  have eq76467 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq89 (σ x) (σ x)
       have i₂ := eq76366
       grind)
    | exact superpose eq76366 eq89
    | exact resolve eq89 eq76366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76366
  have eq76582 : y = (k y y) := by
    first
    | (have r₁ := eq76467
       have r₂ := eq59483
       grind)
    | exact resolve eq76467 eq59483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76467
  have eq76653 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq451 y y
       have i₂ := eq76582
       grind)
    | exact superpose eq76582 eq451
    | (have j0 := eq451 y y
       grind)
    | exact resolve eq451 eq76582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451
  have eq76654 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq14 y y
       have i₂ := eq76582
       grind)
    | exact superpose eq76582 eq14
    | (have j0 := eq14 y y
       grind)
    | exact resolve eq14 eq76582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76582
  have eq76655 : y = (M.op y y) := by grind
  clear eq76654
  have eq76656 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq76653
  have eq76702 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq76 y X0
       have i₂ := eq76655
       grind)
    | exact superpose eq76655 eq76
    | exact resolve eq76 eq76655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq76787 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) := by
    intro X0
    first
    | (have i₁ := eq643 y y x
       have i₂ := eq76655
       grind)
    | exact superpose eq76655 eq643
    | exact resolve eq643 eq76655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643 eq76655
  have eq76896 : ∀ X0 : G, y = (M.op (M.op y X0) y) := by
    intro X0
    first
    | (have i₁ := eq76787 X0
       have i₂ := eq89 y X0
       grind)
    | exact superpose eq89 eq76787
    | exact resolve eq76787 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq76787
  have eq77715 : ∀ X0 : G, (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq76702 X0
       have i₂ := eq76896 X0
       grind)
    | exact superpose eq76896 eq76702
    | exact resolve eq76702 eq76896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76702
  have eq77724 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq76896 X0
       have i₂ := eq77715 X0
       grind)
    | exact superpose eq77715 eq76896
    | exact resolve eq76896 eq77715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76896
  have eq78404 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op y X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq59487 X0 X1
       have i₂ := eq77724 (M.op x X0)
       grind)
    | exact superpose eq77724 eq59487
    | exact resolve eq59487 eq77724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59487 eq77724
  have eq79373 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq78404 X0 X1
       have i₂ := eq77715 X1
       grind)
    | exact superpose eq77715 eq78404
    | exact resolve eq78404 eq77715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77715 eq78404
  have eq80470 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) X0) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 X1) X0
       have i₂ := eq79373 X0 X1
       grind)
    | exact superpose eq79373 eq9
    | exact resolve eq9 eq79373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81880 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq80470 (σ y) (σ y) X0
       have i₂ := eq76656
       grind)
    | exact superpose eq76656 eq80470
    | exact resolve eq80470 eq76656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76656 eq80470
  have eq82081 : ∀ X0 : G, (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq81880 X0
       have i₂ := eq79373 (σ y) X0
       grind)
    | exact superpose eq79373 eq81880
    | exact resolve eq81880 eq79373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81880
  have eq82284 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq79373 (σ y) X0
       have i₂ := eq82081 X0
       grind)
    | exact superpose eq82081 eq79373
    | exact resolve eq79373 eq82081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79373 eq82081
  have eq82695 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq59483
       have i₂ := eq82284 (σ x)
       grind)
    | exact superpose eq82284 eq59483
    | (have r₁ := eq59483
       have r₂ := eq82284 (σ x)
       grind)
    | exact resolve eq59483 eq82284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59483 eq82284
  have eq82884 : False := by grind
  exact eq82884

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pyx_pxy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 (M.op X1 X1) X1
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : y = (τ (σ y)) := by
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
  have eq36 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq45 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq98 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq45 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq45
    | (have j0 := eq45 x
       grind)
    | exact resolve eq45 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
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
  have eq179 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq607 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y x) := by
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
  have eq609 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq28
    | (have j0 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq28 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq713 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq714 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq713 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq713 X0
       have r₂ := eq13 X0 X0
       grind)
    | (have r₁ := eq713 (M.op x x)
       have r₂ := eq13 (M.op (M.op x x) (M.op x x)) x
       grind)
    | (have r₁ := eq713 x
       have r₂ := eq13 (k x x) x
       grind)
    | exact resolve eq713 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713
  have eq750 : y = (M.op (M.op (M.op x y) (k x x)) y) := by
    first
    | (have i₁ := eq175 x
       have i₂ := eq714 x
       grind)
    | exact superpose eq714 eq175
    | exact resolve eq175 eq714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq758 : (σ x) = (M.op (M.op (k (σ x) (σ x)) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | (have i₁ := eq179 sF2
       have i₂ := eq714 sF2
       grind)
    | exact superpose eq714 eq179
    | exact resolve eq179 eq714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq867 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq607
       grind)
    | exact superpose eq607 eq40
    | exact resolve eq40 eq607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607
  have eq868 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq867
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq867
    | exact resolve eq867 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq867
  have eq870 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq20 eq868
    | exact resolve eq868 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq868
  have eq878 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq870 eq609
    | exact resolve eq609 eq870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq885 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq878
       have r₂ := eq27
       grind)
    | exact resolve eq878 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq878
  have eq890 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq885 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq885
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq885
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq885
       grind)
    | exact resolve eq12 eq885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq896 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq890
       have r₂ := eq26
       grind)
    | exact resolve eq890 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq890
  have eq899 : (σ y) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq896
       have i₂ := eq714 sF2
       grind)
    | exact superpose eq714 eq896
    | exact resolve eq896 eq714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896
  have eq901 : (σ y) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq870 eq899
    | exact resolve eq899 eq870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq899
  have eq902 : (σ y) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq901
       have r₂ := eq27
       grind)
    | exact resolve eq901 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901
  have eq905 : (τ (σ y)) = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq902 eq98
    | exact resolve eq98 eq902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq902
  have eq910 : (M.op x y) = (M.op y x) ∨ y = (k x x) := by
    first
    | exact superpose eq32 eq905
    | exact resolve eq905 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905
  have eq915 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x x) ∨ (M.op x y) = (k y x) ∨ y = (k x x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq910
       grind)
    | exact superpose eq910 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq910
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq910
       grind)
    | exact resolve eq12 eq910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq910
  have eq921 : y = (M.op x x) ∨ (M.op x y) = (k y x) ∨ y = (k x x) := by
    first
    | (have r₁ := eq915
       have r₂ := eq18
       grind)
    | exact resolve eq915 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq915
  have eq924 : y = (k x x) ∨ (M.op x y) = (k y x) ∨ y = (k x x) := by
    first
    | (have i₁ := eq921
       have i₂ := eq714 x
       grind)
    | exact superpose eq714 eq921
    | exact resolve eq921 eq714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921
  have eq925 : (M.op x y) = (k y x) ∨ y = (k x x) := by grind
  clear eq924
  have eq928 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq925
       grind)
    | exact superpose eq925 eq40
    | exact resolve eq40 eq925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq925
  have eq929 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq928
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq928
    | exact resolve eq928 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq928
  have eq931 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (k x x) := by
    first
    | exact superpose eq20 eq929
    | exact resolve eq929 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq929
  have eq944 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (k x x) := by
    first
    | exact superpose eq931 eq609
    | exact resolve eq609 eq931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609
  have eq951 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (k x x) := by
    first
    | (have r₁ := eq944
       have r₂ := eq27
       grind)
    | exact resolve eq944 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq944
  have eq956 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (k x x) := by
    first
    | exact superpose eq951 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq951
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq951
       grind)
    | exact resolve eq12 eq951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq951
  have eq962 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (k x x) := by
    first
    | (have r₁ := eq956
       have r₂ := eq26
       grind)
    | exact resolve eq956 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq956
  have eq965 : (σ y) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq962
       have i₂ := eq714 sF2
       grind)
    | exact superpose eq714 eq962
    | exact resolve eq962 eq714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq962
  have eq967 : (σ y) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (k x x) := by
    first
    | exact superpose eq931 eq965
    | exact resolve eq965 eq931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq931 eq965
  have eq968 : (σ y) = (k (σ x) (σ x)) ∨ y = (k x x) := by
    first
    | (have r₁ := eq967
       have r₂ := eq27
       grind)
    | exact resolve eq967 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq967
  have eq971 : (τ (σ y)) = (k x x) ∨ y = (k x x) := by
    first
    | exact superpose eq968 eq98
    | exact resolve eq98 eq968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq968
  have eq976 : y = (k x x) ∨ y = (k x x) := by
    first
    | exact superpose eq32 eq971
    | exact resolve eq971 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq971
  have eq977 : y = (k x x) := by grind
  clear eq976
  have eq982 : y = (M.op (M.op (M.op x y) y) y) := by
    first
    | (have i₁ := eq750
       have i₂ := eq977
       grind)
    | exact superpose eq977 eq750
    | exact resolve eq750 eq977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750
  have eq985 : (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq977
       grind)
    | exact superpose eq977 eq40
    | exact resolve eq40 eq977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq986 : (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq985
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq985
    | exact resolve eq985 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq985
  have eq988 : (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq986
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq986
    | exact resolve eq986 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq986
  have eq991 : (σ x) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq988 eq758
    | exact resolve eq758 eq988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq758
  have eq1200 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
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
  have eq1216 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1200 X0
       have i₂ := eq714 X0
       grind)
    | exact superpose eq714 eq1200
    | exact resolve eq1200 eq714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1200
  have eq5317 : x = (M.op y x) := by
    first
    | (have i₁ := eq1216 x
       have i₂ := eq977
       grind)
    | exact superpose eq977 eq1216
    | exact resolve eq1216 eq977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq977
  have eq5318 : (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq988 eq1216
    | exact resolve eq1216 eq988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1216
  have eq5403 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq5318 eq885
    | exact resolve eq885 eq5318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq885
  have eq5446 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq5403
       have i₂ := eq5317
       grind)
    | exact superpose eq5317 eq5403
    | exact resolve eq5403 eq5317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5403
  have eq5454 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5446 eq27
    | exact resolve eq27 eq5446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5473 : (σ x) = (M.op (M.op (σ y) (σ x)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5446 eq991
    | exact resolve eq991 eq5446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq991 eq5446
  have eq5546 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5318 eq5473
    | exact resolve eq5473 eq5318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5318 eq5473
  have eq5578 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq5546
       have i₂ := eq714 sF2
       grind)
    | exact superpose eq714 eq5546
    | exact resolve eq5546 eq714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5546
  have eq5599 : (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq988 eq5578
    | exact resolve eq5578 eq988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5578
  have eq5641 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5599 eq870
    | exact resolve eq870 eq5599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq870
  have eq5732 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq988 eq5641
    | exact resolve eq5641 eq988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5641
  have eq5786 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq5732
       have i₂ := eq5317
       grind)
    | exact superpose eq5317 eq5732
    | exact resolve eq5732 eq5317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5317 eq5732
  have eq5787 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq5786
  have eq5816 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq5599 eq5787
    | exact resolve eq5787 eq5599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5599 eq5787
  have eq5836 : x = (M.op x y) := by
    first
    | (have r₁ := eq5816
       have r₂ := eq5454
       grind)
    | exact resolve eq5816 eq5454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5454 eq5816
  have eq5849 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq5836
       grind)
    | exact superpose eq5836 eq18
    | exact resolve eq18 eq5836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq5850 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq5836
       grind)
    | exact superpose eq5836 eq22
    | exact resolve eq22 eq5836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5836
  have eq5898 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq5850 eq20
    | exact resolve eq20 eq5850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq5962 : y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq5849 eq982
    | exact resolve eq982 eq5849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq982
  have eq6003 : y = (M.op x y) := by
    first
    | exact superpose eq5849 eq5962
    | exact resolve eq5962 eq5849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5849 eq5962
  have eq6015 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq6003
       grind)
    | exact superpose eq6003 eq24
    | exact resolve eq24 eq6003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq6003
  have eq6114 : (σ x) = (σ y) := by
    first
    | exact superpose eq5850 eq6015
    | exact resolve eq6015 eq5850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5850 eq6015
  have eq6182 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq6114 eq26
    | exact resolve eq26 eq6114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq6292 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq6182
       have i₂ := eq714 sF2
       grind)
    | exact superpose eq714 eq6182
    | exact resolve eq6182 eq714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714 eq6182
  have eq6315 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq988 eq6292
    | exact resolve eq6292 eq988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq988 eq6292
  have eq6326 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6114 eq6315
    | exact resolve eq6315 eq6114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6114 eq6315
  have eq6332 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq6326 eq27
    | exact resolve eq27 eq6326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq6326
  have eq6438 : False := by grind
  exact eq6438

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pyy_pxy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
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
  have eq36 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    grind
  clear eq23
  have eq64 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq70 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq64 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq64
    | exact resolve eq64 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq76 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq9
    | exact resolve eq9 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq89 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq76 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq76
    | exact resolve eq76 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq177 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq311 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq177 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq177 X0 X1
       grind)
    | exact superpose eq177 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq177 X1 X0
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq177 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq177 X0 X1
       grind)
    | exact resolve eq13 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq322 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq311 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311
  have eq323 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq322 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322
  have eq331 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq323 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq323
    | (have j0 := eq323 X0 X1
       grind)
    | exact resolve eq323 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323
  have eq332 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq331 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331
  have eq1111 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq332 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq332
    | exact resolve eq332 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1123 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq332 x y
       grind)
    | exact superpose eq332 eq16
    | (have j1 := eq332 x y
       grind)
    | exact resolve eq16 eq332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332
  have eq1162 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1111 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq1111
    | (have j0 := eq1111 X0 X1
       grind)
    | exact resolve eq1111 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq1111
  have eq1163 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1162 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1162
    | exact resolve eq1162 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1162
  have eq1224 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq1163 (τ X1) X0
       grind)
    | exact superpose eq1163 eq18
    | (have j1 := eq1163 (τ X1) X0
       grind)
    | exact resolve eq18 eq1163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1350 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1224 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1224
    | exact resolve eq1224 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1224
  have eq1415 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1350 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1350
    | (have j0 := eq1350 X0 X1
       grind)
    | exact resolve eq1350 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1350
  have eq1682 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1123
       have i₂ := eq1163 y x
       grind)
    | exact superpose eq1163 eq1123
    | (have j1 := eq1163 (σ y) (σ x)
       grind)
    | exact resolve eq1123 eq1163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1163
  have eq1687 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq1682
  have eq1692 : (τ (σ y)) = (k (τ (σ y)) x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq1687
       grind)
    | exact superpose eq1687 eq36
    | exact resolve eq36 eq1687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq1713 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq89 (σ x) (σ x)
       have i₂ := eq1687
       grind)
    | exact superpose eq1687 eq89
    | exact resolve eq89 eq1687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1687
  have eq1728 : y = (k y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1692
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1692
    | exact resolve eq1692 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1692
  have eq1820 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1415 y x
       have i₂ := eq1728
       grind)
    | exact superpose eq1728 eq1415
    | (have j0 := eq1415 y x
       grind)
    | exact resolve eq1415 eq1728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1415 eq1728
  have eq1827 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by grind
  clear eq1820
  have eq1995 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1713
       grind)
    | exact superpose eq1713 eq16
    | exact resolve eq16 eq1713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1713
  have eq2020 : y = (M.op x x) := by
    first
    | (have r₁ := eq1995
       have r₂ := eq1827
       grind)
    | exact resolve eq1995 eq1827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1827 eq1995
  have eq2022 : y = (k y x) := by grind
  have eq2043 : y = (M.op x y) := by
    first
    | (have i₁ := eq89 x x
       have i₂ := eq2020
       grind)
    | exact superpose eq2020 eq89
    | exact resolve eq89 eq2020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2020
  have eq2056 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1123
       have i₂ := eq2022
       grind)
    | exact superpose eq2022 eq1123
    | exact resolve eq1123 eq2022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1123 eq2022
  have eq4706 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2056
       have i₂ := eq2043
       grind)
    | exact superpose eq2043 eq2056
    | exact resolve eq2056 eq2043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2056
  have eq4707 : (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq4706
  have eq4743 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq89 (σ x) (σ x)
       have i₂ := eq4707
       grind)
    | exact superpose eq4707 eq89
    | exact resolve eq89 eq4707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq4707
  have eq4827 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4743
       grind)
    | exact superpose eq4743 eq16
    | exact resolve eq16 eq4743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4743
  have eq4870 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq4827
       have i₂ := eq2043
       grind)
    | exact superpose eq2043 eq4827
    | exact resolve eq4827 eq2043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2043 eq4827
  have eq4871 : False := by grind
  exact eq4871

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pxy_pyx_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  clear eq36
  have eq51 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y x X0
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq54 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq81 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq82 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq88 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq81
  have eq90 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq82
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq82
    | exact resolve eq82 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq92 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq90
    | exact resolve eq90 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq93 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq92
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq92
    | exact resolve eq92 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq209 : y = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq51 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq51
    | (have j0 := eq51 y
       grind)
    | exact resolve eq51 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq216 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq27 eq52
    | (have j0 := eq52 (σ y)
       grind)
    | exact resolve eq52 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq380 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq53 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq384 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X1)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq53 X1 X0 X1 (M.op X0 X1)
       have i₂ := eq380 (M.op X0 X1)
       grind)
    | exact superpose eq380 eq53
    | exact resolve eq53 eq380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq387 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq380 X0
       grind)
    | exact superpose eq380 eq14
    | exact resolve eq14 eq380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380
  have eq478 : y = (M.op (M.op y (M.op x y)) y) := by
    first
    | (have i₁ := eq384 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq384
    | (have j0 := eq384 x y
       grind)
    | exact resolve eq384 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384
  have eq697 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq75 X0 X1
       grind)
    | exact superpose eq75 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq75 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq75 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq75 X0 X0
       grind)
    | exact resolve eq12 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq712 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq697 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697
  have eq714 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq712 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq712 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq712 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq712 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712
  have eq723 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq714 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq714
    | (have j0 := eq714 X0 X1
       grind)
    | exact resolve eq714 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714
  have eq970 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq54 eq387
    | exact resolve eq387 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq972 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq55 eq387
    | exact resolve eq387 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq387
  have eq8625 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq93 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8626 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq8625
    | exact resolve eq8625 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8625
  have eq8637 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq8626
       have r₂ := eq28
       grind)
    | exact resolve eq8626 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8626
  have eq8639 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq8637
    | exact resolve eq8637 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8637
  have eq8644 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq8639
  have eq8664 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq8644
    | exact resolve eq8644 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8644
  have eq10412 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq8664 eq93
    | exact resolve eq93 eq8664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq8664
  have eq10422 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq10412
  have eq10425 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq10422
       have r₂ := eq28
       grind)
    | exact resolve eq10422 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10422
  have eq10430 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq10425
  have eq10464 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10430
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq10430
    | exact resolve eq10430 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10430
  have eq11373 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq10464
       grind)
    | exact superpose eq10464 eq45
    | exact resolve eq45 eq10464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq10464
  have eq11389 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq11373
    | exact resolve eq11373 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11373
  have eq12139 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11389 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq11389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12142 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq12139
    | exact resolve eq12139 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12139
  have eq12153 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq12142
       have r₂ := eq28
       grind)
    | exact resolve eq12142 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12142
  have eq12155 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq12153
    | exact resolve eq12153 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12153
  have eq12156 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq12155
  have eq12914 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq12156
  have eq12950 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq12914
    | exact resolve eq12914 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12914
  have eq13006 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12950 eq11389
    | exact resolve eq11389 eq12950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11389 eq12950
  have eq13011 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq13006
  have eq13017 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq13011
       have r₂ := eq28
       grind)
    | exact resolve eq13011 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13011
  have eq13025 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13017 eq216
    | exact resolve eq216 eq13017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq13046 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13017 eq972
    | exact resolve eq972 eq13017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq972
  have eq13100 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  have eq13209 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13046 eq13025
    | exact resolve eq13025 eq13046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13025 eq13046
  have eq13251 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq13209
  have eq13255 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq13251
    | exact resolve eq13251 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13251
  have eq13289 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13255 eq13017
    | exact resolve eq13017 eq13255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13017 eq13255
  have eq13292 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq13289
  have eq13312 : y = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13292 eq30
    | exact resolve eq30 eq13292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq13292
  have eq13472 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq13312
    | exact resolve eq13312 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq13312
  have eq14440 : y = (M.op (M.op x x) y) ∨ x = y := by
    first
    | exact superpose eq13472 eq209
    | exact resolve eq209 eq13472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq14469 : x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq13472 eq970
    | exact resolve eq970 eq13472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20496 : y = (M.op x y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq14440
       have i₂ := eq14469
       grind)
    | exact superpose eq14469 eq14440
    | exact resolve eq14440 eq14469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14440 eq14469
  have eq20534 : y = (M.op x y) ∨ x = y := by grind
  clear eq20496
  have eq20537 : y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq20534
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq20534
    | exact resolve eq20534 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20534
  have eq20622 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq20537 eq13472
    | exact resolve eq13472 eq20537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13472 eq20537
  have eq20625 : x = y := by grind
  clear eq20622
  have eq20682 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq20625
       grind)
    | exact superpose eq20625 eq19
    | exact resolve eq19 eq20625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq20683 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq20625
       grind)
    | exact superpose eq20625 eq25
    | exact resolve eq25 eq20625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq20743 : x = (M.op (M.op x (M.op x y)) x) := by
    first
    | (have i₁ := eq478
       have i₂ := eq20625
       grind)
    | exact superpose eq20625 eq478
    | exact resolve eq478 eq20625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478 eq20625
  have eq20761 : x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq970 eq20743
    | exact resolve eq20743 eq970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq970 eq20743
  have eq20811 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq20683
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq20683
    | exact resolve eq20683 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20683
  have eq20816 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq20811 eq27
    | exact resolve eq27 eq20811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq20811
  have eq20976 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq88
       have i₂ := eq20682
       grind)
    | exact superpose eq20682 eq88
    | exact resolve eq88 eq20682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq20997 : (k (M.op x y) x) = (M.op (M.op x y) x) := by grind
  clear eq20682
  have eq21039 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq20976
    | exact resolve eq20976 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20976
  have eq21374 : x = (k (M.op x y) x) := by
    first
    | exact superpose eq20761 eq20997
    | exact resolve eq20997 eq20761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20761 eq20997
  have eq21565 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21039 eq13100
    | exact resolve eq13100 eq21039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13100 eq21039
  have eq21588 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq21565
  have eq21592 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20816 eq21588
    | exact resolve eq21588 eq20816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21588
  have eq21603 : x = (M.op x y) := by
    first
    | (have r₁ := eq21592
       have r₂ := eq28
       grind)
    | exact resolve eq21592 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21592
  have eq21633 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq21603 eq21
    | exact resolve eq21 eq21603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq21720 : x = (k x x) := by
    first
    | exact superpose eq21603 eq21374
    | exact resolve eq21374 eq21603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21374 eq21603
  have eq21797 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq21633
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq21633
    | exact resolve eq21633 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21633
  have eq22128 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq723 x x
       have i₂ := eq21720
       grind)
    | exact superpose eq21720 eq723
    | (have j0 := eq723 x x
       grind)
    | exact resolve eq723 eq21720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723 eq21720
  have eq22129 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq22128
  have eq22130 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq22129
  have eq22145 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq22130
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq22130
    | exact resolve eq22130 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq22130
  have eq22167 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20816 eq22145
    | exact resolve eq22145 eq20816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20816 eq22145
  have eq22184 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21797 eq22167
    | exact resolve eq22167 eq21797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21797 eq22167
  have eq22201 : False := by grind
  exact eq22201

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pyx_pxx_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 (M.op X1 X1) X1
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq15 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 x
       grind)
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : y = (τ (σ y)) := by
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
  have eq36 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq45 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq91 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq45 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq45
    | exact resolve eq45 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
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
  have eq181 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : y = (M.op (M.op (M.op x y) (M.op x y)) y) := by
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
  have eq185 : ∀ X0 : G, (M.op (M.op (M.op (M.op (M.op x y) (M.op x y)) X0) y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq182 eq16
    | exact resolve eq16 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq26 eq176
    | (have j0 := eq176 (σ y)
       grind)
    | exact resolve eq176 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq190 : ∀ X0 : G, (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) (σ y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq187 eq16
    | exact resolve eq16 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq559 : y = (M.op (M.op y y) y) := by
    first
    | exact superpose eq182 eq185
    | exact resolve eq185 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182 eq185
  have eq563 : ∀ X0 : G, (M.op (M.op (M.op (M.op y y) X0) y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 (M.op y y) y
       have i₂ := eq559
       grind)
    | exact superpose eq559 eq16
    | exact resolve eq16 eq559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559
  have eq569 : (σ y) = (M.op (M.op (σ y) (σ y)) (σ y)) := by
    first
    | exact superpose eq187 eq190
    | exact resolve eq190 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187 eq190
  have eq581 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq563 (M.op y X0)
       have i₂ := eq16 y y X0
       grind)
    | exact superpose eq16 eq563
    | exact resolve eq563 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563
  have eq641 : (M.op x y) = (k y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq28 y x
       grind)
    | exact superpose eq28 eq18
    | (have j1 := eq28 y x
       grind)
    | exact resolve eq18 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq655 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq28 sF3 sF2
       grind)
    | exact superpose eq28 eq26
    | (have j1 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq666 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq699 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq641
       grind)
    | exact superpose eq641 eq40
    | exact resolve eq40 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq700 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq699
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq699
    | exact resolve eq699 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699
  have eq702 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq700
    | exact resolve eq700 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700
  have eq712 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq702 eq655
    | exact resolve eq655 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655
  have eq719 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq712
       have r₂ := eq27
       grind)
    | exact resolve eq712 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712
  have eq725 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq719 eq28
    | (have j0 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq28 eq719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq726 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq719 eq16
    | exact resolve eq16 eq719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq729 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq725
    | exact resolve eq725 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq725
  have eq733 : (τ (σ y)) = (k x (τ (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq729 eq91
    | exact resolve eq91 eq729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq729
  have eq736 : y = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq32 eq733
    | exact resolve eq733 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq733
  have eq744 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq719 eq726
    | exact resolve eq726 eq719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq748 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq569 eq726
    | exact resolve eq726 eq569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569 eq726
  have eq755 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq744
  have eq757 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq748 eq755
    | exact resolve eq755 eq748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755
  have eq763 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq748 eq181
    | exact resolve eq181 eq748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq766 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq748 eq763
    | exact resolve eq763 eq748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq748 eq763
  have eq769 : (σ x) = (σ y) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq757 eq719
    | exact resolve eq719 eq757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719 eq757
  have eq776 : y = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq769
  have eq785 : y = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq581 x
       have i₂ := eq776
       grind)
    | exact superpose eq776 eq581
    | exact resolve eq581 eq776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq789 : ∀ X0 : G, x = (M.op (M.op y (M.op y X0)) x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq16 x y X0
       have i₂ := eq776
       grind)
    | exact superpose eq776 eq16
    | exact resolve eq16 eq776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq791 : ∀ X0 : G, x = (M.op (M.op y X0) x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq789 X0
       have i₂ := eq581 X0
       grind)
    | exact superpose eq581 eq789
    | exact resolve eq789 eq581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581 eq789
  have eq842 : x = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq791 y
       have i₂ := eq785
       grind)
    | exact superpose eq785 eq791
    | exact resolve eq791 eq785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq785 eq791
  have eq851 : x = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq842
  have eq857 : x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq776
       have i₂ := eq851
       grind)
    | exact superpose eq851 eq776
    | exact resolve eq776 eq851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776 eq851
  have eq865 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq857
  have eq873 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq865 eq32
    | exact resolve eq32 eq865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq865
  have eq907 : x = y ∨ x = y := by
    first
    | exact superpose eq30 eq873
    | exact resolve eq873 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq873
  have eq908 : x = y := by grind
  clear eq907
  have eq909 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq908
       grind)
    | exact superpose eq908 eq18
    | exact resolve eq18 eq908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq910 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq908
       grind)
    | exact superpose eq908 eq24
    | exact resolve eq24 eq908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq923 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq736
       have i₂ := eq908
       grind)
    | exact superpose eq908 eq736
    | exact resolve eq736 eq908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736
  have eq930 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq666 x
       grind)
    | (have r₁ := eq923
       have r₂ := eq666 x
       grind)
    | exact resolve eq923 eq666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq923
  have eq934 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq910
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq910
    | exact resolve eq910 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq910
  have eq935 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq930
       have i₂ := eq909
       grind)
    | exact superpose eq909 eq930
    | exact resolve eq930 eq909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq930
  have eq936 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq934 eq26
    | exact resolve eq26 eq934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq954 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq934 eq702
    | exact resolve eq702 eq934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702
  have eq960 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq934 eq766
    | exact resolve eq766 eq934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766 eq934
  have eq961 : x = (M.op x x) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq960
       have i₂ := eq908
       grind)
    | exact superpose eq908 eq960
    | exact resolve eq960 eq908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq960
  have eq966 : x = (M.op x x) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq954
       have i₂ := eq908
       grind)
    | exact superpose eq908 eq954
    | exact resolve eq954 eq908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq954
  have eq977 : x = (M.op x y) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq961
       have i₂ := eq909
       grind)
    | exact superpose eq909 eq961
    | exact resolve eq961 eq909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq961
  have eq982 : x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq966
       have i₂ := eq909
       grind)
    | exact superpose eq909 eq966
    | exact resolve eq966 eq909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq966
  have eq986 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq977 eq982
    | exact resolve eq982 eq977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq977 eq982
  have eq995 : (k (M.op x y) x) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq181 x
       have i₂ := eq909
       grind)
    | exact superpose eq909 eq181
    | exact resolve eq181 eq909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq909
  have eq1009 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq935 eq27
    | exact resolve eq27 eq935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq935
  have eq1023 : x = (M.op x y) := by
    first
    | (have r₁ := eq1009
       have r₂ := eq986
       grind)
    | exact resolve eq1009 eq986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq986 eq1009
  have eq1028 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq1023
       grind)
    | exact superpose eq1023 eq22
    | exact resolve eq22 eq1023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq1034 : (M.op x y) = (k y (M.op x y)) ∨ y = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq641
       have i₂ := eq1023
       grind)
    | exact superpose eq1023 eq641
    | exact resolve eq641 eq1023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641
  have eq1041 : (M.op x y) = (k x (M.op x y)) ∨ y = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq1034
       have i₂ := eq908
       grind)
    | exact superpose eq908 eq1034
    | exact resolve eq1034 eq908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1034
  have eq1046 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq1041
       have i₂ := eq1023
       grind)
    | exact superpose eq1023 eq1041
    | exact resolve eq1041 eq1023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1041
  have eq1051 : x = (M.op x (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1046
       have i₂ := eq908
       grind)
    | exact superpose eq908 eq1046
    | exact resolve eq1046 eq908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq908 eq1046
  have eq1054 : x = (k (M.op x y) x) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq995 eq1051
    | exact resolve eq1051 eq995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq995 eq1051
  have eq1057 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1054
       have i₂ := eq1023
       grind)
    | exact superpose eq1023 eq1054
    | exact resolve eq1054 eq1023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1023 eq1054
  have eq1058 : (M.op x y) = (k (M.op x y) (M.op x y)) := by grind
  clear eq1057
  have eq1060 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1028 eq20
    | exact resolve eq20 eq1028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1028
  have eq1491 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1058 eq38
    | exact resolve eq38 eq1058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq1058
  have eq1496 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq1491
    | exact resolve eq1491 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1491
  have eq1498 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq1060 eq1496
    | exact resolve eq1496 eq1060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1496
  have eq1503 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1498 eq666
    | (have j0 := eq666 (σ x)
       grind)
    | (have r₁ := eq666 (σ x)
       have r₂ := eq1498
       grind)
    | exact resolve eq666 eq1498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666 eq1498
  have eq1504 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1503
  have eq1514 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1504 eq936
    | exact resolve eq936 eq1504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936 eq1504
  have eq1536 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq1514 eq27
    | exact resolve eq27 eq1514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1514
  have eq1549 : False := by grind
  exact eq1549

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pyx_pyy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
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
  have eq70 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
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
  have eq74 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op X0 X0) X1) X0) X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 X1 (M.op X0 X0) X0 X2
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq62
    | exact resolve eq62 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq9
    | exact resolve eq9 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op X0 X0) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X0) X1
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq9
    | exact resolve eq9 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq89 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq76 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq76
    | exact resolve eq76 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X1 : G, (M.op X1 X1) = (k (M.op X1 X1) X1) := by
    intro X1
    grind
  have eq112 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq23 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq96 (σ X0)
       grind)
    | exact superpose eq96 eq23
    | exact resolve eq23 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq466 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq74 X0 (M.op X0 X1) X2
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq74
    | exact resolve eq74 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq745 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq2818 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq745 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq745
    | (have j0 := eq745 X1 X0
       have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq745 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2819 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq745 (M.op X0 X0) X0
       have i₂ := eq96 X0
       grind)
    | exact superpose eq96 eq745
    | (have j0 := eq745 (M.op X0 X0) X0
       grind)
    | exact resolve eq745 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745
  have eq14829 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ (M.op X0 X0)) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 (σ (M.op X0 X0)) (σ X0)
       have i₂ := eq2819 X0
       grind)
    | exact superpose eq2819 eq13
    | (have j0 := eq13 (σ (M.op X0 X0)) (σ X0)
       have j1 := eq2819 X0
       grind)
    | (have r₁ := eq13 (σ (M.op X0 X0)) (σ X0)
       have r₂ := eq2819 X0
       grind)
    | exact resolve eq13 eq2819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2819
  have eq14903 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ (M.op X0 X0)) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq14829 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14829
  have eq14904 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ (M.op X0 X0)) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq14903 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14903
  have eq14942 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (M.op X0 X0) X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq14904 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq14904
    | (have j0 := eq14904 X0
       grind)
    | exact resolve eq14904 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14904
  have eq14953 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq14942 X0
       have i₂ := eq96 X0
       grind)
    | exact superpose eq96 eq14942
    | (have j0 := eq14942 X0
       grind)
    | exact resolve eq14942 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq14942
  have eq14954 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq14953 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14953
  have eq17653 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2818 x y
       grind)
    | exact superpose eq2818 eq16
    | (have j1 := eq2818 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq2818 x y
       grind)
    | exact resolve eq16 eq2818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2818
  have eq17787 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq17653
  have eq42313 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq89 (σ y) (σ x)
       have i₂ := eq17787
       grind)
    | exact superpose eq17787 eq89
    | exact resolve eq89 eq17787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17787
  have eq161138 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq112 y
       have i₂ := eq42313
       grind)
    | exact superpose eq42313 eq112
    | exact resolve eq112 eq42313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42313
  have eq161461 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k y y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq161138
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq161138
    | exact resolve eq161138 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161138
  have eq161492 : (τ (σ y)) = (k (τ (σ y)) x) ∨ y = (k y y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq112 x
       have i₂ := eq161461
       grind)
    | exact superpose eq161461 eq112
    | exact resolve eq112 eq161461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq161592 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq89 (σ x) (σ x)
       have i₂ := eq161461
       grind)
    | exact superpose eq161461 eq89
    | exact resolve eq89 eq161461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161461
  have eq161792 : y = (k y x) ∨ y = (k y y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq161492
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq161492
    | exact resolve eq161492 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161492
  have eq161802 : y = (k y y) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq14 eq161792
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq161792 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161792
  have eq162884 : (σ (M.op x y)) ≠ (σ y) ∨ y = (k y y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq161592
       grind)
    | exact superpose eq161592 eq16
    | exact resolve eq16 eq161592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161592
  have eq163115 : (σ y) ≠ (σ y) ∨ y = (k y y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq161802 eq162884
    | exact resolve eq162884 eq161802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161802 eq162884
  have eq163116 : y = (k y y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq163115
  have eq163227 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14 y y
       have i₂ := eq163116
       grind)
    | exact superpose eq163116 eq14
    | (have j0 := eq14 y y
       grind)
    | exact resolve eq14 eq163116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163116
  have eq163228 : y = (M.op y y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq163227
  have eq163265 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq76 y X0
       have i₂ := eq163228
       grind)
    | exact superpose eq163228 eq76
    | exact resolve eq76 eq163228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq163357 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq466 y y x
       have i₂ := eq163228
       grind)
    | exact superpose eq163228 eq466
    | exact resolve eq466 eq163228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163228
  have eq163547 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq163357 X0
       have i₂ := eq89 y X0
       grind)
    | exact superpose eq89 eq163357
    | exact resolve eq163357 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163357
  have eq164703 : ∀ X0 : G, y = (M.op y x) ∨ (M.op y X0) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq163547 eq163265
    | exact resolve eq163265 eq163547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163265 eq163547
  have eq164727 : ∀ X0 : G, y = (M.op y y) ∨ (M.op y X0) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq89 y x
       have i₂ := eq164703 X0
       grind)
    | exact superpose eq164703 eq89
    | (have j1 := eq164703 y
       grind)
    | exact resolve eq89 eq164703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164703
  have eq165538 : y ≠ y ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have j0 := eq164727 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164727
  have eq165539 : y = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq165538
  have eq165642 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq76 y X0
       have i₂ := eq165539
       grind)
    | exact superpose eq165539 eq76
    | exact resolve eq76 eq165539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq165734 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq466 y y x
       have i₂ := eq165539
       grind)
    | exact superpose eq165539 eq466
    | exact resolve eq466 eq165539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466 eq165539
  have eq165923 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq165734 X0
       have i₂ := eq89 y X0
       grind)
    | exact superpose eq89 eq165734
    | exact resolve eq165734 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165734
  have eq167191 : ∀ X0 : G, y = (M.op x x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | exact superpose eq165923 eq165642
    | exact resolve eq165642 eq165923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165642
  have eq167194 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq167191 eq165923
    | exact resolve eq165923 eq167191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165923
  have eq167246 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14954 x
       have i₂ := eq167191 X0
       grind)
    | exact superpose eq167191 eq14954
    | (have j1 := eq167191 X0
       grind)
    | exact resolve eq14954 eq167191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167191
  have eq167456 : ∀ X0 : G, y = (M.op x x) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq167194 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167194
  have eq167542 : ∀ X0 : G, y = (M.op x y) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq89 x x
       have i₂ := eq167456 X0
       grind)
    | exact superpose eq167456 eq89
    | (have j1 := eq167456 x
       grind)
    | exact resolve eq89 eq167456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167456
  have eq169306 : y ≠ y ∨ y = (M.op x y) := by
    first
    | (have j0 := eq167542 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167542
  have eq169307 : y = (M.op x y) := by grind
  clear eq169306
  have eq169351 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq169307
       grind)
    | exact superpose eq169307 eq16
    | exact resolve eq16 eq169307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq169356 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op (M.op x X0) y) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq62 X0 x y X1
       have i₂ := eq169307
       grind)
    | exact superpose eq169307 eq62
    | exact resolve eq62 eq169307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq169307
  have eq171493 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ x)) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have j1 := eq167246 X0
       grind)
    | (have r₁ := eq169351
       have r₂ := eq167246 X0
       grind)
    | exact resolve eq169351 eq167246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167246
  have eq176318 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq89 (σ x) (σ x)
       have i₂ := eq171493 X0
       grind)
    | exact superpose eq171493 eq89
    | (have j1 := eq171493 X0
       grind)
    | exact resolve eq89 eq171493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq171493
  have eq176503 : ∀ X0 : G, (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq176318 X0
       grind)
    | (have r₁ := eq176318 X0
       have r₂ := eq169351
       grind)
    | exact resolve eq176318 eq169351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176318
  have eq176614 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq14954 y
       have i₂ := eq176503 y
       grind)
    | exact superpose eq176503 eq14954
    | exact resolve eq14954 eq176503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14954
  have eq176804 : ∀ X0 : G, y = (M.op (M.op (M.op y y) X0) y) := by
    intro X0
    first
    | (have i₁ := eq77 y X0
       have i₂ := eq176503 (M.op (M.op y y) X0)
       grind)
    | exact superpose eq176503 eq77
    | exact resolve eq77 eq176503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq177014 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq176614
  have eq177146 : ∀ X0 : G, y = (M.op (M.op y X0) y) := by
    intro X0
    first
    | (have i₁ := eq176804 X0
       have i₂ := eq176503 y
       grind)
    | exact superpose eq176503 eq176804
    | exact resolve eq176804 eq176503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176804
  have eq177385 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq177146 X0
       have i₂ := eq176503 X0
       grind)
    | exact superpose eq176503 eq177146
    | exact resolve eq177146 eq176503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177146
  have eq177648 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op y X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq169356 X0 X1
       have i₂ := eq177385 (M.op x X0)
       grind)
    | exact superpose eq177385 eq169356
    | exact resolve eq169356 eq177385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169356 eq177385
  have eq179068 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq177648 X0 X1
       have i₂ := eq176503 X1
       grind)
    | exact superpose eq176503 eq177648
    | exact resolve eq177648 eq176503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176503 eq177648
  have eq179967 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (σ y) (σ y)
       have i₂ := eq177014
       grind)
    | exact superpose eq177014 eq9
    | exact resolve eq9 eq177014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177014
  have eq180138 : ∀ X0 : G, (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq179967 X0
       have i₂ := eq179068 (σ y) X0
       grind)
    | exact superpose eq179068 eq179967
    | exact resolve eq179967 eq179068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179967
  have eq180340 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq179068 (σ y) X0
       have i₂ := eq180138 X0
       grind)
    | exact superpose eq180138 eq179068
    | exact resolve eq179068 eq180138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179068 eq180138
  have eq180676 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq169351
       have i₂ := eq180340 (σ x)
       grind)
    | exact superpose eq180340 eq169351
    | (have r₁ := eq169351
       have r₂ := eq180340 (σ x)
       grind)
    | exact resolve eq169351 eq180340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169351 eq180340
  have eq181190 : False := by grind
  exact eq181190

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pyx_y_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 (M.op X1 X1) X1
       have r₂ := eq13 (M.op X1 X1) X1
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
  have eq30 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq15 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 x
       grind)
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq181 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : y = (M.op (M.op (M.op x y) (M.op x y)) y) := by
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
  have eq185 : ∀ X0 : G, (M.op (M.op (M.op (M.op (M.op x y) (M.op x y)) X0) y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq182 eq16
    | exact resolve eq16 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq26 eq176
    | (have j0 := eq176 (σ y)
       grind)
    | exact resolve eq176 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq190 : ∀ X0 : G, (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) (σ y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq187 eq16
    | exact resolve eq16 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq559 : y = (M.op (M.op y y) y) := by
    first
    | exact superpose eq182 eq185
    | exact resolve eq185 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182 eq185
  have eq563 : ∀ X0 : G, (M.op (M.op (M.op (M.op y y) X0) y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 (M.op y y) y
       have i₂ := eq559
       grind)
    | exact superpose eq559 eq16
    | exact resolve eq16 eq559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq569 : (σ y) = (M.op (M.op (σ y) (σ y)) (σ y)) := by
    first
    | exact superpose eq187 eq190
    | exact resolve eq190 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187 eq190
  have eq581 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq563 (M.op y X0)
       have i₂ := eq16 y y X0
       grind)
    | exact superpose eq16 eq563
    | exact resolve eq563 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563
  have eq587 : (M.op y y) = (k (M.op y y) y) := by
    first
    | (have i₁ := eq181 y
       have i₂ := eq581 y
       grind)
    | exact superpose eq581 eq181
    | exact resolve eq181 eq581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq610 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (k X0 X1)) X2) = X2 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X1 X0
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq611 : ∀ X0 X1 X2 : G, (M.op (M.op (k X0 X1) (M.op X1 X2)) X0) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 X2
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq641 : (M.op x y) = (k y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq28 y x
       grind)
    | exact superpose eq28 eq18
    | (have j1 := eq28 y x
       grind)
    | exact resolve eq18 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq655 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq28 sF3 sF2
       grind)
    | exact superpose eq28 eq26
    | (have j1 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq666 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq693 : x ≠ (M.op x y) ∨ x = (M.op y y) ∨ y = (k x y) := by
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
  have eq699 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq641
       grind)
    | exact superpose eq641 eq40
    | exact resolve eq40 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641
  have eq700 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq699
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq699
    | exact resolve eq699 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699
  have eq702 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq700
    | exact resolve eq700 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700
  have eq712 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq702 eq655
    | exact resolve eq655 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655
  have eq719 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq712
       have r₂ := eq27
       grind)
    | exact resolve eq712 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712
  have eq724 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq719 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq719
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq719
       grind)
    | exact resolve eq12 eq719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719
  have eq728 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq724
  have eq730 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq702 eq728
    | exact resolve eq728 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728
  have eq747 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq730 eq181
    | exact resolve eq181 eq730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730
  have eq749 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq747
    | exact resolve eq747 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747
  have eq751 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq702 eq749
    | exact resolve eq749 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702 eq749
  have eq752 : y = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq751
       have r₂ := eq27
       grind)
    | exact resolve eq751 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751
  have eq754 : y = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq581 x
       have i₂ := eq752
       grind)
    | exact superpose eq752 eq581
    | exact resolve eq581 eq752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq758 : ∀ X0 : G, x = (M.op (M.op y (M.op y X0)) x) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq16 x y X0
       have i₂ := eq752
       grind)
    | exact superpose eq752 eq16
    | exact resolve eq16 eq752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq760 : ∀ X0 : G, x = (M.op (M.op y X0) x) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq758 X0
       have i₂ := eq581 X0
       grind)
    | exact superpose eq581 eq758
    | exact resolve eq758 eq581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581 eq758
  have eq797 : x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq760 y
       have i₂ := eq754
       grind)
    | exact superpose eq754 eq760
    | exact resolve eq760 eq754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq754
  have eq806 : x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq797
  have eq817 : x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq752
       have i₂ := eq806
       grind)
    | exact superpose eq806 eq752
    | exact resolve eq752 eq806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq752
  have eq818 : x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq760 x
       have i₂ := eq806
       grind)
    | exact superpose eq806 eq760
    | exact resolve eq760 eq806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq822 : ∀ X0 : G, (M.op (M.op (M.op y X0) x) X0) = X0 ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq16 X0 y x
       have i₂ := eq806
       grind)
    | exact superpose eq806 eq16
    | exact resolve eq16 eq806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806
  have eq824 : x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq818
  have eq825 : (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq817
  have eq827 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq760 eq822
    | exact resolve eq822 eq760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq760 eq822
  have eq832 : (M.op x y) = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq825 eq29
    | exact resolve eq29 eq825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq825
  have eq851 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq832
    | exact resolve eq832 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq832
  have eq854 : (M.op x y) = (M.op (M.op x y) y) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq851
       grind)
    | exact superpose eq851 eq18
    | exact resolve eq18 eq851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851
  have eq876 : (k x x) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq181 x
       have i₂ := eq824
       grind)
    | exact superpose eq824 eq181
    | exact resolve eq181 eq824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq879 : x = (k x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq824 eq876
    | exact resolve eq876 eq824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824 eq876
  have eq891 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq827 y
       grind)
    | exact superpose eq827 eq18
    | (have j1 := eq827 y
       grind)
    | exact resolve eq18 eq827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq898 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x X1)) X0) = X0 ∨ (σ (M.op x y)) = (σ x) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 x X1
       have i₂ := eq827 X0
       grind)
    | exact superpose eq827 eq16
    | exact resolve eq16 eq827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq905 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 ∨ (σ (M.op x y)) = (σ x) := by
    intro X0 X1
    first
    | exact superpose eq827 eq898
    | exact resolve eq898 eq827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827 eq898
  have eq910 : (M.op x y) = (τ (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq891 eq29
    | exact resolve eq29 eq891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq891
  have eq929 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq910
    | exact resolve eq910 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq910
  have eq933 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq929
       grind)
    | exact superpose eq929 eq24
    | exact resolve eq24 eq929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq953 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq933
    | exact resolve eq933 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq933
  have eq993 : (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq879
       grind)
    | exact superpose eq879 eq40
    | exact resolve eq40 eq879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq879
  have eq996 : (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq993
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq993
    | exact resolve eq993 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq993
  have eq1029 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq854
       have i₂ := eq929
       grind)
    | exact superpose eq929 eq854
    | exact resolve eq854 eq929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854 eq929
  have eq1036 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq1029
  have eq1040 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq996 eq666
    | (have j0 := eq666 (σ x)
       grind)
    | (have r₁ := eq666 (σ x)
       have r₂ := eq996
       grind)
    | exact resolve eq666 eq996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq996
  have eq1041 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1040
  have eq1056 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1036 eq181
    | exact resolve eq181 eq1036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1061 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1036 eq1056
    | exact resolve eq1056 eq1036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1036 eq1056
  have eq1075 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq1041 eq16
    | exact resolve eq16 eq1041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1041
  have eq1079 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq905 eq1075
    | exact resolve eq1075 eq905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905 eq1075
  have eq1083 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1061 eq42
    | exact resolve eq42 eq1061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq1061
  have eq1086 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq1083
    | exact resolve eq1083 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1083
  have eq1088 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq953 eq1086
    | exact resolve eq1086 eq953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1086
  have eq1103 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1079 eq26
    | (have j1 := eq1079 (σ y)
       grind)
    | exact resolve eq26 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1079
  have eq1122 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1103 eq27
    | exact resolve eq27 eq1103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1103
  have eq1131 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq953 eq1122
    | (have r₁ := eq1122
       have r₂ := eq953
       grind)
    | exact resolve eq1122 eq953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1122
  have eq1132 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq1131
  have eq1133 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1132 eq26
    | exact resolve eq26 eq1132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1171 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1132 eq1088
    | exact resolve eq1088 eq1132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1175 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1088 eq666
    | (have j0 := eq666 (σ y)
       grind)
    | (have r₁ := eq666 (σ y)
       have r₂ := eq1088
       grind)
    | exact resolve eq666 eq1088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666 eq1088
  have eq1176 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1175
  have eq1177 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq1171
  have eq1178 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1132 eq1176
    | exact resolve eq1176 eq1132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1176
  have eq1200 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1178 eq181
    | exact resolve eq181 eq1178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq1178
  have eq1204 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1133 eq1200
    | exact resolve eq1200 eq1133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1133 eq1200
  have eq1207 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1177 eq1204
    | exact resolve eq1204 eq1177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1177 eq1204
  have eq1210 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1207 eq27
    | exact resolve eq27 eq1207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1207
  have eq1233 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq953 eq1210
    | exact resolve eq1210 eq953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq953 eq1210
  have eq1238 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by grind
  clear eq1233
  have eq1239 : x = (M.op x y) := by
    first
    | (have r₁ := eq1238
       have r₂ := eq1132
       grind)
    | exact resolve eq1238 eq1132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1132 eq1238
  have eq1240 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1239
       grind)
    | exact superpose eq1239 eq18
    | exact resolve eq18 eq1239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1241 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq1239
       grind)
    | exact superpose eq1239 eq22
    | exact resolve eq22 eq1239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq1242 : ∀ X0 : G, (k (σ x) (σ X0)) = (σ (k (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq1239
       grind)
    | exact superpose eq1239 eq36
    | exact resolve eq36 eq1239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq1248 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ y = (k (M.op x y) y) := by
    first
    | (have i₁ := eq693
       have i₂ := eq1239
       grind)
    | exact superpose eq1239 eq693
    | (have r₁ := eq693
       have r₂ := eq1239
       grind)
    | exact resolve eq693 eq1239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693 eq1239
  have eq1257 : (M.op x y) = (M.op y y) ∨ y = (k (M.op x y) y) := by grind
  clear eq1248
  have eq1261 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1241 eq20
    | exact resolve eq20 eq1241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1241
  have eq2961 : (M.op x y) = (k (M.op x y) y) ∨ y = (k (M.op x y) y) := by
    first
    | (have i₁ := eq587
       have i₂ := eq1257
       grind)
    | exact superpose eq1257 eq587
    | exact resolve eq587 eq1257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587
  have eq2963 : y = (M.op (M.op x y) y) ∨ y = (k (M.op x y) y) := by
    first
    | (have i₁ := eq559
       have i₂ := eq1257
       grind)
    | exact superpose eq1257 eq559
    | exact resolve eq559 eq1257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559 eq1257
  have eq2980 : y = (k (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1240 eq2963
    | exact resolve eq2963 eq1240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1240 eq2963
  have eq3042 : y ≠ (M.op x y) ∨ y = (k (M.op x y) y) := by grind
  clear eq2961
  have eq3045 : y = (k (M.op x y) y) := by
    first
    | (have r₁ := eq3042
       have r₂ := eq2980
       grind)
    | exact resolve eq3042 eq2980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2980 eq3042
  have eq3051 : (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq3045 eq1242
    | exact resolve eq1242 eq3045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1242 eq3045
  have eq3058 : (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq3051
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3051
    | exact resolve eq3051 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq3051
  have eq3067 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) (M.op (σ y) X0)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq3058 eq611
    | (have j0 := eq611 (σ x) (σ y) x
       grind)
    | exact resolve eq611 eq3058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611
  have eq3068 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq3058 eq610
    | (have j0 := eq610 (σ x) (σ y) x
       grind)
    | exact resolve eq610 eq3058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610
  have eq3069 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq3068
    | (have j0 := eq3068 X0
       grind)
    | exact resolve eq3068 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3068
  have eq3070 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) (M.op (σ y) X0)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq3067
    | (have j0 := eq3067 X0
       grind)
    | exact resolve eq3067 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3067
  have eq4753 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq569 eq3069
    | exact resolve eq3069 eq569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569 eq3069
  have eq4898 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4753 eq3070
    | exact resolve eq3070 eq4753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3070
  have eq4922 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4898
  have eq4925 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4753 eq4922
    | exact resolve eq4922 eq4753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4753 eq4922
  have eq4942 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4925 eq28
    | (have j0 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq28 eq4925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4925
  have eq4956 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3058 eq4942
    | exact resolve eq4942 eq3058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4942
  have eq4962 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq4956
    | exact resolve eq4956 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4956
  have eq4963 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq4962
  have eq4967 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq4963 eq27
    | exact resolve eq27 eq4963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4963
  have eq4985 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq4967
       have r₂ := eq1261
       grind)
    | exact resolve eq4967 eq1261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4967
  have eq4986 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq4985 eq26
    | exact resolve eq26 eq4985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq5016 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq4985 eq3058
    | exact resolve eq3058 eq4985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3058 eq4985
  have eq5129 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4986 eq28
    | (have j0 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq28 eq4986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq4986
  have eq5141 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5016 eq5129
    | exact resolve eq5129 eq5016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5016 eq5129
  have eq5142 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq5141
  have eq5696 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq5142 eq27
    | exact resolve eq27 eq5142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq5142
  have eq5717 : False := by grind
  exact eq5717

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if m(X,Y) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pyy_pxx_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
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
  clear eq18
  have eq25 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    grind
  have eq36 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    grind
  have eq64 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq70 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq64 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq64
    | exact resolve eq64 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op X0 X0) X1) X0) X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 X1 (M.op X0 X0) X0 X2
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq64
    | exact resolve eq64 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq76 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq9
    | exact resolve eq9 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq89 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq76 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq76
    | exact resolve eq76 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op (M.op X0 X0) X1) X0) (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq76 X0 (M.op (M.op X0 X0) X1)
       have i₂ := eq89 (M.op X0 X0) X1
       grind)
    | exact superpose eq89 eq76
    | exact resolve eq76 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq275 : ∀ X0 : G, (σ (σ (M.op (τ (τ X0)) (τ (τ X0))))) = (k (σ (σ (M.op (τ (τ X0)) (τ (τ X0))))) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (σ (M.op (τ (τ X0)) (τ (τ X0))))
       have i₂ := eq25 (τ X0)
       grind)
    | exact superpose eq25 eq19
    | exact resolve eq19 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq533 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq74 X0 (M.op X0 X1) X2
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq74
    | exact resolve eq74 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq626 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq639 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 ∨ (M.op (τ X0) (τ X0)) = X1 := by
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
  have eq2360 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = (M.op X0 (M.op (M.op X0 X0) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq108 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq108
    | exact resolve eq108 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq2457 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op (M.op X0 X0) (M.op X0 X1))) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X0 (M.op (M.op X0 X0) (M.op X0 X1))
       have i₂ := eq2360 X0 X1
       grind)
    | exact superpose eq2360 eq9
    | exact resolve eq9 eq2360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2360
  have eq2720 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq626 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq626
    | (have j0 := eq626 X1 X0
       have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq626 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2721 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  have eq2746 : ∀ X0 X1 X2 : G, (σ (k (k X1 X0) X2)) = (k (M.op (σ X0) (σ X1)) (σ X2)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k X1 X0) X2
       have i₂ := eq626 X1 X0
       grind)
    | exact superpose eq626 eq15
    | (have j1 := eq626 X1 X0
       grind)
    | exact resolve eq15 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626
  have eq9979 : ∀ X0 : G, (σ (k (σ (τ (τ X0))) (τ X0))) = (k (σ (k (σ (τ (τ X0))) (τ X0))) X0) ∨ (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) ∨ (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq275 X0
       have i₂ := eq639 (τ X0) (τ (τ X0))
       grind)
    | exact superpose eq639 eq275
    | (have j1 := eq639 (τ X0) (τ (τ X0))
       grind)
    | exact resolve eq275 eq639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275 eq639
  have eq10035 : ∀ X0 : G, (σ (k (σ (τ (τ X0))) (τ X0))) = (k (σ (k (σ (τ (τ X0))) (τ X0))) X0) ∨ (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) := by
    intro X0
    first
    | (have j0 := eq9979 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9979
  have eq10038 : ∀ X0 : G, (k (σ (σ (τ (τ X0)))) X0) = (k (k (σ (σ (τ (τ X0)))) X0) X0) ∨ (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq10035 X0
       have i₂ := eq19 X0 (σ (τ (τ X0)))
       grind)
    | exact superpose eq19 eq10035
    | (have j0 := eq10035 X0
       grind)
    | exact resolve eq10035 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq10035
  have eq10042 : ∀ X0 : G, (k (σ (τ X0)) X0) = (k (k (σ (τ X0)) X0) X0) ∨ (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq10038 X0
       have i₂ := eq11 (τ X0)
       grind)
    | exact superpose eq11 eq10038
    | (have j0 := eq10038 X0
       grind)
    | exact resolve eq10038 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10038
  have eq10043 : ∀ X0 : G, (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq10042 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq10042
    | (have j0 := eq10042 X0
       grind)
    | exact resolve eq10042 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10042
  have eq10839 : ∀ X0 X1 : G, (M.op (M.op (M.op (τ (τ X0)) X1) (τ (τ X0))) X1) = X1 ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq76 (τ (τ X0)) X1
       have i₂ := eq10043 X0
       grind)
    | exact superpose eq10043 eq76
    | (have j1 := eq10043 X0
       grind)
    | exact resolve eq76 eq10043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10902 : ∀ X0 X1 : G, (τ (τ X0)) = (M.op (M.op (τ (τ X0)) (M.op (τ (τ X0)) X1)) (τ (τ X0))) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq533 (τ (τ X0)) (τ (τ X0)) x
       have i₂ := eq10043 X0
       grind)
    | exact superpose eq10043 eq533
    | (have j1 := eq10043 X0
       grind)
    | exact resolve eq533 eq10043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10043
  have eq10942 : ∀ X0 X1 : G, (τ (τ X0)) = (M.op (M.op (τ (τ X0)) X1) (τ (τ X0))) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10902 X0 X1
       have i₂ := eq89 (τ (τ X0)) X1
       grind)
    | exact superpose eq89 eq10902
    | (have j0 := eq10902 X0 X1
       grind)
    | exact resolve eq10902 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10902
  have eq11866 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op (τ (τ X0)) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq10942 eq10839
    | (have j0 := eq10839 X0 X1
       have j1 := eq10942 X0 X1
       grind)
    | exact resolve eq10839 eq10942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10839
  have eq12037 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ (τ X0)) = (M.op X1 (τ (τ X0))) := by
    intro X0 X1
    first
    | exact superpose eq11866 eq10942
    | (have j0 := eq10942 X0 X1
       have j1 := eq11866 X0 X1
       grind)
    | exact resolve eq10942 eq11866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10942 eq11866
  have eq13366 : ∀ X0 X1 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (τ (τ (σ X0))) = (M.op X1 (τ (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (k (σ X0) (σ X0)) X0
       have i₂ := eq12037 (σ X0) X1
       grind)
    | exact superpose eq12037 eq23
    | (have j1 := eq12037 (σ X0) X1
       grind)
    | exact resolve eq23 eq12037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12037
  have eq13414 : ∀ X0 X1 : G, (k (τ (σ X0)) X0) = (k (k (τ (σ X0)) X0) X0) ∨ (τ (τ (σ X0))) = (M.op X1 (τ (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq13366 X1 X1
       have i₂ := eq23 (σ X1) X1
       grind)
    | exact superpose eq23 eq13366
    | (have j0 := eq13366 X0 X1
       grind)
    | exact resolve eq13366 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13366
  have eq13454 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ (τ (σ X0))) = (M.op X1 (τ (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq13414 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13414
    | (have j0 := eq13414 X0 X1
       grind)
    | exact resolve eq13414 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13414
  have eq13490 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ X0) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13454 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13454
    | (have j0 := eq13454 X0 X1
       grind)
    | exact resolve eq13454 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13454
  have eq13564 : ∀ X0 X1 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (τ (σ X0)) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (k (σ X0) (σ X0)) X0
       have i₂ := eq13490 (σ X0) X1
       grind)
    | exact superpose eq13490 eq23
    | (have j1 := eq13490 (σ X0) X1
       grind)
    | exact resolve eq23 eq13490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13490
  have eq13612 : ∀ X0 X1 : G, (k (τ (σ X0)) X0) = (k (k (τ (σ X0)) X0) X0) ∨ (τ (σ X0)) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq13564 X1 X1
       have i₂ := eq23 (σ X1) X1
       grind)
    | exact superpose eq23 eq13564
    | (have j0 := eq13564 X0 X1
       grind)
    | exact resolve eq13564 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13564
  have eq13652 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ (σ X0)) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq13612 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13612
    | (have j0 := eq13612 X0 X1
       grind)
    | exact resolve eq13612 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13612
  have eq13688 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13652 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13652
    | (have j0 := eq13652 X0 X1
       grind)
    | exact resolve eq13652 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13652
  have eq13762 : ∀ X0 X1 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (k (σ X0) (σ X0)) X0
       have i₂ := eq13688 (σ X0) X1
       grind)
    | exact superpose eq13688 eq23
    | (have j1 := eq13688 (σ X0) X1
       grind)
    | exact resolve eq23 eq13688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13688
  have eq13810 : ∀ X0 X1 : G, (k (τ (σ X0)) X0) = (k (k (τ (σ X0)) X0) X0) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13762 X1 X1
       have i₂ := eq23 (σ X1) X1
       grind)
    | exact superpose eq23 eq13762
    | (have j0 := eq13762 X0 X1
       grind)
    | exact resolve eq13762 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq13762
  have eq13850 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13810 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13810
    | (have j0 := eq13810 X0 X1
       grind)
    | exact resolve eq13810 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13810
  have eq19727 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  clear eq2746
  have eq19743 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq19727 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19727
  have eq19758 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq13850 eq19743
    | (have j0 := eq19743 X0
       have j1 := eq13850 X0 (σ X0)
       grind)
    | exact resolve eq19743 eq13850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13850 eq19743
  have eq19792 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq19758 X0
       have i₂ := eq14 X0 X0
       grind)
    | exact superpose eq14 eq19758
    | (have j0 := eq19758 X0
       have j1 := eq14 (σ X0) (σ X0)
       grind)
    | exact resolve eq19758 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19758
  have eq19876 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq19792 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19792
  have eq28257 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq89 (σ X0) (σ X0)
       have i₂ := eq19876 X0
       grind)
    | exact superpose eq19876 eq89
    | (have j1 := eq19876 X0
       grind)
    | exact resolve eq89 eq19876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19876
  have eq31902 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2720 x y
       grind)
    | exact superpose eq2720 eq16
    | (have j1 := eq2720 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq2720 x y
       grind)
    | exact resolve eq16 eq2720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2720
  have eq32090 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq31902
  have eq81132 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq89 (σ y) (σ x)
       have i₂ := eq32090
       grind)
    | exact superpose eq32090 eq89
    | exact resolve eq89 eq32090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32090
  have eq152342 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq81132
       grind)
    | exact superpose eq81132 eq36
    | exact resolve eq36 eq81132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81132
  have eq152643 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k y y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq152342
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq152342
    | exact resolve eq152342 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152342
  have eq152668 : (τ (σ y)) = (k (τ (σ y)) x) ∨ y = (k y y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq152643
       grind)
    | exact superpose eq152643 eq36
    | exact resolve eq36 eq152643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq152766 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq89 (σ x) (σ x)
       have i₂ := eq152643
       grind)
    | exact superpose eq152643 eq89
    | exact resolve eq89 eq152643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152643
  have eq152952 : y = (k y x) ∨ y = (k y y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq152668
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq152668
    | exact resolve eq152668 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152668
  have eq152960 : y = (k y y) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq14 eq152952
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq152952 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152952
  have eq153966 : (σ (M.op x y)) ≠ (σ y) ∨ y = (k y y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq152766
       grind)
    | exact superpose eq152766 eq16
    | exact resolve eq16 eq152766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152766
  have eq154181 : (σ y) ≠ (σ y) ∨ y = (k y y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq152960 eq153966
    | exact resolve eq153966 eq152960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152960 eq153966
  have eq154182 : y = (k y y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq154181
  have eq154286 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14 y y
       have i₂ := eq154182
       grind)
    | exact superpose eq154182 eq14
    | (have j0 := eq14 y y
       grind)
    | exact resolve eq14 eq154182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154182
  have eq154287 : y = (M.op y y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq154286
  have eq154322 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq76 y X0
       have i₂ := eq154287
       grind)
    | exact superpose eq154287 eq76
    | exact resolve eq76 eq154287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq154419 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq533 y y x
       have i₂ := eq154287
       grind)
    | exact superpose eq154287 eq533
    | exact resolve eq533 eq154287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154287
  have eq154583 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq154419 X0
       have i₂ := eq89 y X0
       grind)
    | exact superpose eq89 eq154419
    | exact resolve eq154419 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154419
  have eq156436 : ∀ X0 : G, y = (M.op y x) ∨ (M.op y X0) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq154583 eq154322
    | exact resolve eq154322 eq154583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154322 eq154583
  have eq156460 : ∀ X0 : G, y = (M.op y y) ∨ (M.op y X0) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq89 y x
       have i₂ := eq156436 X0
       grind)
    | exact superpose eq156436 eq89
    | (have j1 := eq156436 y
       grind)
    | exact resolve eq89 eq156436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156436
  have eq157225 : y ≠ y ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have j0 := eq156460 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156460
  have eq157226 : y = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq157225
  have eq157327 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq76 y X0
       have i₂ := eq157226
       grind)
    | exact superpose eq157226 eq76
    | exact resolve eq76 eq157226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq157354 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2721 y
       have i₂ := eq157226
       grind)
    | exact superpose eq157226 eq2721
    | exact resolve eq2721 eq157226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq157424 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq533 y y x
       have i₂ := eq157226
       grind)
    | exact superpose eq157226 eq533
    | exact resolve eq533 eq157226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533 eq157226
  have eq157550 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq157354
  have eq157590 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq157424 X0
       have i₂ := eq89 y X0
       grind)
    | exact superpose eq89 eq157424
    | exact resolve eq157424 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157424
  have eq158141 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq76 (σ y) X0
       have i₂ := eq157550
       grind)
    | exact superpose eq157550 eq76
    | exact resolve eq76 eq157550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq158295 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (M.op (σ y) (M.op (σ y) X0))) (σ y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq2457 (σ y) x (σ y)
       have i₂ := eq157550
       grind)
    | exact superpose eq157550 eq2457
    | exact resolve eq2457 eq157550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2457 eq157550
  have eq158386 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (M.op (σ y) X0)) (σ y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq158295 X0
       have i₂ := eq89 (σ y) (M.op (σ y) X0)
       grind)
    | exact superpose eq89 eq158295
    | exact resolve eq158295 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158295
  have eq158456 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq158386 X0
       have i₂ := eq89 (σ y) X0
       grind)
    | exact superpose eq89 eq158386
    | exact resolve eq158386 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158386
  have eq158791 : ∀ X0 : G, y = (M.op x x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | exact superpose eq157590 eq157327
    | exact resolve eq157327 eq157590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157327
  have eq158794 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq158791 eq157590
    | exact resolve eq157590 eq158791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157590 eq158791
  have eq159044 : ∀ X0 : G, y = (M.op x x) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq158794 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158794
  have eq159129 : ∀ X0 : G, y = (M.op x y) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq89 x x
       have i₂ := eq159044 X0
       grind)
    | exact superpose eq159044 eq89
    | (have j1 := eq159044 x
       grind)
    | exact resolve eq89 eq159044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq159044
  have eq160806 : y ≠ y ∨ y = (M.op x y) := by
    first
    | (have j0 := eq159129 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159129
  have eq160807 : y = (M.op x y) := by grind
  clear eq160806
  have eq160851 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq160807
       grind)
    | exact superpose eq160807 eq16
    | exact resolve eq16 eq160807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160807
  have eq162772 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq158141 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158141
  have eq162858 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq158456 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158456
  have eq173175 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq162858 eq162772
    | exact resolve eq162772 eq162858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162772
  have eq173177 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq173175 eq162858
    | exact resolve eq162858 eq173175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162858 eq173175
  have eq175000 : (σ y) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq160851
       have i₂ := eq173177 (σ x)
       grind)
    | exact superpose eq173177 eq160851
    | (have r₁ := eq160851
       have r₂ := eq173177 (σ x)
       grind)
    | exact resolve eq160851 eq173177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173177
  have eq175045 : y = (M.op x x) := by grind
  clear eq175000
  have eq176753 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq28257 x
       have i₂ := eq175045
       grind)
    | exact superpose eq175045 eq28257
    | (have j0 := eq28257 x
       grind)
    | exact resolve eq28257 eq175045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28257
  have eq177000 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have r₁ := eq176753
       have r₂ := eq160851
       grind)
    | exact resolve eq176753 eq160851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176753
  have eq178785 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = y := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq177000
       grind)
    | exact superpose eq177000 eq36
    | exact resolve eq36 eq177000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq177000
  have eq179104 : x = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq178785
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq178785
    | exact resolve eq178785 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178785
  have eq179202 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq14 x x
       have i₂ := eq179104
       grind)
    | exact superpose eq179104 eq14
    | (have j0 := eq14 x x
       grind)
    | exact resolve eq14 eq179104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179104
  have eq179203 : x = (M.op x x) ∨ x = y := by grind
  clear eq179202
  have eq179221 : x = y ∨ x = y := by
    first
    | (have i₁ := eq179203
       have i₂ := eq175045
       grind)
    | exact superpose eq175045 eq179203
    | exact resolve eq179203 eq175045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179203
  have eq179222 : x = y := by grind
  clear eq179221
  have eq179252 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq160851
       have i₂ := eq179222
       grind)
    | exact superpose eq179222 eq160851
    | exact resolve eq160851 eq179222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160851
  have eq179271 : x = (M.op x x) := by
    first
    | (have i₁ := eq175045
       have i₂ := eq179222
       grind)
    | exact superpose eq179222 eq175045
    | exact resolve eq175045 eq179222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175045 eq179222
  have eq179314 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2721 x
       have i₂ := eq179271
       grind)
    | exact superpose eq179271 eq2721
    | exact resolve eq2721 eq179271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2721 eq179271
  have eq179520 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq179314
  have eq179592 : False := by grind
  exact eq179592
