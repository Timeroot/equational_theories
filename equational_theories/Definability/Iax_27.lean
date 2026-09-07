import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation442`: `x = x ◇ (y ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation442 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law442 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law442.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq44 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq11 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X0 X0
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
  have eq50 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq84 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq88 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq84 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq84 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq84 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq84 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq104 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq88 (σ X0) (σ X1)
       grind)
    | exact superpose eq88 eq13
    | exact resolve eq13 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq104 X0 X1
       have i₂ := eq88 X0 X1
       grind)
    | exact superpose eq88 eq104
    | exact resolve eq104 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq104
  have eq1063 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq109 x y
       grind)
    | exact superpose eq109 eq14
    | (have r₁ := eq14
       have r₂ := eq109 x y
       grind)
    | exact resolve eq14 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq1088 : False := by grind
  exact eq1088

/-- `Equation442`: `x = x ◇ (y ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pyx_Equation442 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law442 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law442.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 (M.op X2 X0)))) = X0 := by
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 (M.op X2 X0))) = (M.op (M.op X1 (M.op X1 (M.op X2 X0))) (M.op X3 (M.op X3 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op X1 (M.op X1 (M.op X2 X0))) X3 X0
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X1 X0) X0 X0
       have i₂ := eq8 X0 X0 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq29 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X2 X0))) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2 X1
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq12 X0 (M.op X2 X0)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq12 X1 (τ X0)
       grind)
    | exact superpose eq12 eq17
    | (have j1 := eq12 X1 (τ X0)
       grind)
    | exact resolve eq17 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq17 X1 X0
       grind)
    | exact superpose eq17 eq9
    | exact resolve eq9 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq37
    | exact resolve eq37 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq27 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq27
    | exact resolve eq27 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq27 (τ X0) X1
       grind)
    | exact superpose eq27 eq17
    | (have j1 := eq27 (τ X0) X1
       grind)
    | exact resolve eq17 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq27 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq99 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  have eq101 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq45 X1 X0
       have i₂ := eq12 (σ X1) X0
       grind)
    | exact superpose eq12 eq45
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq45 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq113 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq99 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq99
    | exact resolve eq99 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq126 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X1 X2) (M.op X0 X0)) ∨ (M.op X2 X0) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op X1 X2) X0 X1
       have i₂ := eq29 X2 X0 X1
       grind)
    | exact superpose eq29 eq8
    | (have j1 := eq29 X2 X0 X2
       grind)
    | exact resolve eq8 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq137 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq63 X1 (M.op X0 X1)
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq63
    | (have j0 := eq63 X1 X0
       grind)
    | exact resolve eq63 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq203 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq207 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ (k X0 X1)) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 (σ X1) (σ X0)
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq20
    | (have j1 := eq31 X1 X0
       grind)
    | exact resolve eq20 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq224 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 (σ X1) (σ X1)
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq20
    | (have j1 := eq31 X0 X1
       grind)
    | exact resolve eq20 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq233 : ∀ X0 : G, (σ X0) = (σ (k X0 (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq203 X0
       have i₂ := eq13 X0 (k X0 X0)
       grind)
    | exact superpose eq13 eq203
    | (have j0 := eq203 X0
       grind)
    | exact resolve eq203 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq244 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq113 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq113
    | (have j1 := eq31 X0 X1
       grind)
    | exact resolve eq113 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq263 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq244 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq244
    | (have j0 := eq244 X0 X1
       grind)
    | exact resolve eq244 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244
  have eq338 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X3 X2)) = (M.op (M.op X3 (M.op X3 X2)) (M.op X4 (M.op X4 (M.op X0 (M.op X0 (M.op X1 X2)))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 (M.op X3 (M.op X3 X2)) X4 (M.op X0 (M.op X0 (M.op X1 X2)))
       have i₂ := eq18 X2 X0 X1 X3
       grind)
    | exact superpose eq18 eq8
    | exact resolve eq8 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq681 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq40 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq40
    | exact resolve eq40 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq765 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq681 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq681
    | (have j0 := eq681 X0 X1
       grind)
    | exact resolve eq681 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681
  have eq790 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq60 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq60
    | exact resolve eq60 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq837 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq790 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq790
    | (have j0 := eq790 X0 X1
       grind)
    | exact resolve eq790 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq790
  have eq1116 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ (k X0 X1)) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 (σ X0) (σ X1)
       have i₂ := eq57 X0 X1
       grind)
    | exact superpose eq57 eq20
    | (have j1 := eq57 X0 X1
       grind)
    | exact resolve eq20 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq1454 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (k (τ X0) (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq16 X0 (k (τ X0) (τ X0))
       have i₂ := eq233 (τ X0)
       grind)
    | exact superpose eq233 eq16
    | (have j1 := eq233 (τ X0)
       grind)
    | exact resolve eq16 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq233
  have eq1492 : ∀ X0 : G, (σ (τ X0)) = (k X0 (k (σ (τ X0)) X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1454 X0
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq1454
    | (have j0 := eq1454 X0
       grind)
    | exact resolve eq1454 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1454
  have eq1498 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1492 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1492
    | (have j0 := eq1492 X0
       grind)
    | exact resolve eq1492 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1492
  have eq1501 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1498 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1498
    | (have j0 := eq1498 X0
       grind)
    | exact resolve eq1498 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1498
  have eq1876 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  clear eq126
  have eq2154 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq224 x y
       grind)
    | exact superpose eq224 eq14
    | (have j1 := eq224 x y
       grind)
    | exact resolve eq14 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2181 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq224 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq2951 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ (k X0 X1))) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq207 (τ X1) (τ X0)
       have i₂ := eq48 X0 X1
       grind)
    | exact superpose eq48 eq207
    | (have j0 := eq207 (τ X0) (τ X1)
       grind)
    | exact resolve eq207 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq3011 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ (k X0 X1))) X0) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2951 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2951
    | (have j0 := eq2951 X0 X1
       grind)
    | exact resolve eq2951 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2951
  have eq3016 : ∀ X0 X1 : G, (k X0 X1) = (M.op (k X0 X1) X0) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3011 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq3011
    | (have j0 := eq3011 X0 X1
       grind)
    | exact resolve eq3011 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3011
  have eq3017 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (τ X1)) ∨ (k X0 X1) = (M.op (k X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3016 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3016
    | (have j0 := eq3016 X0 X1
       grind)
    | exact resolve eq3016 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3016
  have eq3018 : ∀ X0 X1 : G, (k X0 X1) = (M.op (k X0 X1) X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3017 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq3017
    | (have j0 := eq3017 X0 X1
       grind)
    | exact resolve eq3017 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3017
  have eq5315 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2181 (τ X1) (τ X0)
       have i₂ := eq48 X1 X0
       grind)
    | exact superpose eq48 eq2181
    | (have j0 := eq2181 (τ X1) (τ X0)
       grind)
    | exact resolve eq2181 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq5339 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5315 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq5315
    | (have j0 := eq5315 X0 X1
       grind)
    | exact resolve eq5315 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5315
  have eq5347 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5339 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq5339
    | (have j0 := eq5339 X0 X1
       grind)
    | exact resolve eq5339 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5339
  have eq5350 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5347 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5347
    | (have j0 := eq5347 X0 X1
       grind)
    | exact resolve eq5347 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5347
  have eq5351 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5350 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5350
    | (have j0 := eq5350 X0 X1
       grind)
    | exact resolve eq5350 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5350
  have eq7622 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X1)) = (M.op (M.op X2 (M.op X2 X1)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq338 (M.op X0 X1) X0 X1 X2 (M.op X0 X1)
       have i₂ := eq8 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq8 eq338
    | exact resolve eq338 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq7717 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7622 X0 (M.op X1 (M.op X2 X1)) X1
       have i₂ := eq8 X1 X1 X2
       grind)
    | exact superpose eq8 eq7622
    | exact resolve eq7622 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7622
  have eq8443 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq263 x y
       grind)
    | exact superpose eq263 eq14
    | (have j1 := eq263 x y
       grind)
    | exact resolve eq14 eq263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8503 : y = (k y x) := by
    first
    | (have j1 := eq837 x y
       grind)
    | (have r₁ := eq8443
       have r₂ := eq837 x y
       grind)
    | exact resolve eq8443 eq837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq837 eq8443
  have eq9121 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq765 x y
       have i₂ := eq8503
       grind)
    | exact superpose eq8503 eq765
    | (have j0 := eq765 x y
       grind)
    | exact resolve eq765 eq8503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9123 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2181 x y
       have i₂ := eq8503
       grind)
    | exact superpose eq8503 eq2181
    | (have j0 := eq2181 x y
       grind)
    | exact resolve eq2181 eq8503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9124 : y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq3018 y x
       have i₂ := eq8503
       grind)
    | exact superpose eq8503 eq3018
    | (have j0 := eq3018 y y
       grind)
    | exact resolve eq3018 eq8503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11361 : y ≠ y ∨ y = (k y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq137 y y
       have i₂ := eq9124
       grind)
    | exact superpose eq9124 eq137
    | (have r₁ := eq137 y y
       have r₂ := eq9124
       grind)
    | exact resolve eq137 eq9124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq11374 : x ≠ y ∨ x = (M.op y y) := by grind
  clear eq9124
  have eq11375 : y = (k y y) ∨ x = (M.op y y) := by grind
  clear eq11361
  have eq12388 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2181 y y
       have i₂ := eq11375
       grind)
    | exact superpose eq11375 eq2181
    | (have j0 := eq2181 y y
       grind)
    | exact resolve eq2181 eq11375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2181 eq11375
  have eq12393 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq12388
  have eq44527 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2154
       have i₂ := eq765 x y
       grind)
    | exact superpose eq765 eq2154
    | (have j1 := eq765 x y
       grind)
    | (have r₁ := eq2154
       have r₂ := eq765 x y
       grind)
    | exact resolve eq2154 eq765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765 eq2154
  have eq44535 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq44527
  have eq44552 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq44535
       grind)
    | exact superpose eq44535 eq14
    | exact resolve eq14 eq44535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44566 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq101 (σ x) y
       have i₂ := eq44535
       grind)
    | exact superpose eq44535 eq101
    | (have j0 := eq101 (σ x) y
       grind)
    | exact resolve eq101 eq44535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq44535
  have eq44676 : x = (k y x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq44566
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq44566
    | exact resolve eq44566 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44566
  have eq44694 : x = y ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq44676
       have i₂ := eq8503
       grind)
    | exact superpose eq8503 eq44676
    | exact resolve eq44676 eq8503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8503 eq44676
  have eq44698 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq44694
       have r₂ := eq11374
       grind)
    | exact resolve eq44694 eq11374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11374 eq44694
  have eq44997 : (σ x) ≠ (σ y) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq44552
       have i₂ := eq9121
       grind)
    | exact superpose eq9121 eq44552
    | exact resolve eq44552 eq9121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9121 eq44552
  have eq44999 : (σ x) ≠ (σ y) ∨ x = (M.op y y) := by grind
  clear eq44997
  have eq46579 : (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq12393
       have i₂ := eq44698
       grind)
    | exact superpose eq44698 eq12393
    | exact resolve eq12393 eq44698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12393 eq44698
  have eq46742 : (σ x) = (σ y) ∨ x = (M.op y y) := by grind
  clear eq46579
  have eq46777 : x = (M.op y y) := by
    first
    | (have r₁ := eq46742
       have r₂ := eq44999
       grind)
    | exact resolve eq46742 eq44999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44999 eq46742
  have eq47553 : x = (k y y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq1876 y
       have i₂ := eq46777
       grind)
    | exact superpose eq46777 eq1876
    | exact resolve eq1876 eq46777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1876
  have eq47560 : ∀ X0 : G, y = (M.op y (M.op X0 (M.op X0 x))) := by
    intro X0
    first
    | (have i₁ := eq8 y X0 y
       have i₂ := eq46777
       grind)
    | exact superpose eq46777 eq8
    | exact resolve eq8 eq46777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47564 : x = (M.op x y) := by
    first
    | (have i₁ := eq20 y y
       have i₂ := eq46777
       grind)
    | exact superpose eq46777 eq20
    | exact resolve eq20 eq46777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq47568 : x ≠ y ∨ y = (k y y) := by
    first
    | (have i₁ := eq63 y y
       have i₂ := eq46777
       grind)
    | exact superpose eq46777 eq63
    | (have j0 := eq63 y y
       grind)
    | exact resolve eq63 eq46777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq47650 : ∀ X0 : G, y = (M.op y (M.op X0 (M.op y x))) := by
    intro X0
    first
    | (have i₁ := eq7717 y y X0
       have i₂ := eq46777
       grind)
    | exact superpose eq46777 eq7717
    | exact resolve eq7717 eq46777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7717
  have eq51224 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq1116 y y
       have i₂ := eq47553
       grind)
    | exact superpose eq47553 eq1116
    | exact resolve eq1116 eq47553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47553
  have eq51236 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
    first
    | (have r₁ := eq51224
       have r₂ := eq9123
       grind)
    | exact resolve eq51224 eq9123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51224
  have eq63169 : (σ (M.op x y)) ≠ (σ x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq51236
       grind)
    | exact superpose eq51236 eq14
    | exact resolve eq14 eq51236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51236
  have eq63306 : (σ x) ≠ (σ x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq63169
       have i₂ := eq47564
       grind)
    | exact superpose eq47564 eq63169
    | exact resolve eq63169 eq47564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63169
  have eq63307 : x = (k x x) := by grind
  clear eq63306
  have eq64062 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq5351 x x
       have i₂ := eq63307
       grind)
    | exact superpose eq63307 eq5351
    | (have j0 := eq5351 x x
       grind)
    | (have r₁ := eq5351 x x
       have r₂ := eq63307
       grind)
    | exact resolve eq5351 eq63307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5351 eq63307
  have eq64067 : x = (M.op x x) := by grind
  clear eq64062
  have eq64743 : y = (M.op y (M.op x x)) := by
    first
    | (have i₁ := eq47560 x
       have i₂ := eq64067
       grind)
    | exact superpose eq64067 eq47560
    | exact resolve eq47560 eq64067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47560
  have eq64910 : y = (M.op y x) := by
    first
    | (have i₁ := eq64743
       have i₂ := eq64067
       grind)
    | exact superpose eq64067 eq64743
    | exact resolve eq64743 eq64067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64067 eq64743
  have eq65328 : ∀ X0 : G, y = (M.op y (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq47650 X0
       have i₂ := eq64910
       grind)
    | exact superpose eq64910 eq47650
    | exact resolve eq47650 eq64910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47650 eq64910
  have eq68197 : ∀ X0 : G, y = (M.op y (k y X0)) ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq65328 (k y X0)
       have i₂ := eq3018 y X0
       grind)
    | exact superpose eq3018 eq65328
    | (have j1 := eq3018 y X0
       grind)
    | exact resolve eq65328 eq3018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3018 eq65328
  have eq68424 : ∀ X0 : G, y = (M.op y (k y X0)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq68197 X0
       have i₂ := eq46777
       grind)
    | exact superpose eq46777 eq68197
    | (have j0 := eq68197 X0
       grind)
    | exact resolve eq68197 eq46777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68197
  have eq81832 : y = (M.op y y) ∨ x = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq68424 (τ (M.op (σ y) (σ y)))
       have i₂ := eq113 y
       grind)
    | exact superpose eq113 eq68424
    | (have j0 := eq68424 (τ (M.op (σ y) (σ y)))
       grind)
    | exact resolve eq68424 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq81839 : y = (M.op y y) ∨ x = (k y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq68424 (k y y)
       have i₂ := eq1501 y
       grind)
    | exact superpose eq1501 eq68424
    | (have j0 := eq68424 (k y y)
       have j1 := eq1501 y
       grind)
    | exact resolve eq68424 eq1501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1501 eq68424
  have eq81937 : y = (M.op y y) ∨ x = (k y y) := by grind
  clear eq81839
  have eq81969 : x = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq81937
       have i₂ := eq46777
       grind)
    | exact superpose eq46777 eq81937
    | exact resolve eq81937 eq46777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81937
  have eq81976 : x = (τ (M.op (σ y) (σ y))) ∨ x = y := by
    first
    | (have i₁ := eq81832
       have i₂ := eq46777
       grind)
    | exact superpose eq46777 eq81832
    | exact resolve eq81832 eq46777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46777 eq81832
  have eq92316 : x = (τ (σ (k y y))) ∨ x = y ∨ y = (k y y) := by
    first
    | (have i₁ := eq81976
       have i₂ := eq263 y y
       grind)
    | exact superpose eq263 eq81976
    | (have j1 := eq263 y y
       grind)
    | exact resolve eq81976 eq263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263 eq81976
  have eq92480 : x = (τ (σ (k y y))) ∨ y = (k y y) := by
    first
    | (have r₁ := eq92316
       have r₂ := eq47568
       grind)
    | exact resolve eq92316 eq47568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47568 eq92316
  have eq92492 : y = (k y y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq92480
       have i₂ := eq9 (k y y)
       grind)
    | exact superpose eq9 eq92480
    | exact resolve eq92480 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92480
  have eq92895 : x ≠ y ∨ x = (k y y) := by grind
  clear eq92492
  have eq92918 : x = (k y y) := by
    first
    | (have r₁ := eq92895
       have r₂ := eq81969
       grind)
    | exact resolve eq92895 eq81969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81969 eq92895
  have eq93363 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1116 y y
       have i₂ := eq92918
       grind)
    | exact superpose eq92918 eq1116
    | exact resolve eq1116 eq92918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1116 eq92918
  have eq93379 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq93363
       have r₂ := eq9123
       grind)
    | exact resolve eq93363 eq9123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9123 eq93363
  have eq93845 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq93379
       grind)
    | exact superpose eq93379 eq14
    | exact resolve eq14 eq93379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93379
  have eq93938 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq93845
       have i₂ := eq47564
       grind)
    | exact superpose eq47564 eq93845
    | exact resolve eq93845 eq47564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47564 eq93845
  have eq93939 : False := by grind
  exact eq93939

/-- `Equation442`: `x = x ◇ (y ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_x_y_pxy_Equation442 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law442 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law442.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 (M.op X2 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 (M.op X2 X0))) = (M.op (M.op X1 (M.op X1 (M.op X2 X0))) (M.op X3 (M.op X3 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op X1 (M.op X1 (M.op X2 X0))) X3 X0
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X1 X0) X0 X0
       have i₂ := eq8 X0 X0 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq29 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X2 X0))) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq12 (M.op X2 X0) X1
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq16
    | (have j1 := eq12 (τ X0) X1
       grind)
    | exact resolve eq16 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq36 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq36
    | exact resolve eq36 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    grind
  have eq53 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq36 X0 X1
       have i₂ := eq12 X0 (σ X1)
       grind)
    | exact superpose eq12 eq36
    | (have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq36 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq58 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq51 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq51
    | exact resolve eq51 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq59 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq27 (σ X0) (σ X1)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq27
    | exact resolve eq27 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq27 (τ X0) X1
       grind)
    | exact superpose eq27 eq16
    | (have j1 := eq27 (τ X0) X1
       grind)
    | exact resolve eq16 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq65 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq27 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq126 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X1 X2) (M.op X0 X0)) ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op X1 X2) X0 X1
       have i₂ := eq29 X2 X0 X1
       grind)
    | exact superpose eq29 eq8
    | (have j1 := eq29 X2 X0 X2
       grind)
    | exact resolve eq8 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq137 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k (M.op X0 X1) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq65 (M.op X0 X1) X1
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq65
    | (have j0 := eq65 X0 X1
       grind)
    | exact resolve eq65 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq203 : ∀ X0 : G, (σ X0) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq207 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ (k X0 X1)) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 (σ X1) (σ X0)
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq20
    | (have j1 := eq31 X0 X1
       grind)
    | exact resolve eq20 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq224 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 (σ X1) (σ X1)
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq20
    | (have j1 := eq31 X0 X1
       grind)
    | exact resolve eq20 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq233 : ∀ X0 : G, (σ X0) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq203 X0
       have i₂ := eq13 (k X0 X0) X0
       grind)
    | exact superpose eq13 eq203
    | (have j0 := eq203 X0
       grind)
    | exact resolve eq203 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq244 : ∀ X0 X1 : G, (k (τ (σ X0)) X1) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq58 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq58
    | (have j1 := eq31 X0 X1
       grind)
    | exact resolve eq58 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq263 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq244 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq244
    | (have j0 := eq244 X0 X1
       grind)
    | exact resolve eq244 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244
  have eq338 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X3 X2)) = (M.op (M.op X3 (M.op X3 X2)) (M.op X4 (M.op X4 (M.op X0 (M.op X0 (M.op X1 X2)))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 (M.op X3 (M.op X3 X2)) X4 (M.op X0 (M.op X0 (M.op X1 X2)))
       have i₂ := eq18 X2 X0 X1 X3
       grind)
    | exact superpose eq18 eq8
    | exact resolve eq8 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq681 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq33 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq33
    | exact resolve eq33 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq765 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq681 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq681
    | (have j0 := eq681 X0 X1
       grind)
    | exact resolve eq681 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681
  have eq790 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq64 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq64
    | exact resolve eq64 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq837 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq790 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq790
    | (have j0 := eq790 X0 X1
       grind)
    | exact resolve eq790 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq790
  have eq1116 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ (k X0 X1)) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20 (σ X1) (σ X0)
       have i₂ := eq59 X0 X1
       grind)
    | exact superpose eq59 eq20
    | (have j1 := eq59 X0 X1
       grind)
    | exact resolve eq20 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq1454 : ∀ X0 : G, (σ (τ X0)) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (k (τ X0) (τ X0))
       have i₂ := eq233 (τ X0)
       grind)
    | exact superpose eq233 eq17
    | (have j1 := eq233 (τ X0)
       grind)
    | exact resolve eq17 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq1492 : ∀ X0 : G, (σ (τ X0)) = (k (k (σ (τ X0)) X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1454 X0
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq1454
    | (have j0 := eq1454 X0
       grind)
    | exact resolve eq1454 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1454
  have eq1498 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1492 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1492
    | (have j0 := eq1492 X0
       grind)
    | exact resolve eq1492 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1492
  have eq1501 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1498 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1498
    | (have j0 := eq1498 X0
       grind)
    | exact resolve eq1498 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1498
  have eq1879 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  clear eq126
  have eq2200 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq224 x y
       grind)
    | exact superpose eq224 eq14
    | (have j1 := eq224 x y
       grind)
    | exact resolve eq14 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2227 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq224 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq3108 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ (k X0 X1))) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq207 (τ X1) (τ X0)
       have i₂ := eq48 X0 X1
       grind)
    | exact superpose eq48 eq207
    | (have j0 := eq207 (τ X0) (τ X1)
       grind)
    | exact resolve eq207 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq3174 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ (k X0 X1))) X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3108 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq3108
    | (have j0 := eq3108 X0 X1
       grind)
    | exact resolve eq3108 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3108
  have eq3176 : ∀ X0 X1 : G, (k X0 X1) = (M.op (k X0 X1) X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3174 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq3174
    | (have j0 := eq3174 X0 X1
       grind)
    | exact resolve eq3174 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3174
  have eq3177 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (k X0 X1) = (M.op (k X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3176 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3176
    | (have j0 := eq3176 X0 X1
       grind)
    | exact resolve eq3176 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3176
  have eq3178 : ∀ X0 X1 : G, (k X0 X1) = (M.op (k X0 X1) X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3177 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3177
    | (have j0 := eq3177 X0 X1
       grind)
    | exact resolve eq3177 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3177
  have eq4918 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2227 (τ X0) (τ X1)
       have i₂ := eq48 X1 X0
       grind)
    | exact superpose eq48 eq2227
    | (have j0 := eq2227 (τ X0) (τ X1)
       grind)
    | exact resolve eq2227 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq4951 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq4918 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq4918
    | (have j0 := eq4918 X0 X1
       grind)
    | exact resolve eq4918 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4918
  have eq4956 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq4951 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4951
    | (have j0 := eq4951 X0 X1
       grind)
    | exact resolve eq4951 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4951
  have eq4957 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4956 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq4956
    | (have j0 := eq4956 X0 X1
       grind)
    | exact resolve eq4956 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4956
  have eq4958 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4957 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4957
    | (have j0 := eq4957 X0 X1
       grind)
    | exact resolve eq4957 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4957
  have eq7200 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq263 x y
       grind)
    | exact superpose eq263 eq14
    | (have j1 := eq263 x y
       grind)
    | exact resolve eq14 eq263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7246 : y = (k x y) := by
    first
    | (have j1 := eq837 x y
       grind)
    | (have r₁ := eq7200
       have r₂ := eq837 x y
       grind)
    | exact resolve eq7200 eq837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq837 eq7200
  have eq7425 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq765 x y
       have i₂ := eq7246
       grind)
    | exact superpose eq7246 eq765
    | (have j0 := eq765 x y
       grind)
    | exact resolve eq765 eq7246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7427 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2227 x y
       have i₂ := eq7246
       grind)
    | exact superpose eq7246 eq2227
    | (have j0 := eq2227 x y
       grind)
    | exact resolve eq2227 eq7246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7428 : y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq3178 x y
       have i₂ := eq7246
       grind)
    | exact superpose eq7246 eq3178
    | (have j0 := eq3178 y y
       grind)
    | exact resolve eq3178 eq7246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7573 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X1)) = (M.op (M.op X2 (M.op X2 X1)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq338 (M.op X0 X1) X0 X1 X2 (M.op X0 X1)
       have i₂ := eq8 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq8 eq338
    | exact resolve eq338 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq8763 : y ≠ y ∨ y = (k y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq137 y y
       have i₂ := eq7428
       grind)
    | exact superpose eq7428 eq137
    | (have r₁ := eq137 y y
       have r₂ := eq7428
       grind)
    | exact resolve eq137 eq7428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq8771 : x ≠ y ∨ x = (M.op y y) := by grind
  clear eq7428
  have eq8772 : y = (k y y) ∨ x = (M.op y y) := by grind
  clear eq8763
  have eq10937 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2227 y y
       have i₂ := eq8772
       grind)
    | exact superpose eq8772 eq2227
    | (have j0 := eq2227 y y
       grind)
    | exact resolve eq2227 eq8772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2227 eq8772
  have eq10942 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq10937
  have eq17995 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7573 X0 (M.op X1 (M.op X2 X1)) X1
       have i₂ := eq8 X1 X1 X2
       grind)
    | exact superpose eq8 eq7573
    | exact resolve eq7573 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7573
  have eq44633 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2200
       have i₂ := eq765 x y
       grind)
    | exact superpose eq765 eq2200
    | (have j1 := eq765 x y
       grind)
    | (have r₁ := eq2200
       have r₂ := eq765 x y
       grind)
    | exact resolve eq2200 eq765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765 eq2200
  have eq44641 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq44633
  have eq44660 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq44641
       grind)
    | exact superpose eq44641 eq14
    | exact resolve eq14 eq44641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44672 : (τ (σ x)) = (k (τ (σ x)) y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq53 (σ x) y
       have i₂ := eq44641
       grind)
    | exact superpose eq44641 eq53
    | (have j0 := eq53 (σ x) y
       grind)
    | exact resolve eq53 eq44641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq44641
  have eq44784 : x = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq44672
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq44672
    | exact resolve eq44672 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44672
  have eq44802 : x = y ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq44784
       have i₂ := eq7246
       grind)
    | exact superpose eq7246 eq44784
    | exact resolve eq44784 eq7246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7246 eq44784
  have eq44806 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq44802
       have r₂ := eq8771
       grind)
    | exact resolve eq44802 eq8771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8771 eq44802
  have eq45100 : (σ x) ≠ (σ y) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq44660
       have i₂ := eq7425
       grind)
    | exact superpose eq7425 eq44660
    | exact resolve eq44660 eq7425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7425 eq44660
  have eq45102 : (σ x) ≠ (σ y) ∨ x = (M.op y y) := by grind
  clear eq45100
  have eq46684 : (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10942
       have i₂ := eq44806
       grind)
    | exact superpose eq44806 eq10942
    | exact resolve eq10942 eq44806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10942 eq44806
  have eq46845 : (σ x) = (σ y) ∨ x = (M.op y y) := by grind
  clear eq46684
  have eq46878 : x = (M.op y y) := by
    first
    | (have r₁ := eq46845
       have r₂ := eq45102
       grind)
    | exact resolve eq46845 eq45102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45102 eq46845
  have eq47654 : x = (k y y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq1879 y
       have i₂ := eq46878
       grind)
    | exact superpose eq46878 eq1879
    | exact resolve eq1879 eq46878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1879
  have eq47659 : ∀ X0 : G, y = (M.op y (M.op X0 (M.op X0 x))) := by
    intro X0
    first
    | (have i₁ := eq8 y X0 y
       have i₂ := eq46878
       grind)
    | exact superpose eq46878 eq8
    | exact resolve eq8 eq46878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47663 : x = (M.op x y) := by
    first
    | (have i₁ := eq20 y y
       have i₂ := eq46878
       grind)
    | exact superpose eq46878 eq20
    | exact resolve eq20 eq46878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq47667 : x ≠ y ∨ y = (k y y) := by
    first
    | (have i₁ := eq65 y y
       have i₂ := eq46878
       grind)
    | exact superpose eq46878 eq65
    | (have j0 := eq65 y y
       grind)
    | exact resolve eq65 eq46878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq47749 : ∀ X0 : G, y = (M.op y (M.op X0 (M.op y x))) := by
    intro X0
    first
    | (have i₁ := eq17995 y y X0
       have i₂ := eq46878
       grind)
    | exact superpose eq46878 eq17995
    | exact resolve eq17995 eq46878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17995
  have eq51461 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq1116 y y
       have i₂ := eq47654
       grind)
    | exact superpose eq47654 eq1116
    | exact resolve eq1116 eq47654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47654
  have eq51473 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
    first
    | (have r₁ := eq51461
       have r₂ := eq7427
       grind)
    | exact resolve eq51461 eq7427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51461
  have eq62892 : (σ (M.op x y)) ≠ (σ x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq51473
       grind)
    | exact superpose eq51473 eq14
    | exact resolve eq14 eq51473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51473
  have eq63030 : (σ x) ≠ (σ x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq62892
       have i₂ := eq47663
       grind)
    | exact superpose eq47663 eq62892
    | exact resolve eq62892 eq47663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62892
  have eq63031 : x = (k x x) := by grind
  clear eq63030
  have eq63262 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq4958 x x
       have i₂ := eq63031
       grind)
    | exact superpose eq63031 eq4958
    | (have j0 := eq4958 x x
       grind)
    | (have r₁ := eq4958 x x
       have r₂ := eq63031
       grind)
    | exact resolve eq4958 eq63031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4958 eq63031
  have eq63267 : x = (M.op x x) := by grind
  clear eq63262
  have eq63649 : y = (M.op y (M.op x x)) := by
    first
    | (have i₁ := eq47659 x
       have i₂ := eq63267
       grind)
    | exact superpose eq63267 eq47659
    | exact resolve eq47659 eq63267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47659
  have eq63813 : y = (M.op y x) := by
    first
    | (have i₁ := eq63649
       have i₂ := eq63267
       grind)
    | exact superpose eq63267 eq63649
    | exact resolve eq63649 eq63267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63267 eq63649
  have eq64372 : ∀ X0 : G, y = (M.op y (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq47749 X0
       have i₂ := eq63813
       grind)
    | exact superpose eq63813 eq47749
    | exact resolve eq47749 eq63813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47749 eq63813
  have eq66862 : ∀ X0 : G, y = (M.op y (k X0 y)) ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq64372 (k X0 y)
       have i₂ := eq3178 X0 y
       grind)
    | exact superpose eq3178 eq64372
    | (have j1 := eq3178 X0 y
       grind)
    | exact resolve eq64372 eq3178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3178 eq64372
  have eq67092 : ∀ X0 : G, y = (M.op y (k X0 y)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq66862 X0
       have i₂ := eq46878
       grind)
    | exact superpose eq46878 eq66862
    | (have j0 := eq66862 X0
       grind)
    | exact resolve eq66862 eq46878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66862
  have eq78855 : y = (M.op y y) ∨ x = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq67092 (τ (M.op (σ y) (σ y)))
       have i₂ := eq58 y
       grind)
    | exact superpose eq58 eq67092
    | (have j0 := eq67092 (τ (M.op (σ y) (σ y)))
       grind)
    | exact resolve eq67092 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq78863 : y = (M.op y y) ∨ x = (k y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq67092 (k y y)
       have i₂ := eq1501 y
       grind)
    | exact superpose eq1501 eq67092
    | (have j0 := eq67092 (k y y)
       have j1 := eq1501 y
       grind)
    | exact resolve eq67092 eq1501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1501 eq67092
  have eq78967 : y = (M.op y y) ∨ x = (k y y) := by grind
  clear eq78863
  have eq79000 : x = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq78967
       have i₂ := eq46878
       grind)
    | exact superpose eq46878 eq78967
    | exact resolve eq78967 eq46878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78967
  have eq79008 : x = (τ (M.op (σ y) (σ y))) ∨ x = y := by
    first
    | (have i₁ := eq78855
       have i₂ := eq46878
       grind)
    | exact superpose eq46878 eq78855
    | exact resolve eq78855 eq46878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46878 eq78855
  have eq92003 : x = (τ (σ (k y y))) ∨ x = y ∨ y = (k y y) := by
    first
    | (have i₁ := eq79008
       have i₂ := eq263 y y
       grind)
    | exact superpose eq263 eq79008
    | (have j1 := eq263 y y
       grind)
    | exact resolve eq79008 eq263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263 eq79008
  have eq92166 : x = (τ (σ (k y y))) ∨ y = (k y y) := by
    first
    | (have r₁ := eq92003
       have r₂ := eq47667
       grind)
    | exact resolve eq92003 eq47667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47667 eq92003
  have eq92177 : y = (k y y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq92166
       have i₂ := eq9 (k y y)
       grind)
    | exact superpose eq9 eq92166
    | exact resolve eq92166 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92166
  have eq92881 : x ≠ y ∨ x = (k y y) := by grind
  clear eq92177
  have eq92904 : x = (k y y) := by
    first
    | (have r₁ := eq92881
       have r₂ := eq79000
       grind)
    | exact resolve eq92881 eq79000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79000 eq92881
  have eq93048 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1116 y y
       have i₂ := eq92904
       grind)
    | exact superpose eq92904 eq1116
    | exact resolve eq1116 eq92904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1116 eq92904
  have eq93064 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq93048
       have r₂ := eq7427
       grind)
    | exact resolve eq93048 eq7427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7427 eq93048
  have eq93663 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq93064
       grind)
    | exact superpose eq93064 eq14
    | exact resolve eq14 eq93064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93064
  have eq93855 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq93663
       have i₂ := eq47663
       grind)
    | exact superpose eq47663 eq93663
    | exact resolve eq93663 eq47663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47663 eq93663
  have eq93856 : False := by grind
  exact eq93856

/-- `Equation4423`: `x ◇ (x ◇ y) = (z ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_x_pyx_Equation4423 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4423 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4423.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X2) X0) := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq15 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : ∀ X0 X1 X3 : G, (M.op (M.op X3 X3) X1) = (M.op X1 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq8 X1 (M.op X1 x) X3
       have i₂ := eq8 X1 x X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X3 X3) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq8 X1 x X3
       have i₂ := eq8 X1 x X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq8 X0 X2 x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq9
    | exact resolve eq9 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X1 (M.op X1 X2)) ∨ (k X3 X0) = (M.op X0 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 X2 X0
       have i₂ := eq12 X3 X0
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X3 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X1 X0
       have i₂ := eq12 X2 X0
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X1 X0
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 X1) X0) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X0 X1
       have i₂ := eq12 X2 X0
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X2 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 X0 (σ X0)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq27 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq38 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq16 X1 X0
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) (M.op X2 X2)) = (M.op (M.op X2 X2) (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op X2 X2) X1 X3
       have i₂ := eq19 X2 X1 X0
       grind)
    | (have i₁ := eq8 (M.op X2 X2) X1 X3
       have i₂ := eq19 X0 X1 X2
       grind)
    | exact superpose eq19 eq8
    | exact resolve eq8 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq24
    | exact resolve eq24 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op (M.op X0 X0) X1)) = (M.op (M.op X2 X2) (M.op (M.op X2 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq20 (M.op X2 X2) X3 X1
       have i₂ := eq19 X2 X1 X0
       grind)
    | (have i₁ := eq20 (M.op X2 X2) X3 X1
       have i₂ := eq19 X0 X1 X2
       grind)
    | exact superpose eq19 eq20
    | exact resolve eq20 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq134 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X2 (σ X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq31 (σ X0) X2 (σ X1)
       grind)
    | exact superpose eq31 eq13
    | (have j1 := eq31 (σ X0) X2 X2
       grind)
    | exact resolve eq13 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq31 X1 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) ≠ X0 ∨ (k X0 (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq139 X0 (M.op X2 X2)
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq139
    | (have j0 := eq139 X0 (M.op X2 X2)
       grind)
    | (have r₁ := eq139 (M.op (M.op X2 X2) (M.op X2 X2)) (M.op X2 X2)
       have r₂ := eq8 (M.op X2 X2) (M.op X2 X2) X2
       grind)
    | exact resolve eq139 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq159 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) X3) = (M.op X3 (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq17 (M.op X1 X1) X3 X2
       have i₂ := eq19 X1 (M.op X1 X1) X0
       grind)
    | (have i₁ := eq17 (M.op X1 X1) X3 X2
       have i₂ := eq19 X0 (M.op X1 X1) X1
       grind)
    | exact superpose eq19 eq17
    | exact resolve eq17 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) ≠ (M.op (M.op X2 X2) X1) ∨ (M.op (M.op X2 X2) X1) = (k (M.op (M.op X2 X2) X1) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq139 (M.op (M.op X2 X2) X1) X1
       have i₂ := eq17 X2 X1 X0
       grind)
    | exact superpose eq17 eq139
    | (have j0 := eq139 (M.op (M.op X2 X2) X1) X1
       grind)
    | (have r₁ := eq139 (M.op (M.op x x) X1) X1
       have r₂ := eq17 x X1 x
       grind)
    | exact resolve eq139 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (M.op (M.op X3 X3) (M.op (M.op X2 X2) (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 X1 (M.op (M.op X2 X2) (M.op X1 X1)) X3
       have i₂ := eq17 X2 (M.op X1 X1) X0
       grind)
    | exact superpose eq17 eq19
    | exact resolve eq19 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq191 : ∀ X1 X2 : G, (M.op (M.op X2 X2) X1) = (k (M.op (M.op X2 X2) X1) X1) := by
    intro X1 X2
    first
    | (have j0 := eq185 x X1 X2
       grind)
    | (have r₁ := eq185 x X1 x
       have r₂ := eq19 x X1 x
       grind)
    | (have r₁ := eq185 x X1 x
       have r₂ := eq19 x X1 x
       grind)
    | exact resolve eq185 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq380 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 (M.op X1 X1)) = X0 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq139 X0 (M.op X1 X1)
       have i₂ := eq28 X0 X1 X2
       grind)
    | (have i₁ := eq139 X0 X0
       have i₂ := eq28 X0 X1 X2
       grind)
    | exact superpose eq28 eq139
    | (have j0 := eq139 X0 X0
       have j1 := eq28 X0 X1 X2
       grind)
    | exact resolve eq139 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq139
  have eq388 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 X1)) = X0 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq380 X0 X1 X2
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq380 X1 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq380 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380
  have eq598 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq29 x y
       grind)
    | exact superpose eq29 eq14
    | (have j1 := eq29 x x
       grind)
    | exact resolve eq14 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq600 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (σ X0)
       have i₂ := eq29 X0 X0
       grind)
    | exact superpose eq29 eq11
    | (have j0 := eq11 X1 (σ X0)
       have j1 := eq29 X0 X1
       grind)
    | (have r₁ := eq11 X0 (σ X0)
       have r₂ := eq29 X0 X1
       grind)
    | exact resolve eq11 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq611 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (σ X1)) = (M.op (σ X1) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (σ X1) (σ X0) X2
       have i₂ := eq29 X1 X0
       grind)
    | exact superpose eq29 eq8
    | (have j1 := eq29 X1 X1
       grind)
    | exact resolve eq8 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq637 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq29 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq641 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq600 X0 X1
       have j1 := eq11 X1 (σ X0)
       grind)
    | (have r₁ := eq600 X0 X1
       have r₂ := eq11 X0 (σ X0)
       grind)
    | exact resolve eq600 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600
  have eq658 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq641 (τ X0) X1
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq641
    | (have j0 := eq641 (τ X0) X1
       grind)
    | exact resolve eq641 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641
  have eq662 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq658 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq658
    | (have j0 := eq658 X0 X1
       grind)
    | exact resolve eq658 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq666 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq662 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq662
    | (have j0 := eq662 X0 X1
       grind)
    | exact resolve eq662 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662
  have eq717 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq666 (τ X0) X1
       have i₂ := eq69 X0 X0
       grind)
    | exact superpose eq69 eq666
    | (have j0 := eq666 (τ X0) X1
       grind)
    | exact resolve eq666 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666
  have eq2001 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq637 (τ X0)
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq637
    | (have j0 := eq637 (τ X0)
       grind)
    | exact resolve eq637 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637
  have eq2010 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2001 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2001
    | (have j0 := eq2001 X0
       grind)
    | exact resolve eq2001 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2001
  have eq2016 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2010 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2010
    | (have j0 := eq2010 X0
       grind)
    | exact resolve eq2010 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2010
  have eq6200 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq598
       have i₂ := eq31 x X0 y
       grind)
    | exact superpose eq31 eq598
    | (have j1 := eq31 x X0 x
       grind)
    | exact resolve eq598 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq598
  have eq6204 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq6200 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6200
  have eq6296 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq6204 (τ X0)
       grind)
    | exact superpose eq6204 eq15
    | exact resolve eq15 eq6204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq6204
  have eq6300 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq6296 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6296
    | exact resolve eq6296 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6296
  have eq6311 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have j0 := eq6300 X0
       have j1 := eq11 X0 (σ x)
       grind)
    | (have r₁ := eq6300 X0
       have r₂ := eq11 X0 (σ x)
       grind)
    | exact resolve eq6300 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6300
  have eq6489 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2016 (σ x)
       have i₂ := eq6311 (σ x)
       grind)
    | exact superpose eq6311 eq2016
    | (have j0 := eq2016 (σ x)
       grind)
    | (have r₁ := eq2016 (σ x)
       have r₂ := eq6311 (σ x)
       grind)
    | exact resolve eq2016 eq6311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6491 : ∀ X0 : G, (τ (σ x)) ≠ (τ (σ x)) ∨ (k X0 (τ (σ x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq717 (σ x) X0
       have i₂ := eq6311 (σ x)
       grind)
    | exact superpose eq6311 eq717
    | (have j0 := eq717 (σ x) X0
       grind)
    | exact resolve eq717 eq6311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717
  have eq6501 : ∀ X0 X1 : G, (M.op (σ x) X0) = X0 ∨ (σ x) = (k (σ x) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq388 (σ x) X1 X0
       have i₂ := eq6311 X0
       grind)
    | exact superpose eq6311 eq388
    | (have j0 := eq388 (σ x) X1 x
       grind)
    | exact resolve eq388 eq6311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388 eq6311
  have eq6514 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 := by
    intro X0
    first
    | (have j0 := eq6491 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6491
  have eq6516 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq6489
  have eq6522 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq6514 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq6514
    | exact resolve eq6514 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6514
  have eq6625 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2016 x
       have i₂ := eq6522 x
       grind)
    | exact superpose eq6522 eq2016
    | (have j0 := eq2016 x
       grind)
    | (have r₁ := eq2016 x
       have r₂ := eq6522 x
       grind)
    | exact resolve eq2016 eq6522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6522
  have eq6650 : x = (M.op x x) := by grind
  clear eq6625
  have eq7002 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq6650
       grind)
    | exact superpose eq6650 eq8
    | exact resolve eq8 eq6650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7007 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1 x
       have i₂ := eq6650
       grind)
    | exact superpose eq6650 eq19
    | exact resolve eq19 eq6650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7030 : ∀ X0 : G, (M.op x X0) = (k (M.op x X0) X0) := by
    intro X0
    first
    | (have i₁ := eq191 x x
       have i₂ := eq6650
       grind)
    | exact superpose eq6650 eq191
    | exact resolve eq191 eq6650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq7055 : ∀ X0 X1 : G, (M.op x x) = (M.op X0 x) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X0 x x X1
       have i₂ := eq6650
       grind)
    | exact superpose eq6650 eq26
    | (have j0 := eq26 X0 X1 x X1
       grind)
    | exact resolve eq26 eq6650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq7067 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ x = (M.op X0 x) := by
    intro X0 X1
    first
    | (have i₁ := eq7055 X0 X1
       have i₂ := eq6650
       grind)
    | exact superpose eq6650 eq7055
    | (have j0 := eq7055 X0 X1
       grind)
    | exact resolve eq7055 eq6650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7055
  have eq9024 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X3) (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X4)) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X4) (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X1 X1) X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq159 X0 X0 X3 (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X4)
       have i₂ := eq95 X1 X2 (M.op X0 X0) X4
       grind)
    | (have i₁ := eq159 X0 X0 X2 (M.op (M.op X0 X0) X1)
       have i₂ := eq95 X0 X1 (M.op X0 X0) X3
       grind)
    | exact superpose eq95 eq159
    | exact resolve eq159 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq159
  have eq9073 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X3) (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X4)) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X4) (M.op x (M.op (M.op X1 X1) X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9024 X0 X1 X2 X3 X4
       have i₂ := eq7007 (M.op X0 X0) (M.op (M.op X1 X1) X2)
       grind)
    | exact superpose eq7007 eq9024
    | exact resolve eq9024 eq7007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9024
  have eq9189 : ∀ X0 X2 X3 X4 : G, (M.op (M.op X3 X3) (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X4)) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X4) (M.op x (M.op x X2))) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq9073 X0 x X2 X3 X4
       have i₂ := eq7007 x X2
       grind)
    | exact superpose eq7007 eq9073
    | exact resolve eq9073 eq7007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9073
  have eq9305 : ∀ X0 X3 X4 : G, (M.op (M.op X3 X3) (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X4)) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X4) (M.op x x)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq9189 X0 x X3 X4
       have i₂ := eq7002 x x
       grind)
    | exact superpose eq7002 eq9189
    | exact resolve eq9189 eq7002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9189
  have eq9418 : ∀ X0 X3 X4 : G, (M.op (M.op X3 X3) (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X4)) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X4) x) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq9305 X0 X3 X4
       have i₂ := eq6650
       grind)
    | exact superpose eq6650 eq9305
    | exact resolve eq9305 eq6650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9305
  have eq9526 : ∀ X3 X4 : G, (M.op (M.op X3 X3) (M.op x X4)) = (M.op (M.op x X4) x) := by
    intro X3 X4
    first
    | (have i₁ := eq9418 x X3 x
       have i₂ := eq7007 (M.op x x) x
       grind)
    | exact superpose eq7007 eq9418
    | exact resolve eq9418 eq7007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9418
  have eq9632 : ∀ X4 : G, (M.op x (M.op x X4)) = (M.op (M.op x X4) x) := by
    intro X4
    first
    | (have i₁ := eq9526 x X4
       have i₂ := eq7007 x (M.op x X4)
       grind)
    | exact superpose eq7007 eq9526
    | exact resolve eq9526 eq7007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9526
  have eq9714 : ∀ X4 : G, (M.op x x) = (M.op (M.op x X4) x) := by
    intro X4
    first
    | (have i₁ := eq9632 X4
       have i₂ := eq7002 x X4
       grind)
    | exact superpose eq7002 eq9632
    | exact resolve eq9632 eq7002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9632
  have eq9775 : ∀ X4 : G, x = (M.op (M.op x X4) x) := by
    intro X4
    first
    | (have i₁ := eq9714 X4
       have i₂ := eq6650
       grind)
    | exact superpose eq6650 eq9714
    | exact resolve eq9714 eq6650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9714
  have eq9886 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (M.op (M.op X1 X1) x) := by
    intro X0 X1
    first
    | (have i₁ := eq67 x x X1 X0
       have i₂ := eq9775 x
       grind)
    | exact superpose eq9775 eq67
    | exact resolve eq67 eq9775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq9775
  have eq9941 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq9886 X0 X1
       have i₂ := eq7007 X1 x
       grind)
    | exact superpose eq7007 eq9886
    | exact resolve eq9886 eq7007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9886
  have eq9970 : ∀ X0 X1 : G, x = (M.op (M.op X0 X0) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9941 X0 X1
       have i₂ := eq6650
       grind)
    | exact superpose eq6650 eq9941
    | exact resolve eq9941 eq6650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9941
  have eq9982 : ∀ X1 : G, x = (M.op x (M.op X1 X1)) := by
    intro X1
    first
    | (have i₁ := eq9970 x X1
       have i₂ := eq7007 x (M.op X1 X1)
       grind)
    | exact superpose eq7007 eq9970
    | exact resolve eq9970 eq7007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9970
  have eq14615 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X1) (M.op X2 X2)) = (M.op (σ X0) (M.op (M.op X3 X3) (M.op X2 X2))) ∨ (M.op (σ X0) (σ X4)) = (σ (k X4 X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq190 X1 X2 X3 (σ X0)
       have i₂ := eq29 X0 X4
       grind)
    | exact superpose eq29 eq190
    | (have j1 := eq29 X0 X4
       grind)
    | exact resolve eq190 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq190
  have eq15228 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X1 X1) (M.op X2 X2)) = (M.op (σ X0) (M.op x (M.op X2 X2))) ∨ (M.op (σ X0) (σ X4)) = (σ (k X4 X0)) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq14615 X0 X1 X2 x X4
       have i₂ := eq7007 x (M.op X2 X2)
       grind)
    | exact superpose eq7007 eq14615
    | (have j0 := eq14615 X0 X1 X2 x X4
       grind)
    | exact resolve eq14615 eq7007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14615
  have eq15381 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X1 X1) (M.op X2 X2)) = (M.op (σ X0) x) ∨ (M.op (σ X0) (σ X4)) = (σ (k X4 X0)) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq15228 X0 X1 X2 X4
       have i₂ := eq9982 X2
       grind)
    | exact superpose eq9982 eq15228
    | (have j0 := eq15228 X0 X1 X2 X4
       grind)
    | exact resolve eq15228 eq9982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15228
  have eq15532 : ∀ X0 X2 X4 : G, (M.op x (M.op X2 X2)) = (M.op (σ X0) x) ∨ (M.op (σ X0) (σ X4)) = (σ (k X4 X0)) := by
    intro X0 X2 X4
    first
    | (have i₁ := eq15381 X0 x X2 X4
       have i₂ := eq7007 x (M.op X2 X2)
       grind)
    | exact superpose eq7007 eq15381
    | (have j0 := eq15381 X0 x X2 X4
       grind)
    | exact resolve eq15381 eq7007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15381
  have eq15675 : ∀ X0 X4 : G, (M.op (σ X0) (σ X4)) = (σ (k X4 X0)) ∨ x = (M.op (σ X0) x) := by
    intro X0 X4
    first
    | (have i₁ := eq15532 X0 x X4
       have i₂ := eq9982 x
       grind)
    | exact superpose eq9982 eq15532
    | (have j0 := eq15532 X0 x X4
       grind)
    | exact resolve eq15532 eq9982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15532
  have eq19463 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (σ x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1 (σ x)
       have i₂ := eq6516
       grind)
    | exact superpose eq6516 eq19
    | exact resolve eq19 eq6516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq19524 : x = (M.op x (σ x)) := by
    first
    | (have i₁ := eq9982 (σ x)
       have i₂ := eq6516
       grind)
    | exact superpose eq6516 eq9982
    | exact resolve eq9982 eq6516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9982
  have eq19532 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq148 (σ x) (σ x) X0
       have i₂ := eq6516
       grind)
    | exact superpose eq6516 eq148
    | (have j0 := eq148 (σ x) x X0
       grind)
    | exact resolve eq148 eq6516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq19549 : ∀ X0 : G, (σ x) = (k (σ x) (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq19532 X0
       have j1 := eq6501 X0 X0
       grind)
    | (have r₁ := eq19532 X0
       have r₂ := eq6501 (σ x) x
       grind)
    | exact resolve eq19532 eq6501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6501 eq19532
  have eq19597 : ∀ X1 : G, (M.op x X1) = (M.op (σ x) X1) := by
    intro X1
    first
    | (have i₁ := eq19463 x X1
       have i₂ := eq7007 x X1
       grind)
    | exact superpose eq7007 eq19463
    | exact resolve eq19463 eq7007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19463
  have eq24810 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq19597 (σ y)
       grind)
    | exact superpose eq19597 eq14
    | exact resolve eq14 eq19597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24811 : (σ x) = (M.op x (σ x)) := by
    first
    | (have i₁ := eq6516
       have i₂ := eq19597 (σ x)
       grind)
    | exact superpose eq19597 eq6516
    | exact resolve eq6516 eq19597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19597
  have eq25080 : x = (σ x) := by
    first
    | (have i₁ := eq24811
       have i₂ := eq19524
       grind)
    | exact superpose eq19524 eq24811
    | exact resolve eq24811 eq19524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19524 eq24811
  have eq33070 : ∀ X0 : G, (τ (σ x)) = (k x (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq38 x (M.op X0 X0)
       have i₂ := eq19549 X0
       grind)
    | exact superpose eq19549 eq38
    | exact resolve eq38 eq19549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq19549
  have eq33084 : ∀ X0 : G, x = (k x (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq33070 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq33070
    | exact resolve eq33070 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33070
  have eq43720 : ∀ X0 : G, (τ (M.op x (σ X0))) = (k (τ (M.op x (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq24 (M.op x (σ X0)) X0
       have i₂ := eq7030 (σ X0)
       grind)
    | exact superpose eq7030 eq24
    | exact resolve eq24 eq7030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq7030
  have eq89782 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (σ X1)) = (σ (k (k X2 X1) X1)) ∨ (k X3 (σ X1)) = X3 ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq134 X1 (k X2 X1) X3
       have i₂ := eq611 X2 X1 X0
       grind)
    | exact superpose eq611 eq134
    | (have j0 := eq134 X1 X1 X3
       have j1 := eq611 X0 X1 X2
       grind)
    | exact resolve eq134 eq611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134 eq611
  have eq89848 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (σ X1)) = (σ (k (k X2 X1) X1)) ∨ (k X3 (σ X1)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq89782 X0 X1 X2 X3
       have j1 := eq11 X3 (σ X1)
       grind)
    | (have r₁ := eq89782 X0 X1 X2 X3
       have r₂ := eq11 X0 (σ X1)
       grind)
    | exact resolve eq89782 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89782
  have eq90014 : ∀ X1 X2 X3 : G, (M.op x (σ X1)) = (σ (k (k X2 X1) X1)) ∨ (k X3 (σ X1)) = X3 := by
    intro X1 X2 X3
    first
    | (have i₁ := eq89848 x X1 X2 X3
       have i₂ := eq7007 x (σ X1)
       grind)
    | exact superpose eq7007 eq89848
    | (have j0 := eq89848 x X1 X2 X3
       grind)
    | exact resolve eq89848 eq7007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7007 eq89848
  have eq259053 : ∀ X0 : G, x = (k x (τ (σ (k X0 X0)))) ∨ x = (M.op (σ X0) x) := by
    intro X0
    first
    | (have i₁ := eq33084 (σ X0)
       have i₂ := eq15675 X0 X0
       grind)
    | exact superpose eq15675 eq33084
    | (have j1 := eq15675 X0 x
       grind)
    | exact resolve eq33084 eq15675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15675 eq33084
  have eq259102 : ∀ X0 : G, x = (k x (k X0 X0)) ∨ x = (M.op (σ X0) x) := by
    intro X0
    first
    | (have i₁ := eq259053 X0
       have i₂ := eq9 (k X0 X0)
       grind)
    | exact superpose eq9 eq259053
    | (have j0 := eq259053 X0
       grind)
    | exact resolve eq259053 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259053
  have eq259754 : ∀ X0 : G, x = (k x (τ (k X0 X0))) ∨ x = (M.op (σ (τ X0)) x) := by
    intro X0
    first
    | (have i₁ := eq259102 (τ X0)
       have i₂ := eq69 X0 X0
       grind)
    | exact superpose eq69 eq259102
    | (have j0 := eq259102 (τ X0)
       grind)
    | exact resolve eq259102 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259102
  have eq259775 : ∀ X0 : G, x = (k x (τ (k X0 X0))) ∨ x = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq259754 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq259754
    | (have j0 := eq259754 X0
       grind)
    | exact resolve eq259754 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259754
  have eq264392 : ∀ X0 : G, (σ x) = (k (σ x) (k X0 X0)) ∨ x = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq16 (k X0 X0) x
       have i₂ := eq259775 X0
       grind)
    | exact superpose eq259775 eq16
    | (have j1 := eq259775 X0
       grind)
    | exact resolve eq16 eq259775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259775
  have eq264403 : ∀ X0 : G, x = (k x (k X0 X0)) ∨ x = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq264392 X0
       have i₂ := eq25080
       grind)
    | exact superpose eq25080 eq264392
    | (have j0 := eq264392 X0
       grind)
    | exact resolve eq264392 eq25080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25080 eq264392
  have eq265184 : ∀ X0 : G, x = (M.op (k X0 X0) x) ∨ x = (M.op (k X0 X0) x) ∨ x = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq7067 (k X0 X0) x
       have i₂ := eq264403 X0
       grind)
    | exact superpose eq264403 eq7067
    | (have j0 := eq7067 (k X0 X0) x
       have j1 := eq264403 (k X0 X0)
       grind)
    | exact resolve eq7067 eq264403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7067 eq264403
  have eq265188 : ∀ X0 : G, x = (M.op (k X0 X0) x) ∨ x = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq265184 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265184
  have eq284951 : ∀ X0 X1 X2 : G, (M.op x (σ (τ X1))) = (σ (k (τ (k X0 X1)) (τ X1))) ∨ (k X2 (σ (τ X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq90014 (τ X1) (τ X0) X2
       have i₂ := eq69 X1 X0
       grind)
    | exact superpose eq69 eq90014
    | (have j0 := eq90014 (τ X1) X2 X2
       grind)
    | exact resolve eq90014 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq90014
  have eq284994 : ∀ X0 X1 X2 : G, (M.op x (σ (τ X1))) = (k (σ (τ (k X0 X1))) X1) ∨ (k X2 (σ (τ X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq284951 X0 X1 X2
       have i₂ := eq16 X1 (τ (k X0 X1))
       grind)
    | exact superpose eq16 eq284951
    | (have j0 := eq284951 X0 X1 X2
       grind)
    | exact resolve eq284951 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq284951
  have eq285011 : ∀ X0 X1 X2 : G, (k (k X0 X1) X1) = (M.op x (σ (τ X1))) ∨ (k X2 (σ (τ X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq284994 X0 X1 X2
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq284994
    | (have j0 := eq284994 X0 X1 X2
       grind)
    | exact resolve eq284994 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284994
  have eq285021 : ∀ X0 X1 X2 : G, (k (k X0 X1) X1) = (M.op x X1) ∨ (k X2 (σ (τ X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq285011 X0 X1 X2
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq285011
    | (have j0 := eq285011 X0 X1 X2
       grind)
    | exact resolve eq285011 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285011
  have eq285026 : ∀ X0 X1 X2 : G, (k X2 X1) = X2 ∨ (k (k X0 X1) X1) = (M.op x X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq285021 X0 X1 X2
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq285021
    | (have j0 := eq285021 X0 X1 X2
       grind)
    | exact resolve eq285021 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285021
  have eq291306 : ∀ X0 X1 : G, (M.op x X0) = (k (τ (M.op x (σ X0))) X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq285026 (τ (M.op x (σ X0))) X0 X1
       have i₂ := eq43720 X0
       grind)
    | exact superpose eq43720 eq285026
    | (have j0 := eq285026 X0 X0 X1
       grind)
    | exact resolve eq285026 eq43720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285026
  have eq291437 : ∀ X0 X1 : G, (M.op x X0) = (τ (M.op x (σ X0))) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq291306 X0 X1
       have i₂ := eq43720 X0
       grind)
    | exact superpose eq43720 eq291306
    | (have j0 := eq291306 X0 X1
       grind)
    | exact resolve eq291306 eq43720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43720 eq291306
  have eq350747 : ∀ X0 X1 : G, (σ (M.op x X0)) = (M.op x (σ X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op x (σ X0))
       have i₂ := eq291437 X0 X1
       grind)
    | exact superpose eq291437 eq10
    | (have j1 := eq291437 X0 X1
       grind)
    | exact resolve eq10 eq291437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291437
  have eq354219 : ∀ X0 : G, (M.op x (σ y)) ≠ (M.op x (σ y)) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq24810
       have i₂ := eq350747 y X0
       grind)
    | exact superpose eq350747 eq24810
    | (have j1 := eq350747 y X0
       grind)
    | (have r₁ := eq24810
       have r₂ := eq350747 y x
       grind)
    | exact resolve eq24810 eq350747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24810 eq350747
  have eq354273 : ∀ X0 : G, (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq354219 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354219
  have eq354486 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2016 y
       have i₂ := eq354273 y
       grind)
    | exact superpose eq354273 eq2016
    | (have j0 := eq2016 y
       grind)
    | (have r₁ := eq2016 y
       have r₂ := eq354273 y
       grind)
    | exact resolve eq2016 eq354273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2016
  have eq354564 : x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq265188 y
       have i₂ := eq354273 y
       grind)
    | exact superpose eq354273 eq265188
    | (have j0 := eq265188 y
       grind)
    | exact resolve eq265188 eq354273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265188 eq354273
  have eq354817 : x = (M.op y x) := by grind
  clear eq354564
  have eq354818 : y = (M.op y y) := by grind
  clear eq354486
  have eq355044 : (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq7002 y x
       have i₂ := eq354817
       grind)
    | exact superpose eq354817 eq7002
    | exact resolve eq7002 eq354817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq355072 : x = (M.op x y) := by
    first
    | (have i₁ := eq355044
       have i₂ := eq354817
       grind)
    | exact superpose eq354817 eq355044
    | exact resolve eq355044 eq354817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354817 eq355044
  have eq355526 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq7002 y y
       have i₂ := eq354818
       grind)
    | exact superpose eq354818 eq7002
    | exact resolve eq7002 eq354818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7002
  have eq355553 : y = (M.op x y) := by
    first
    | (have i₁ := eq355526
       have i₂ := eq354818
       grind)
    | exact superpose eq354818 eq355526
    | exact resolve eq355526 eq354818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354818 eq355526
  have eq355781 : x = y := by
    first
    | (have i₁ := eq355553
       have i₂ := eq355072
       grind)
    | exact superpose eq355072 eq355553
    | exact resolve eq355553 eq355072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355072 eq355553
  have eq356245 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq355781
       grind)
    | exact superpose eq355781 eq14
    | exact resolve eq14 eq355781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355781
  have eq356253 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq356245
       have i₂ := eq6650
       grind)
    | exact superpose eq6650 eq356245
    | exact resolve eq356245 eq6650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6650 eq356245
  have eq356255 : False := by grind
  exact eq356255

/-- `Equation4428`: `x ◇ (x ◇ y) = (z ◇ w) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_pxx_pyx_Equation4428 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4428 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4428.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X3) X1) := by
    intro X0 X1 X2 X3
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq15 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (k (τ X0) X1) X2
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq13
    | exact resolve eq13 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq23 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X4 X5) X2) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq8 x X2 X4 X5
       have i₂ := eq8 x X2 X0 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 X2)) = (M.op X0 X2) ∨ (k X3 X0) = (M.op X0 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 X2 X0 X0
       have i₂ := eq12 X3 X0
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X3 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X1 X0
       have i₂ := eq12 X2 X0
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X1 X0
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 X0 (σ X0)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq50 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq192 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq56 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq1206 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 (M.op X1 X2))) ≠ (M.op X3 (M.op X1 X2)) ∨ (k (M.op X1 X2) X3) = (M.op X3 (M.op X1 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq192 (M.op X1 X2) X3
       have i₂ := eq8 X0 (M.op X1 X2) X1 X2
       grind)
    | exact superpose eq8 eq192
    | (have j0 := eq192 (M.op X1 X2) X3
       grind)
    | exact resolve eq192 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1224 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq192 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq1238 : ∀ X1 X2 X3 : G, (k (M.op X1 X2) X3) = (M.op X3 (M.op X1 X2)) := by
    intro X1 X2 X3
    first
    | (have j0 := eq1206 x X1 X2 X3
       have j1 := eq48 X3 X1 X2 (M.op X1 X2)
       grind)
    | (have r₁ := eq1206 X1 X1 X2 x
       have r₂ := eq48 x X1 (M.op X1 X2) X3
       grind)
    | exact resolve eq1206 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq1206
  have eq1271 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq52 x y
       grind)
    | exact superpose eq52 eq14
    | (have j1 := eq52 x x
       grind)
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1358 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq1224 (σ X0)
       grind)
    | exact superpose eq1224 eq13
    | exact resolve eq13 eq1224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1369 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1358 X0
       have i₂ := eq1224 X0
       grind)
    | exact superpose eq1224 eq1358
    | exact resolve eq1358 eq1224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1358
  have eq1672 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X3) = (M.op (σ (M.op X0 X0)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq23 X1 X2 X3 (σ X0) (σ X0)
       have i₂ := eq1369 X0
       grind)
    | exact superpose eq1369 eq23
    | exact resolve eq23 eq1369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2008 : ∀ X0 X1 : G, (σ (k (k (τ (σ X0)) X0) X1)) = (k (M.op (σ X0) (σ X0)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (σ X0) X0 X1
       have i₂ := eq1224 (σ X0)
       grind)
    | exact superpose eq1224 eq19
    | exact resolve eq19 eq1224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq2035 : ∀ X0 X1 : G, (σ (k (k (τ (σ X0)) X0) X1)) = (M.op (σ X1) (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2008 X0 X1
       have i₂ := eq1238 (σ X0) (σ X0) (σ X1)
       grind)
    | exact superpose eq1238 eq2008
    | exact resolve eq2008 eq1238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2008
  have eq2043 : ∀ X0 X1 : G, (σ (k (k (τ (σ X0)) X0) X1)) = (M.op (σ X1) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2035 X0 X1
       have i₂ := eq1369 X0
       grind)
    | exact superpose eq1369 eq2035
    | exact resolve eq2035 eq1369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2035
  have eq2047 : ∀ X0 X1 : G, (M.op (σ X1) (σ (M.op X0 X0))) = (σ (k (k X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2043 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq2043
    | exact resolve eq2043 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2043
  have eq2049 : ∀ X0 X1 : G, (M.op (σ X1) (σ (M.op X0 X0))) = (σ (k (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2047 X0 X1
       have i₂ := eq1224 X0
       grind)
    | exact superpose eq1224 eq2047
    | exact resolve eq2047 eq1224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1224 eq2047
  have eq2051 : ∀ X0 X1 : G, (M.op (σ X1) (σ (M.op X0 X0))) = (σ (M.op X1 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2049 X0 X1
       have i₂ := eq1238 X0 X0 X1
       grind)
    | exact superpose eq1238 eq2049
    | exact resolve eq2049 eq1238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1238 eq2049
  have eq14073 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1271
       have i₂ := eq12 y x
       grind)
    | exact superpose eq12 eq1271
    | (have j1 := eq12 x (σ x)
       grind)
    | exact resolve eq1271 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1271
  have eq14077 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq14073
  have eq14080 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq14077
       have i₂ := eq1369 x
       grind)
    | exact superpose eq1369 eq14077
    | exact resolve eq14077 eq1369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14077
  have eq14087 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq9 (M.op x x)
       have i₂ := eq14080
       grind)
    | exact superpose eq14080 eq9
    | exact resolve eq9 eq14080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14080
  have eq14122 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq14087
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq14087
    | exact resolve eq14087 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14087
  have eq14123 : x = (M.op x x) := by grind
  clear eq14122
  have eq14514 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (σ x) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1672 x X0 X1 X2
       have i₂ := eq14123
       grind)
    | exact superpose eq14123 eq1672
    | exact resolve eq1672 eq14123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1672
  have eq14520 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 x x
       have i₂ := eq14123
       grind)
    | exact superpose eq14123 eq8
    | exact resolve eq8 eq14123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14527 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op x X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 X0 X1 X2 x x
       have i₂ := eq14123
       grind)
    | exact superpose eq14123 eq23
    | exact resolve eq23 eq14123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq14123
  have eq14597 : ∀ X2 : G, (M.op x X2) = (M.op (σ x) X2) := by
    intro X2
    first
    | (have i₁ := eq14514 x x X2
       have i₂ := eq14527 x x X2
       grind)
    | exact superpose eq14527 eq14514
    | exact resolve eq14514 eq14527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14514 eq14527
  have eq23623 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq14597 (σ y)
       grind)
    | exact superpose eq14597 eq14
    | exact resolve eq14 eq14597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14597
  have eq42968 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op x (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq14520 (σ X0) (σ X0)
       have i₂ := eq1369 X0
       grind)
    | exact superpose eq1369 eq14520
    | exact resolve eq14520 eq1369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1369
  have eq43408 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op x (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq42968 X0
       have i₂ := eq2051 X0 X0
       grind)
    | exact superpose eq2051 eq42968
    | exact resolve eq42968 eq2051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2051 eq42968
  have eq43573 : ∀ X0 : G, (M.op x (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq43408 X0
       have i₂ := eq14520 X0 X0
       grind)
    | exact superpose eq14520 eq43408
    | exact resolve eq43408 eq14520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14520 eq43408
  have eq151715 : (M.op x (σ y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq23623
       have i₂ := eq43573 y
       grind)
    | exact superpose eq43573 eq23623
    | (have r₁ := eq23623
       have r₂ := eq43573 y
       grind)
    | exact resolve eq23623 eq43573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23623 eq43573
  have eq151716 : False := by grind
  exact eq151716

/-- `Equation4430`: `x ◇ (x ◇ y) = (z ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxy_y_x_pxy_Equation4430 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4430 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4430.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X3) X3) := by
    intro X0 X1 X2 X3
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq15 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 X4 X5 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X4 X5) X5) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq8 x x X4 X5
       have i₂ := eq8 x x X0 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op X0 (M.op X0 X1)) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq8 X2 X3 (M.op x X5) X5
       have i₂ := eq8 X0 X1 x X5
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X0 X1 x x
       have i₂ := eq8 X2 X3 x x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq9
    | exact resolve eq9 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq30 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq16 X1 X0
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq51 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X2 X3) X3) = (M.op (M.op X0 (M.op X0 X1)) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq19 X2 X3 (M.op x X5) X5
       have i₂ := eq8 X0 X1 x X5
       grind)
    | exact superpose eq8 eq19
    | exact resolve eq19 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op (M.op X0 X1) X1) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq8 X2 X3 (M.op x X5) X5
       have i₂ := eq19 x X5 X0 X1
       grind)
    | (have i₁ := eq8 X2 X3 (M.op x X5) X5
       have i₂ := eq19 X0 X1 x X5
       grind)
    | exact superpose eq19 eq8
    | exact resolve eq8 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq28
    | exact resolve eq28 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq82 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X2 X3)) = (M.op X4 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq22 X2 X3 X4 (M.op X4 x)
       have i₂ := eq22 X4 x X0 X1
       grind)
    | (have i₁ := eq22 X2 X3 X4 (M.op X4 x)
       have i₂ := eq22 X0 X1 X4 x
       grind)
    | exact superpose eq22 eq22
    | exact resolve eq22 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X2 X3)) = (M.op X4 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq22 X2 X3 X4 (M.op X4 x)
       have i₂ := eq8 X4 x X0 X1
       grind)
    | exact superpose eq8 eq22
    | exact resolve eq22 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X4 X5) X5) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq8 X2 (M.op X2 x) X4 X5
       have i₂ := eq22 X2 x X0 X1
       grind)
    | (have i₁ := eq8 X2 (M.op X2 x) X4 X5
       have i₂ := eq22 X0 X1 X2 x
       grind)
    | exact superpose eq22 eq8
    | exact resolve eq8 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op X2 X3) ∨ (k X2 (M.op X2 X3)) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq11 X2 (M.op X2 X3)
       have i₂ := eq22 X2 X3 X0 X1
       grind)
    | (have i₁ := eq11 X2 (M.op X2 X3)
       have i₂ := eq22 X0 X1 X2 X3
       grind)
    | exact superpose eq22 eq11
    | (have j0 := eq11 X2 (M.op X2 X3)
       grind)
    | (have r₁ := eq11 X2 (M.op X2 (M.op X2 X3))
       have r₂ := eq22 X2 (M.op X2 X3) X2 X3
       grind)
    | (have r₁ := eq11 X0 (M.op X0 (M.op X0 X1))
       have r₂ := eq22 X0 X1 X0 (M.op X0 X1)
       grind)
    | exact resolve eq11 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1263 : ∀ X0 X1 X2 X3 X4 X5 X7 : G, (M.op X3 (M.op X3 X4)) = (M.op X5 (M.op (M.op (M.op X0 (M.op X0 X1)) X2) X7)) := by
    intro X0 X1 X2 X3 X4 X5 X7
    first
    | (have i₁ := eq83 (M.op x X7) X7 X3 X4 X5
       have i₂ := eq51 X0 X1 x X7 X2
       grind)
    | (have i₁ := eq83 (M.op X0 (M.op X0 X1)) X5 X2 X3 X4
       have i₂ := eq51 X0 X1 X2 X3 X5
       grind)
    | exact superpose eq51 eq83
    | exact resolve eq83 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq1420 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq30 x y
       grind)
    | exact superpose eq30 eq14
    | (have j1 := eq30 x y
       grind)
    | exact resolve eq14 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1451 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq30 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq1473 : ∀ X0 X1 X2 X4 X5 X6 X7 : G, (M.op X5 (M.op X6 (M.op X6 X7))) = (M.op (M.op (M.op X0 (M.op X0 X1)) X2) X4) := by
    intro X0 X1 X2 X4 X5 X6 X7
    first
    | (have i₁ := eq97 X6 X7 X5 (M.op x X4) X4
       have i₂ := eq51 X0 X1 x X4 X2
       grind)
    | (have i₁ := eq97 X0 X1 X2 (M.op X0 (M.op X0 X1)) X5
       have i₂ := eq51 X0 X1 X2 x X5
       grind)
    | exact superpose eq51 eq97
    | exact resolve eq97 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1612 : ∀ X0 X1 X2 X3 X4 X6 X7 : G, (M.op X3 (M.op X3 X4)) = (M.op (M.op (M.op X0 (M.op X1 (M.op X1 X2))) X6) X7) := by
    intro X0 X1 X2 X3 X4 X6 X7
    first
    | (have i₁ := eq60 (M.op x X6) X6 X3 X4 X7
       have i₂ := eq97 X1 X2 X0 x X6
       grind)
    | (have i₁ := eq60 X2 (M.op X0 (M.op X0 X1)) X2 X3 x
       have i₂ := eq97 X0 X1 X2 X4 x
       grind)
    | exact superpose eq97 eq60
    | exact resolve eq60 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq97
  have eq8696 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1451 (τ X0) (τ X1)
       have i₂ := eq63 X1 X0
       grind)
    | exact superpose eq63 eq1451
    | (have j0 := eq1451 (τ X0) (τ X1)
       grind)
    | exact resolve eq1451 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq1451
  have eq8703 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq8696 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq8696
    | (have j0 := eq8696 X0 X1
       grind)
    | exact resolve eq8696 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8696
  have eq8705 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq8703 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq8703
    | (have j0 := eq8703 X0 X1
       grind)
    | exact resolve eq8703 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8703
  have eq8706 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8705 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8705
    | (have j0 := eq8705 X0 X1
       grind)
    | exact resolve eq8705 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8705
  have eq8707 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8706 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8706
    | (have j0 := eq8706 X0 X1
       grind)
    | exact resolve eq8706 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8706
  have eq9048 : ∀ X0 X1 : G, (k X0 (M.op X0 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq99 X0 X1 X0 (M.op X0 X1)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq9132 : ∀ X0 X1 X2 : G, (k X2 (M.op X0 (M.op X0 X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9048 X2 (M.op X2 x)
       have i₂ := eq82 X2 x X0 X1 X2
       grind)
    | (have i₁ := eq9048 X2 x
       have i₂ := eq82 X0 X1 X2 x x
       grind)
    | exact superpose eq82 eq9048
    | exact resolve eq9048 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq9048
  have eq9331 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq38 X0 (M.op X1 (M.op X1 X2))
       have i₂ := eq9132 X1 X2 (σ X0)
       grind)
    | exact superpose eq9132 eq38
    | exact resolve eq38 eq9132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9334 : ∀ X0 X1 X2 : G, (k X0 (τ (M.op X1 (M.op X1 X2)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9331 X0 X1 X2
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq9331
    | exact resolve eq9331 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9331
  have eq26832 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1420
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq1420
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq1420 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1420
  have eq26833 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq26832
  have eq42138 : ∀ X0 : G, (k X0 (M.op (σ x) (σ y))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9132 (σ x) (σ y) X0
       have i₂ := eq26833
       grind)
    | exact superpose eq26833 eq9132
    | exact resolve eq9132 eq26833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9132
  have eq110776 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq42138 X0
       have i₂ := eq26833
       grind)
    | exact superpose eq26833 eq42138
    | exact resolve eq42138 eq26833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26833 eq42138
  have eq110799 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq110776 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110776
  have eq112614 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq38 X0 (σ y)
       have i₂ := eq110799 (σ X0)
       grind)
    | exact superpose eq110799 eq38
    | exact resolve eq38 eq110799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq110799
  have eq112625 : ∀ X0 : G, (τ (σ X0)) = (k X0 y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq112614 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq112614
    | exact resolve eq112614 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112614
  have eq112628 : ∀ X0 : G, (k X0 y) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq112625 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq112625
    | exact resolve eq112625 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112625
  have eq114405 : ∀ X0 : G, y ≠ X0 ∨ y = (M.op X0 y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq8707 X0 y
       have i₂ := eq112628 X0
       grind)
    | exact superpose eq112628 eq8707
    | (have j0 := eq8707 X0 y
       grind)
    | (have r₁ := eq8707 y y
       have r₂ := eq112628 y
       grind)
    | exact resolve eq8707 eq112628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112628
  have eq117676 : y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have j0 := eq114405 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114405
  have eq118561 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op y y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1 y y
       have i₂ := eq117676
       grind)
    | exact superpose eq117676 eq19
    | exact resolve eq19 eq117676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq294475 : ∀ X1 : G, (M.op y y) = (M.op (M.op y y) X1) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X1
    first
    | (have i₁ := eq118561 (M.op x X1) X1
       have i₂ := eq118561 x X1
       grind)
    | exact superpose eq118561 eq118561
    | exact resolve eq118561 eq118561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118561
  have eq295500 : ∀ X1 : G, (M.op y y) = (M.op (M.op y y) X1) ∨ y = (M.op x y) := by
    intro X1
    first
    | (have j0 := eq294475 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294475
  have eq406531 : ∀ X0 : G, y = (M.op y X0) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq295500 x
       have i₂ := eq117676
       grind)
    | exact superpose eq117676 eq295500
    | exact resolve eq295500 eq117676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117676 eq295500
  have eq407179 : ∀ X0 : G, y = (M.op y X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq406531 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406531
  have eq409295 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = y ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq1263 x x x X0 X1 y x
       have i₂ := eq407179 (M.op (M.op (M.op x (M.op x x)) x) x)
       grind)
    | exact superpose eq407179 eq1263
    | exact resolve eq1263 eq407179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1263 eq407179
  have eq411137 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq409295 X0 (M.op X0 x)
       have i₂ := eq409295 X0 x
       grind)
    | exact superpose eq409295 eq409295
    | exact resolve eq409295 eq409295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409295
  have eq412522 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq411137 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411137
  have eq414872 : y ≠ y ∨ y = (M.op x y) := by
    first
    | (have j0 := eq412522 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412522
  have eq414873 : y = (M.op x y) := by grind
  clear eq414872
  have eq416374 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 x y
       have i₂ := eq414873
       grind)
    | exact superpose eq414873 eq8
    | exact resolve eq8 eq414873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq416383 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x y) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 x y X0 X1 X2
       have i₂ := eq414873
       grind)
    | exact superpose eq414873 eq21
    | exact resolve eq21 eq414873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq416385 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X0 X1 x y
       have i₂ := eq414873
       grind)
    | exact superpose eq414873 eq22
    | exact resolve eq22 eq414873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq416389 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op x y) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 x y X0 X1 X2
       have i₂ := eq414873
       grind)
    | exact superpose eq414873 eq51
    | exact resolve eq51 eq414873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq416707 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 (M.op X1 X2)) X3) X4) = (M.op X0 (M.op x y)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1473 X1 X2 X3 X4 X0 x y
       have i₂ := eq414873
       grind)
    | exact superpose eq414873 eq1473
    | exact resolve eq1473 eq414873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1473
  have eq416722 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (M.op X2 (M.op x y)) X3) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1612 X2 x y X0 X1 X3 X4
       have i₂ := eq414873
       grind)
    | exact superpose eq414873 eq1612
    | exact resolve eq1612 eq414873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1612
  have eq416766 : ∀ X0 : G, (k X0 (τ (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9334 X0 x y
       have i₂ := eq414873
       grind)
    | exact superpose eq414873 eq9334
    | exact resolve eq9334 eq414873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9334
  have eq416861 : ∀ X0 : G, (k X0 (τ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq416766 X0
       have i₂ := eq414873
       grind)
    | exact superpose eq414873 eq416766
    | exact resolve eq416766 eq414873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416766
  have eq416879 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (M.op X2 y) X3) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq416722 X0 X1 X2 X3 X4
       have i₂ := eq414873
       grind)
    | exact superpose eq414873 eq416722
    | exact resolve eq416722 eq414873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416722
  have eq416890 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 (M.op X1 X2)) X3) X4) = (M.op X0 y) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq416707 X0 X1 X2 X3 X4
       have i₂ := eq414873
       grind)
    | exact superpose eq414873 eq416707
    | exact resolve eq416707 eq414873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416707
  have eq417009 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op y X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq416389 X0 X1 X2
       have i₂ := eq414873
       grind)
    | exact superpose eq414873 eq416389
    | exact resolve eq416389 eq414873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416389
  have eq417011 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = y := by
    intro X0 X1
    first
    | (have i₁ := eq416385 X0 X1
       have i₂ := eq414873
       grind)
    | exact superpose eq414873 eq416385
    | exact resolve eq416385 eq414873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416385
  have eq417013 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op y X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq416383 X0 X1 X2
       have i₂ := eq414873
       grind)
    | exact superpose eq414873 eq416383
    | exact resolve eq416383 eq414873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416383
  have eq417017 : ∀ X2 X3 X4 : G, (M.op y y) = (M.op (M.op (M.op X2 y) X3) X4) := by
    intro X2 X3 X4
    first
    | (have i₁ := eq416879 x x X2 X3 X4
       have i₂ := eq416374 x x
       grind)
    | exact superpose eq416374 eq416879
    | exact resolve eq416879 eq416374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416879
  have eq417028 : ∀ X0 X3 X4 : G, (M.op X0 y) = (M.op (M.op (M.op y y) X3) X4) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq416890 X0 x x X3 X4
       have i₂ := eq416374 x x
       grind)
    | exact superpose eq416374 eq416890
    | exact resolve eq416890 eq416374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416374 eq416890
  have eq417136 : ∀ X2 : G, y = (M.op y X2) := by
    intro X2
    first
    | (have i₁ := eq417013 x x X2
       have i₂ := eq417011 x x
       grind)
    | exact superpose eq417011 eq417013
    | exact resolve eq417013 eq417011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417011 eq417013
  have eq417141 : ∀ X0 : G, (M.op y y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq417028 X0 x x
       have i₂ := eq417017 y x x
       grind)
    | exact superpose eq417017 eq417028
    | exact resolve eq417028 eq417017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417017 eq417028
  have eq417191 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq417141 X0
       have i₂ := eq417136 y
       grind)
    | exact superpose eq417136 eq417141
    | exact resolve eq417141 eq417136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417141
  have eq431902 : ∀ X0 : G, (τ y) ≠ X0 ∨ (τ y) = (M.op X0 (τ y)) := by
    intro X0
    first
    | (have i₁ := eq8707 X0 (τ y)
       have i₂ := eq416861 X0
       grind)
    | exact superpose eq416861 eq8707
    | (have j0 := eq8707 X0 (τ y)
       grind)
    | (have r₁ := eq8707 (τ y) (τ y)
       have r₂ := eq416861 (τ y)
       grind)
    | exact resolve eq8707 eq416861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8707 eq416861
  have eq866962 : (τ y) = (M.op (τ y) (τ y)) := by
    first
    | (have j0 := eq431902 (τ y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431902
  have eq868700 : ∀ X0 : G, (M.op y X0) = (M.op (τ y) (τ y)) := by
    intro X0
    first
    | (have i₁ := eq417009 (τ y) (τ y) X0
       have i₂ := eq866962
       grind)
    | exact superpose eq866962 eq417009
    | exact resolve eq417009 eq866962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417009
  have eq868706 : ∀ X0 : G, (τ y) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq868700 X0
       have i₂ := eq866962
       grind)
    | exact superpose eq866962 eq868700
    | exact resolve eq868700 eq866962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq866962 eq868700
  have eq868872 : y = (τ y) := by
    first
    | (have i₁ := eq868706 x
       have i₂ := eq417136 x
       grind)
    | exact superpose eq417136 eq868706
    | exact resolve eq868706 eq417136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417136 eq868706
  have eq870623 : y = (σ y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq868872
       grind)
    | exact superpose eq868872 eq10
    | exact resolve eq10 eq868872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq868872
  have eq872866 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq870623
       grind)
    | exact superpose eq870623 eq14
    | exact resolve eq14 eq870623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq872923 : y ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq872866
       have i₂ := eq417191 (σ x)
       grind)
    | exact superpose eq417191 eq872866
    | exact resolve eq872866 eq417191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417191 eq872866
  have eq872931 : y ≠ (σ y) := by
    first
    | (have i₁ := eq872923
       have i₂ := eq414873
       grind)
    | exact superpose eq414873 eq872923
    | exact resolve eq872923 eq414873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414873 eq872923
  have eq872933 : y ≠ y := by
    first
    | (have i₁ := eq872931
       have i₂ := eq870623
       grind)
    | exact superpose eq870623 eq872931
    | (have r₁ := eq872931
       have r₂ := eq870623
       grind)
    | exact resolve eq872931 eq870623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq870623 eq872931
  have eq872934 : False := by grind
  exact eq872934

/-- `Equation4441`: `x ◇ (y ◇ x) = (x ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyx_y_x_pyx_Equation4441 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4441 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4441.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X2) X3) := by
    intro X0 X1 X2 X3
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq15 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X2 X4) X5) = (M.op X2 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq8 X2 (M.op X0 x) X4 X5
       have i₂ := eq8 X0 X1 x X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X4) X5) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq8 X0 x X4 X5
       have i₂ := eq8 X0 x X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X1 x x
       have i₂ := eq8 X0 X2 x x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X4 X0)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 X0 X4 X1 (M.op x (M.op X0 X1))
       have i₂ := eq8 (M.op X0 X1) x X2 X3
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq9
    | exact resolve eq9 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq32 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq16 X1 X0
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq66 : ∀ X0 X1 X2 X3 X5 X6 : G, (M.op (M.op X3 X5) X6) = (M.op X3 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3 X5 X6
    first
    | (have i₁ := eq8 X3 (M.op X0 x) X5 X6
       have i₂ := eq19 X0 x X3 X1 X2
       grind)
    | (have i₁ := eq8 X3 (M.op X0 x) X5 X6
       have i₂ := eq19 X0 X1 X2 x X3
       grind)
    | exact superpose eq19 eq8
    | exact resolve eq8 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq30
    | exact resolve eq30 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq95 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 (M.op X1 X0))) = (M.op X2 (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq23 X2 X3 (M.op X0 x)
       have i₂ := eq8 X0 X1 x X2
       grind)
    | exact superpose eq8 eq23
    | exact resolve eq23 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq155 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X3 X4) X5) = (M.op X3 (M.op X6 (M.op (M.op X0 X1) X2))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq18 X6 (M.op X0 x) X3 X4 X5
       have i₂ := eq19 X0 x X6 X1 X2
       grind)
    | (have i₁ := eq18 X6 (M.op X0 x) X3 X4 X5
       have i₂ := eq19 X0 X1 X2 x X6
       grind)
    | exact superpose eq19 eq18
    | exact resolve eq18 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq285 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X0)) ≠ (M.op (M.op X0 X2) X3) ∨ (k X4 (M.op (M.op X0 X2) X3)) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq11 X4 (M.op (M.op X0 X2) X3)
       have i₂ := eq24 X0 X2 X3 X4 X1
       grind)
    | exact superpose eq24 eq11
    | (have j0 := eq11 X4 (M.op (M.op X0 X2) X3)
       grind)
    | exact resolve eq11 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq297 : ∀ X0 X2 X3 X4 : G, (k X4 (M.op (M.op X0 X2) X3)) = X4 := by
    intro X0 X2 X3 X4
    first
    | (have j0 := eq285 X0 x X2 X3 X4
       grind)
    | (have r₁ := eq285 X0 x X2 X3 X4
       have r₂ := eq8 X0 x X2 X3
       grind)
    | exact resolve eq285 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285
  have eq817 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq32 x y
       grind)
    | exact superpose eq32 eq14
    | (have j1 := eq32 x y
       grind)
    | exact resolve eq14 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq841 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq1698 : ∀ X0 X1 X2 X3 X4 X6 : G, (M.op X3 (M.op X6 X3)) = (M.op X3 (M.op X4 (M.op X0 (M.op X1 (M.op X2 X1))))) := by
    intro X0 X1 X2 X3 X4 X6
    first
    | (have i₁ := eq95 X4 (M.op X0 x) X3 X6
       have i₂ := eq18 X1 X2 X0 x X4
       grind)
    | exact superpose eq18 eq95
    | exact resolve eq95 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1764 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X4 (M.op X0 (M.op (M.op X1 X2) X3))) = (M.op X4 (M.op X5 (M.op X6 X5))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq95 X5 X6 X4 (M.op X0 x)
       have i₂ := eq66 X1 X2 X3 X0 x X4
       grind)
    | exact superpose eq66 eq95
    | exact resolve eq95 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq3567 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 X8 : G, (M.op (M.op X5 X6) X7) = (M.op X5 (M.op X8 (M.op X0 (M.op X1 (M.op (M.op X2 X3) X4))))) := by
    intro X0 X1 X2 X3 X4 X5 X6 X7 X8
    first
    | (have i₁ := eq18 X8 (M.op X0 x) X5 X6 X7
       have i₂ := eq155 X2 X3 X4 X0 x X8 X1
       grind)
    | exact superpose eq155 eq18
    | exact resolve eq18 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq7521 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq841 (τ X1) (τ X0)
       have i₂ := eq69 X1 X0
       grind)
    | exact superpose eq69 eq841
    | (have j0 := eq841 (τ X1) (τ X0)
       grind)
    | exact resolve eq841 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq7528 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq7521 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq7521
    | (have j0 := eq7521 X0 X1
       grind)
    | exact resolve eq7521 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7521
  have eq7538 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq7528 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq7528
    | (have j0 := eq7528 X0 X1
       grind)
    | exact resolve eq7528 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7528
  have eq7547 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7538 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7538
    | (have j0 := eq7538 X0 X1
       grind)
    | exact resolve eq7538 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7538
  have eq7548 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7547 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7547
    | (have j0 := eq7547 X0 X1
       grind)
    | exact resolve eq7547 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7547
  have eq12502 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq817
       have i₂ := eq12 y x
       grind)
    | exact superpose eq12 eq817
    | (have j1 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq817 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq817
  have eq12503 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq12502
  have eq12556 : ∀ X0 X1 : G, (k X0 (M.op (σ x) X1)) = X0 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq297 (σ x) (σ y) X1 X0
       have i₂ := eq12503
       grind)
    | exact superpose eq12503 eq297
    | exact resolve eq297 eq12503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15805 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq12556 X0 (σ y)
       have i₂ := eq12503
       grind)
    | exact superpose eq12503 eq12556
    | exact resolve eq12556 eq12503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12503 eq12556
  have eq15840 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq15805 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15805
  have eq16352 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq40 X0 (σ x)
       have i₂ := eq15840 (σ X0)
       grind)
    | exact superpose eq15840 eq40
    | exact resolve eq40 eq15840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq15840
  have eq16357 : ∀ X0 : G, (τ (σ X0)) = (k X0 x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16352 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq16352
    | exact resolve eq16352 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16352
  have eq16360 : ∀ X0 : G, (k X0 x) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16357 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq16357
    | exact resolve eq16357 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16357
  have eq16877 : ∀ X0 : G, x ≠ X0 ∨ x = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq7548 X0 x
       have i₂ := eq16360 X0
       grind)
    | exact superpose eq16360 eq7548
    | (have j0 := eq7548 X0 x
       grind)
    | (have r₁ := eq7548 x x
       have r₂ := eq16360 x
       grind)
    | exact resolve eq7548 eq16360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16360
  have eq21818 : x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have j0 := eq16877 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16877
  have eq22586 : ∀ X0 X1 : G, (k X0 (M.op x X1)) = X0 ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq297 x y X1 X0
       have i₂ := eq21818
       grind)
    | exact superpose eq21818 eq297
    | exact resolve eq297 eq21818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297
  have eq22771 : ∀ X0 : G, (k X0 x) = X0 ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq22586 X0 y
       have i₂ := eq21818
       grind)
    | exact superpose eq21818 eq22586
    | exact resolve eq22586 eq21818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21818 eq22586
  have eq22822 : ∀ X0 : G, (k X0 x) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq22771 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22771
  have eq22972 : ∀ X0 : G, x ≠ X0 ∨ x = (M.op x X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq7548 X0 x
       have i₂ := eq22822 X0
       grind)
    | exact superpose eq22822 eq7548
    | (have j0 := eq7548 X0 x
       grind)
    | (have r₁ := eq7548 x x
       have r₂ := eq22822 x
       grind)
    | exact resolve eq7548 eq22822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7548 eq22822
  have eq36435 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have j0 := eq22972 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22972
  have eq36436 : x = (M.op x x) := by grind
  clear eq36435
  have eq37788 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq36436
       grind)
    | exact superpose eq36436 eq11
    | (have j0 := eq11 x x
       grind)
    | (have r₁ := eq11 x x
       have r₂ := eq36436
       grind)
    | exact resolve eq11 eq36436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37810 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op x x)) := by
    intro X0 X1
    first
    | (have i₁ := eq95 x x X0 X1
       have i₂ := eq36436
       grind)
    | exact superpose eq36436 eq95
    | exact resolve eq95 eq36436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq37895 : x = (k x x) := by grind
  clear eq37788
  have eq37913 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 x) := by
    intro X0 X1
    first
    | (have i₁ := eq37810 X0 X1
       have i₂ := eq36436
       grind)
    | exact superpose eq36436 eq37810
    | exact resolve eq37810 eq36436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37810
  have eq39335 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq841 x x
       have i₂ := eq37895
       grind)
    | exact superpose eq37895 eq841
    | (have j0 := eq841 x x
       grind)
    | exact resolve eq841 eq37895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq841 eq37895
  have eq39339 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq39335
  have eq54212 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ x))) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq23 (σ x) X0 (σ x)
       have i₂ := eq39339
       grind)
    | exact superpose eq39339 eq23
    | exact resolve eq23 eq39339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq54309 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op X2 (M.op X3 (M.op (σ x) (σ x))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1698 X3 (σ x) (σ x) X0 X2 X1
       have i₂ := eq39339
       grind)
    | exact superpose eq39339 eq1698
    | exact resolve eq1698 eq39339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1698
  have eq54310 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 (M.op (M.op X2 X3) X4))) = (M.op X0 (M.op (σ x) (σ x))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1764 X1 X2 X3 X4 X0 (σ x) (σ x)
       have i₂ := eq39339
       grind)
    | exact superpose eq39339 eq1764
    | exact resolve eq1764 eq39339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1764
  have eq54342 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 (M.op (M.op X2 X3) X4))) = (M.op X0 (σ x)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq54310 X0 X1 X2 X3 X4
       have i₂ := eq39339
       grind)
    | exact superpose eq39339 eq54310
    | exact resolve eq54310 eq39339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54310
  have eq54343 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op X2 (M.op X3 (σ x)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq54309 X0 X1 X2 X3
       have i₂ := eq39339
       grind)
    | exact superpose eq39339 eq54309
    | exact resolve eq54309 eq39339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54309
  have eq54367 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq54212 X0
       have i₂ := eq39339
       grind)
    | exact superpose eq39339 eq54212
    | exact resolve eq54212 eq39339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39339 eq54212
  have eq54385 : ∀ X0 X2 X3 : G, (M.op X0 x) = (M.op X0 (M.op X2 (M.op X3 (σ x)))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq54343 X0 x X2 X3
       have i₂ := eq37913 X0 x
       grind)
    | exact superpose eq37913 eq54343
    | exact resolve eq54343 eq37913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54343
  have eq54397 : (σ x) = (M.op (σ x) x) := by
    first
    | (have i₁ := eq54367 x
       have i₂ := eq37913 (σ x) x
       grind)
    | exact superpose eq37913 eq54367
    | exact resolve eq54367 eq37913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37913 eq54367
  have eq54536 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op x X0) = (M.op x (M.op X1 (M.op X2 (M.op X3 (M.op (M.op X4 X5) X6))))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq3567 X2 X3 X4 X5 X6 x x X0 X1
       have i₂ := eq36436
       grind)
    | exact superpose eq36436 eq3567
    | exact resolve eq3567 eq36436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3567
  have eq56227 : ∀ X0 X1 X2 : G, (M.op x X0) = (M.op x (M.op X1 (M.op X2 (σ x)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54536 X0 X1 X2 x x x x
       have i₂ := eq54342 X2 x x x x
       grind)
    | exact superpose eq54342 eq54536
    | exact resolve eq54536 eq54342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54342 eq54536
  have eq56284 : ∀ X0 : G, (M.op x X0) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq56227 X0 x x
       have i₂ := eq54385 x x x
       grind)
    | exact superpose eq54385 eq56227
    | exact resolve eq56227 eq54385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54385 eq56227
  have eq56327 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq56284 X0
       have i₂ := eq36436
       grind)
    | exact superpose eq36436 eq56284
    | exact resolve eq56284 eq36436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36436 eq56284
  have eq56701 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X0 x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq155 x x x X0 X1 X2 x
       have i₂ := eq56327 (M.op (M.op x x) x)
       grind)
    | exact superpose eq56327 eq155
    | exact resolve eq155 eq56327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq102333 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq56701 (σ x) x x
       have i₂ := eq54397
       grind)
    | exact superpose eq54397 eq56701
    | exact resolve eq56701 eq54397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54397 eq56701
  have eq103992 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq102333 (σ y)
       grind)
    | exact superpose eq102333 eq14
    | exact resolve eq14 eq102333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102333
  have eq104609 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq103992
       have i₂ := eq56327 y
       grind)
    | exact superpose eq56327 eq103992
    | exact resolve eq103992 eq56327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56327 eq103992
  have eq104610 : False := by grind
  exact eq104610

/-- `Equation4444`: `x ◇ (y ◇ x) = (y ◇ x) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyx_y_x_pxy_Equation4444 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4444 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4444.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X0) X2) := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq15 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 X0 X3
       have i₂ := eq8 X1 X0 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) X2)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op X1 X0) X0 X2
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 (M.op X1 X0))) = (M.op (M.op X0 (M.op X1 X0)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 (M.op X1 X0) X2
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X2)) X3) = (M.op X2 (M.op X1 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 X1 (M.op X0 (M.op X1 X2))
       have i₂ := eq8 (M.op X1 X2) X0 X3
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20 X0 X1 X2 x
       have i₂ := eq21 X0 X1 X0 x
       grind)
    | exact superpose eq21 eq20
    | exact resolve eq20 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq25 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 X0 X1 X2 X3
       have i₂ := eq8 X1 X0 (M.op (M.op X0 X1) X2)
       grind)
    | exact superpose eq8 eq19
    | exact resolve eq19 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq29 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq9
    | exact resolve eq9 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq15
    | (have j1 := eq12 (τ X0) X1
       grind)
    | exact resolve eq15 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq16 X1 X0
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq29
    | exact resolve eq29 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq72 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op (M.op X0 X1) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21 X0 X1 X0 X3
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq21
    | exact resolve eq21 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 X3 X4 X5 : G, (M.op X4 (M.op X3 X4)) = (M.op (M.op X0 (M.op X1 X0)) X5) := by
    intro X0 X1 X3 X4 X5
    first
    | (have i₁ := eq21 (M.op x (M.op X1 X0)) X3 X4 X5
       have i₂ := eq21 x X1 X0 (M.op X3 X4)
       grind)
    | exact superpose eq21 eq21
    | exact resolve eq21 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 X1 X3 X4 : G, (M.op X0 (M.op X1 X0)) = (M.op X4 (M.op X3 X4)) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq76 X4 X3 X1 X0 x
       have i₂ := eq21 X4 X3 X4 x
       grind)
    | exact superpose eq21 eq76
    | exact resolve eq76 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq76
  have eq154 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X3) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq17 X2 X3 (M.op X0 (M.op X1 X0)) X4
       have i₂ := eq24 X0 X1 (M.op X2 X3)
       grind)
    | exact superpose eq24 eq17
    | exact resolve eq17 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op (M.op X0 X1) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 X1 X0 X4
       have i₂ := eq25 X0 X1 X2 X3
       grind)
    | exact superpose eq25 eq8
    | exact resolve eq8 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq230 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) ≠ (M.op (M.op X1 X0) X2) ∨ (k X3 (M.op (M.op X1 X0) X2)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq11 X3 (M.op (M.op X1 X0) X2)
       have i₂ := eq25 X1 X0 X2 X3
       grind)
    | exact superpose eq25 eq11
    | (have j0 := eq11 X3 (M.op (M.op X1 X0) X2)
       grind)
    | exact resolve eq11 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq236 : ∀ X0 X1 X2 X3 : G, (k X3 (M.op (M.op X1 X0) X2)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq230 X0 X1 X2 X3
       grind)
    | (have r₁ := eq230 X0 X1 X2 X3
       have r₂ := eq8 X0 X1 X2
       grind)
    | exact resolve eq230 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230
  have eq273 : ∀ X0 X1 X2 : G, (k X2 (M.op X0 (M.op X1 X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq236 x x (M.op X0 (M.op X1 X0)) X2
       have i₂ := eq24 X0 X1 (M.op x x)
       grind)
    | exact superpose eq24 eq236
    | exact resolve eq236 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq327 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 (M.op X2 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X0 (M.op X1 (M.op X2 X1))
       have i₂ := eq273 X1 X2 (τ X0)
       grind)
    | exact superpose eq273 eq15
    | exact resolve eq15 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq329 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op X1 (M.op X2 X1)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq327 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq327
    | exact resolve eq327 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327
  have eq400 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X1 X0
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq31
    | (have j0 := eq31 X1 X0
       have j1 := eq31 X1 X0
       grind)
    | exact resolve eq31 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq402 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X1) (σ X0)
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq11
    | (have j0 := eq11 (σ X1) (σ X0)
       have j1 := eq31 X0 X1
       grind)
    | (have r₁ := eq11 (σ X0) (σ X1)
       have r₂ := eq31 X0 X1
       grind)
    | exact resolve eq11 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq412 : ∀ X0 X1 X2 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) X2) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (σ X0) (σ X1) X2
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq8
    | (have j1 := eq31 X1 X0
       grind)
    | exact resolve eq8 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq413 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X1) (σ X0)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq11
    | (have j0 := eq11 (σ X1) (σ X0)
       have j1 := eq31 X1 X0
       grind)
    | (have r₁ := eq11 (σ X0) (σ X1)
       have r₂ := eq31 X0 X1
       grind)
    | exact resolve eq11 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq414 : ∀ X0 X1 X2 X3 : G, (M.op (σ X0) X2) = (M.op (σ X0) X3) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq17 (σ X1) (σ X0) X2 X3
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq17
    | (have j1 := eq31 X1 X0
       grind)
    | exact resolve eq17 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq423 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq31 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq424 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq413 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413
  have eq426 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq424 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq424
    | (have j0 := eq424 X0 X1
       grind)
    | exact resolve eq424 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424
  have eq428 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq402 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq402
    | (have j0 := eq402 X0 X1
       grind)
    | exact resolve eq402 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402
  have eq661 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 X1)) = (M.op (σ X0) X4) ∨ (M.op (σ X3) (σ X0)) = (σ (k X3 X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq154 X1 X2 (σ X0) (σ X3) X4
       have i₂ := eq31 X3 X0
       grind)
    | exact superpose eq31 eq154
    | (have j1 := eq31 X3 X0
       grind)
    | exact resolve eq154 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq154
  have eq6896 : ∀ X0 X1 X2 : G, (σ (M.op (M.op X0 X1) X2)) ≠ (σ (M.op (M.op X0 X1) X2)) ∨ (σ (M.op (M.op X0 X1) X2)) = (M.op (σ (M.op (M.op X0 X1) X2)) (σ (M.op (M.op X0 X1) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq423 (M.op (M.op X0 X1) X2)
       have i₂ := eq236 X1 X0 X2 (M.op (M.op X0 X1) X2)
       grind)
    | exact superpose eq236 eq423
    | (have j0 := eq423 (M.op (M.op X0 X1) X2)
       grind)
    | exact resolve eq423 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236 eq423
  have eq6931 : ∀ X0 X1 X2 : G, (σ (M.op (M.op X0 X1) X2)) = (M.op (σ (M.op (M.op X0 X1) X2)) (σ (M.op (M.op X0 X1) X2))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq6896 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6896
  have eq6982 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq32 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq32
    | exact resolve eq32 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq7042 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6982 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq6982
    | (have j0 := eq6982 X0 X1
       grind)
    | exact resolve eq6982 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6982
  have eq9318 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq426 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq426
    | exact resolve eq426 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426
  have eq9400 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9318 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq9318
    | (have j0 := eq9318 X0 X1
       grind)
    | exact resolve eq9318 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9318
  have eq9402 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9400 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq9400
    | (have j0 := eq9400 X0 X1
       grind)
    | exact resolve eq9400 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9400
  have eq10348 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X2 (M.op X3 X2)) = (M.op (σ X1) (σ (k X0 X1))) ∨ (M.op (σ X1) X4) = (M.op (σ X1) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq111 X2 X3 (σ X0) (σ X1)
       have i₂ := eq414 X1 X0 X4 X5
       grind)
    | exact superpose eq414 eq111
    | (have j1 := eq414 X1 X1 X4 X5
       grind)
    | exact resolve eq111 eq414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414
  have eq11111 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9402 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9402
    | exact resolve eq9402 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9402
  have eq11455 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11111 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11638 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) ≠ (M.op (M.op X0 X1) X2) ∨ (M.op (M.op X0 X1) X2) = (k (M.op (M.op X0 X1) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq11455 (M.op (M.op X0 X1) X2) X3
       have i₂ := eq72 X0 X1 X2 X3
       grind)
    | exact superpose eq72 eq11455
    | (have j0 := eq11455 (M.op (M.op X0 X1) X2) X3
       grind)
    | (have r₁ := eq11455 (M.op (M.op X0 X1) X2) X3
       have r₂ := eq72 X0 X1 X2 X3
       grind)
    | exact resolve eq11455 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq11651 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (k (M.op (M.op X0 X1) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq11638 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11638
  have eq12223 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) X2) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq412 X1 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412
  have eq15592 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq428 (τ X0) (τ X1)
       have i₂ := eq62 X1 X0
       grind)
    | exact superpose eq62 eq428
    | (have j0 := eq428 (τ X0) (τ X1)
       grind)
    | exact resolve eq428 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428
  have eq15626 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X1)) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15592 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq15592
    | (have j0 := eq15592 X0 X1
       grind)
    | exact resolve eq15592 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15592
  have eq15642 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15626 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15626
    | (have j0 := eq15626 X0 X1
       grind)
    | exact resolve eq15626 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15626
  have eq15655 : ∀ X0 X1 : G, (σ (τ X1)) = (k (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15642 X0 X1
       have i₂ := eq16 X0 (τ X1)
       grind)
    | exact superpose eq16 eq15642
    | (have j0 := eq15642 X0 X1
       grind)
    | exact resolve eq15642 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15642
  have eq15664 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15655 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15655
    | (have j0 := eq15655 X0 X1
       grind)
    | exact resolve eq15655 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15655
  have eq15671 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X1 X0) = X1 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15664 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15664
    | (have j0 := eq15664 X0 X1
       grind)
    | exact resolve eq15664 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15664
  have eq15672 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X1 X0) = X1 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15671 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15671
    | (have j0 := eq15671 X0 X1
       grind)
    | exact resolve eq15671 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15671
  have eq15673 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq15672 X0 X1
       have j1 := eq11455 X1 X0
       grind)
    | (have r₁ := eq15672 X1 X0
       have r₂ := eq11455 X0 X1
       grind)
    | (have r₁ := eq15672 X0 X1
       have r₂ := eq11455 X0 X1
       grind)
    | exact resolve eq15672 eq11455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15672
  have eq20759 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq400 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq400
    | exact resolve eq400 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400
  have eq20897 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq20759 X0 X1
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq20759
    | (have j0 := eq20759 X0 X1
       grind)
    | exact resolve eq20759 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq20759
  have eq20899 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq20897 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq20897
    | (have j0 := eq20897 X0 X1
       grind)
    | exact resolve eq20897 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq20897
  have eq20901 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq20899 X0 X1
       have j1 := eq11 X0 (σ X1)
       grind)
    | (have r₁ := eq20899 X0 X1
       have r₂ := eq11 X0 (σ X1)
       grind)
    | exact resolve eq20899 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20899
  have eq20971 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (M.op (σ X1) (σ X0)) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq39 X0 (σ X1)
       have i₂ := eq20901 (σ X0) X1
       grind)
    | exact superpose eq20901 eq39
    | (have j1 := eq20901 (σ X0) X1
       grind)
    | exact resolve eq39 eq20901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq20901
  have eq21066 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (M.op (σ X1) (σ X0)) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20971 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq20971
    | (have j0 := eq20971 X0 X1
       grind)
    | exact resolve eq20971 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20971
  have eq21089 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op (σ X1) (σ X0)) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq21066 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq21066
    | (have j0 := eq21066 X0 X1
       grind)
    | exact resolve eq21066 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21066
  have eq21097 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq21089 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq21089
    | (have j0 := eq21089 X0 X1
       grind)
    | exact resolve eq21089 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21089
  have eq23208 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq21097 y x
       grind)
    | exact superpose eq21097 eq14
    | (have j1 := eq21097 y x
       grind)
    | exact resolve eq14 eq21097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21097
  have eq23566 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq23208
       have i₂ := eq7042 x y
       grind)
    | exact superpose eq7042 eq23208
    | (have j1 := eq7042 x y
       grind)
    | (have r₁ := eq23208
       have r₂ := eq7042 x y
       grind)
    | exact resolve eq23208 eq7042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7042 eq23208
  have eq23567 : y = (k y x) ∨ y = (M.op y x) := by grind
  clear eq23566
  have eq23570 : y = (k y x) := by
    first
    | (have j1 := eq11455 y x
       grind)
    | (have r₁ := eq23567
       have r₂ := eq11455 y x
       grind)
    | exact resolve eq23567 eq11455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11455 eq23567
  have eq23728 : y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq23570
       grind)
    | exact superpose eq23570 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq23570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25141 : ∀ X0 X1 : G, (M.op y X0) = (M.op y X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq17 y x x x
       have i₂ := eq23728
       grind)
    | exact superpose eq23728 eq17
    | exact resolve eq17 eq23728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq28477 : ∀ X0 : G, y = (M.op y X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq23728
       have i₂ := eq25141 x X0
       grind)
    | (have i₁ := eq23728
       have i₂ := eq25141 X0 x
       grind)
    | exact superpose eq25141 eq23728
    | exact resolve eq23728 eq25141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23728 eq25141
  have eq28637 : ∀ X0 : G, y = (M.op y X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq28477 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28477
  have eq29525 : ∀ X1 : G, y = (M.op X1 y) ∨ x = (M.op x y) := by
    intro X1
    first
    | (have i₁ := eq24 y X1 x
       have i₂ := eq28637 (M.op X1 y)
       grind)
    | exact superpose eq28637 eq24
    | exact resolve eq24 eq28637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28637
  have eq30711 : ∀ X0 X1 : G, (k X0 (M.op y x)) = X0 ∨ y = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq273 y x X0
       have i₂ := eq29525 X1
       grind)
    | exact superpose eq29525 eq273
    | (have j1 := eq29525 X1
       grind)
    | exact resolve eq273 eq29525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273 eq29525
  have eq33017 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) ≠ (M.op (σ (τ X1)) X2) ∨ (M.op (σ (τ X1)) X2) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12223 (τ X0) (τ X1) X2
       have i₂ := eq62 X1 X0
       grind)
    | exact superpose eq62 eq12223
    | (have j0 := eq12223 (τ X0) (τ X1) X2
       grind)
    | exact resolve eq12223 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12223
  have eq33131 : ∀ X0 X1 X2 : G, (M.op X1 X2) ≠ (σ (τ (k X0 X1))) ∨ (M.op (σ (τ X1)) X2) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33017 X0 X1 X2
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq33017
    | (have j0 := eq33017 X0 X1 X2
       grind)
    | exact resolve eq33017 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33017
  have eq33155 : ∀ X0 X1 X2 : G, (k X0 X1) ≠ (M.op X1 X2) ∨ (M.op (σ (τ X1)) X2) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33131 X0 X1 X2
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq33131
    | (have j0 := eq33131 X0 X1 X2
       grind)
    | exact resolve eq33131 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33131
  have eq33168 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ (M.op X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33155 X0 X0 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq33155
    | (have j0 := eq33155 X0 X1 X2
       grind)
    | exact resolve eq33155 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33155
  have eq33171 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X1 X2) ∨ (k X0 X1) ≠ (M.op X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33168 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq33168
    | (have j0 := eq33168 X0 X1 X2
       grind)
    | exact resolve eq33168 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33168
  have eq37931 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X2 (M.op X3 X2)) = (M.op (σ X1) (σ (k X0 X1))) ∨ (M.op X4 (M.op X5 X4)) = (M.op (σ X1) X6) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq111 X2 X3 (σ X0) (σ X1)
       have i₂ := eq661 X1 X4 X5 X0 X6
       grind)
    | exact superpose eq661 eq111
    | (have j1 := eq661 X1 X2 X3 X3 (σ (k X0 X1))
       grind)
    | exact resolve eq111 eq661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661
  have eq46960 : ∀ X2 X3 : G, y = (k y X2) ∨ (k X3 (M.op y x)) = X3 := by
    intro X2 X3
    first
    | (have i₁ := eq11651 x x y X3
       have i₂ := eq30711 x (M.op x x)
       grind)
    | exact superpose eq30711 eq11651
    | (have j1 := eq30711 X3 x
       grind)
    | exact resolve eq11651 eq30711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30711
  have eq81188 : y ≠ y ∨ y = (k y (M.op y x)) := by
    first
    | (have j0 := eq46960 (M.op y x) y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46960
  have eq81189 : y = (k y (M.op y x)) := by grind
  clear eq81188
  have eq81742 : y ≠ y ∨ (M.op y x) = (k (M.op y x) y) := by
    first
    | (have i₁ := eq15673 y (M.op y x)
       have i₂ := eq81189
       grind)
    | exact superpose eq81189 eq15673
    | (have j0 := eq15673 y (M.op y x)
       grind)
    | (have r₁ := eq15673 y (M.op y x)
       have r₂ := eq81189
       grind)
    | exact resolve eq15673 eq81189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15673 eq81189
  have eq81748 : (M.op y x) = (k (M.op y x) y) := by grind
  clear eq81742
  have eq82733 : (M.op y x) = (M.op (M.op y x) y) ∨ (M.op y x) = (k (M.op y x) y) := by
    first
    | (have i₁ := eq81748
       have i₂ := eq11111 y (M.op y x)
       grind)
    | exact superpose eq11111 eq81748
    | (have j1 := eq11111 y (M.op y x)
       grind)
    | exact resolve eq81748 eq11111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11111 eq81748
  have eq82767 : (M.op y x) = (M.op (M.op y x) y) := by
    first
    | (have j1 := eq33171 (M.op y x) y x
       grind)
    | (have r₁ := eq82733
       have r₂ := eq33171 (M.op y x) y x
       grind)
    | exact resolve eq82733 eq33171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33171 eq82733
  have eq82768 : (M.op y x) = (M.op x (M.op y x)) := by
    first
    | (have i₁ := eq82767
       have i₂ := eq8 x y y
       grind)
    | exact superpose eq8 eq82767
    | exact resolve eq82767 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82767
  have eq83774 : ∀ X0 : G, (M.op y x) = (M.op X0 (M.op y x)) := by
    intro X0
    first
    | (have i₁ := eq24 x y x
       have i₂ := eq82768
       grind)
    | exact superpose eq82768 eq24
    | exact resolve eq24 eq82768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq83777 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq111 X0 X1 y x
       have i₂ := eq82768
       grind)
    | exact superpose eq82768 eq111
    | exact resolve eq111 eq82768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq82768
  have eq86907 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X3) = (M.op y x) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq210 X0 X1 x (M.op y x) X3
       have i₂ := eq83774 (M.op (M.op X0 X1) x)
       grind)
    | exact superpose eq83774 eq210
    | exact resolve eq210 eq83774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210 eq83774
  have eq95140 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X4 X3)) ≠ (M.op (σ X0) X2) ∨ (M.op X3 (M.op X4 X3)) = (M.op (σ X0) (σ (k X1 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have j0 := eq10348 X1 X0 X3 X4 X4 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10348
  have eq95142 : ∀ X0 X1 X3 X4 : G, (M.op X3 (M.op X4 X3)) = (M.op (σ X0) (σ (k X1 X0))) := by
    intro X0 X1 X3 X4
    first
    | (have j0 := eq95140 X0 X1 x X3 X4
       have j1 := eq37931 X1 X0 X3 X4 X3 X4 (σ (k X1 X0))
       grind)
    | (have r₁ := eq95140 X1 X1 (σ (k X0 X1)) x X3
       have r₂ := eq37931 X0 X1 x X3 X4 x x
       grind)
    | (have r₁ := eq95140 X1 X1 x X4 x
       have r₂ := eq37931 X0 X1 x X3 X4 x x
       grind)
    | (have r₁ := eq95140 X0 X1 (M.op x (σ X0)) (σ X1) X4
       have r₂ := eq37931 X0 X1 x X3 (σ X0) x (M.op X4 (σ X1))
       grind)
    | exact resolve eq95140 eq37931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37931 eq95140
  have eq95916 : ∀ X0 X1 : G, (M.op (σ X0) (σ (k X1 X0))) = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq95142 X0 X1 x x
       have i₂ := eq83777 x x
       grind)
    | exact superpose eq83777 eq95142
    | exact resolve eq95142 eq83777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95142
  have eq109053 : ∀ X0 X1 : G, (M.op (σ (τ X1)) (σ (τ (k X0 X1)))) = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq95916 (τ X1) (τ X0)
       have i₂ := eq62 X1 X0
       grind)
    | exact superpose eq62 eq95916
    | exact resolve eq95916 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq109066 : (M.op (σ x) (σ y)) = (M.op y x) := by
    first
    | (have i₁ := eq95916 x y
       have i₂ := eq23570
       grind)
    | exact superpose eq23570 eq95916
    | exact resolve eq95916 eq23570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95916
  have eq109407 : ∀ X0 X1 : G, (M.op (σ (τ X1)) (k X0 X1)) = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq109053 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq109053
    | exact resolve eq109053 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109053
  have eq109452 : ∀ X0 X1 : G, (M.op X1 (k X0 X1)) = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq109407 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq109407
    | exact resolve eq109407 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109407
  have eq110225 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X1 (M.op X2 X1))) X0) = (M.op y x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq109452 X0 (σ (M.op X1 (M.op X2 X1)))
       have i₂ := eq329 X0 X1 X2
       grind)
    | exact superpose eq329 eq109452
    | exact resolve eq109452 eq329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329
  have eq110261 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X0 X1) X2)) = (M.op y x) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq109452 (M.op (M.op X0 X1) X2) X3
       have i₂ := eq11651 X0 X1 X2 X3
       grind)
    | exact superpose eq11651 eq109452
    | exact resolve eq109452 eq11651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11651
  have eq110295 : (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq109452 y x
       have i₂ := eq23570
       grind)
    | exact superpose eq23570 eq109452
    | exact resolve eq109452 eq23570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23570 eq109452
  have eq110769 : ∀ X0 X1 X2 X3 : G, (M.op x y) = (M.op X3 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq110261 X0 X1 X2 X3
       have i₂ := eq110295
       grind)
    | exact superpose eq110295 eq110261
    | exact resolve eq110261 eq110295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110261
  have eq110797 : ∀ X0 X1 X2 : G, (M.op x y) = (M.op (σ (M.op X1 (M.op X2 X1))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq110225 X0 X1 X2
       have i₂ := eq110295
       grind)
    | exact superpose eq110295 eq110225
    | exact resolve eq110225 eq110295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110225
  have eq110803 : ∀ X3 : G, (M.op x y) = (M.op X3 (M.op y x)) := by
    intro X3
    first
    | (have i₁ := eq110769 x x x X3
       have i₂ := eq86907 x x x
       grind)
    | exact superpose eq86907 eq110769
    | exact resolve eq110769 eq86907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86907 eq110769
  have eq110823 : ∀ X0 : G, (M.op x y) = (M.op (σ (M.op y x)) X0) := by
    intro X0
    first
    | (have i₁ := eq110797 X0 x x
       have i₂ := eq83777 x x
       grind)
    | exact superpose eq83777 eq110797
    | exact resolve eq110797 eq83777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83777 eq110797
  have eq110827 : ∀ X3 : G, (M.op x y) = (M.op X3 (M.op x y)) := by
    intro X3
    first
    | (have i₁ := eq110803 X3
       have i₂ := eq110295
       grind)
    | exact superpose eq110295 eq110803
    | exact resolve eq110803 eq110295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110803
  have eq110847 : ∀ X0 : G, (M.op x y) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq110823 X0
       have i₂ := eq110295
       grind)
    | exact superpose eq110295 eq110823
    | exact resolve eq110823 eq110295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110823
  have eq114754 : (σ (M.op x y)) ≠ (M.op y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq109066
       grind)
    | exact superpose eq109066 eq14
    | exact resolve eq14 eq109066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109066
  have eq114971 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq114754
       have i₂ := eq110295
       grind)
    | exact superpose eq110295 eq114754
    | exact resolve eq114754 eq110295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110295 eq114754
  have eq119027 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq6931 x x (M.op x y)
       have i₂ := eq110827 (M.op x x)
       grind)
    | exact superpose eq110827 eq6931
    | exact resolve eq6931 eq110827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6931 eq110827
  have eq119207 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq119027
       have i₂ := eq110847 (σ (M.op x y))
       grind)
    | exact superpose eq110847 eq119027
    | exact resolve eq119027 eq110847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110847 eq119027
  have eq119256 : False := by grind
  exact eq119256
