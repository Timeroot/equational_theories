import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4391`: `x ◇ (x ◇ x) = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_x_y_pxy_Equation4391 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law4391 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4391.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X2) X0) := by
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
  have eq18 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X4) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 X2 X3 X4
       have i₂ := eq8 X2 X0 X1
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
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 X2 X3
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq12 (M.op X0 X0) X1
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq29 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X1 (M.op X1 X1)) ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2 X2
       have i₂ := eq12 X0 X2
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq12 (M.op X1 X2) X1
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X0 X2
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 X2)) = (M.op X0 (M.op X1 X2)) ∨ (M.op (M.op X1 X2) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op X1 X2) X1 X2
       have i₂ := eq12 X0 (M.op X1 X2)
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq12 (M.op (M.op X1 X2) X0) X1
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X0 (M.op X1 X2)
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
  have eq32 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
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
  have eq34 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    grind
  have eq40 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq43 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq34 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq34
    | exact resolve eq34 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq76 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq79 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    grind
  have eq86 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq79 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq79
    | exact resolve eq79 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq87 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq28 (σ X0) (σ X1)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq28
    | exact resolve eq28 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq28 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq40 X0 X1
       have i₂ := eq12 (σ X0) X1
       grind)
    | exact superpose eq12 eq40
    | (have j1 := eq12 (σ X0) X1
       grind)
    | exact resolve eq40 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq145 : ∀ X0 X1 X2 : G, (k (M.op (M.op X0 X1) X2) X2) = X2 ∨ (M.op X2 X2) = (k X2 X2) := by
    intro X0 X1 X2
    grind
  clear eq27
  have eq163 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq43 X1
       have i₂ := eq12 X0 (τ X1)
       grind)
    | (have i₁ := eq43 X0
       have i₂ := eq12 (M.op (τ X0) (τ X0)) X1
       grind)
    | exact superpose eq12 eq43
    | (have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq43 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq173 : ∀ X0 : G, (σ (τ X0)) = (k (σ (σ (M.op (τ (τ X0)) (τ (τ X0))))) X0) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (σ (M.op (τ (τ X0)) (τ (τ X0))))
       have i₂ := eq43 (τ X0)
       grind)
    | exact superpose eq43 eq17
    | exact resolve eq17 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, (k (σ (σ (M.op (τ (τ X0)) (τ (τ X0))))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq173 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq173
    | exact resolve eq173 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173
  have eq226 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 (M.op X2 X2)) = (M.op (σ X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq29 (σ X0) X2 (σ X1)
       grind)
    | exact superpose eq29 eq13
    | (have j1 := eq29 (σ X0) X2 X2
       grind)
    | exact resolve eq13 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq237 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X2) ≠ X2 ∨ (k (M.op X3 X4) X2) = X2 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq93 (M.op X3 X4) X2
       have i₂ := eq18 X3 X4 X2 X0 X1
       grind)
    | (have i₁ := eq93 (M.op X3 X4) X2
       have i₂ := eq18 X0 X1 X2 X3 X4
       grind)
    | exact superpose eq18 eq93
    | (have j0 := eq93 (M.op X0 X1) X2
       grind)
    | exact resolve eq93 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq302 : ∀ X0 X1 : G, (k (τ X0) X1) = X1 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq86 X1
       have i₂ := eq12 X0 (σ X1)
       grind)
    | (have i₁ := eq86 X0
       have i₂ := eq12 (M.op (σ X0) (σ X0)) X1
       grind)
    | exact superpose eq12 eq86
    | (have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq86 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq338 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X1 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq31
    | (have j0 := eq31 X0 X1
       have j1 := eq31 X0 X1
       grind)
    | exact resolve eq31 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq339 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq12 X0 (σ X0)
       grind)
    | (have i₁ := eq31 X0 X1
       have i₂ := eq12 (M.op (σ X0) (σ X1)) X1
       grind)
    | exact superpose eq12 eq31
    | (have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq31 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq367 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq9
    | (have j1 := eq31 X1 X0
       grind)
    | exact resolve eq9 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq377 : ∀ X0 X1 : G, (k (τ (σ X0)) X1) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq86 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq86
    | (have j1 := eq31 X0 X1
       grind)
    | exact resolve eq86 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq390 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq31 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq394 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq377 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq377
    | (have j0 := eq377 X0 X1
       grind)
    | exact resolve eq377 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377
  have eq795 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq390 (τ X0)
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq390
    | (have j0 := eq390 (τ X0)
       grind)
    | exact resolve eq390 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq797 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq795 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq795
    | (have j0 := eq795 X0
       grind)
    | exact resolve eq795 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq795
  have eq800 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq797 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq797
    | (have j0 := eq797 X0
       grind)
    | exact resolve eq797 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq797
  have eq812 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq800 (τ X0)
       have i₂ := eq76 X0 X0
       grind)
    | exact superpose eq76 eq800
    | (have j0 := eq800 (τ X0)
       grind)
    | exact resolve eq800 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq824 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
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
  have eq857 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq10
    | (have j1 := eq32 X1 X0
       grind)
    | exact resolve eq10 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq897 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = X1 ∨ (k X0 (σ (τ X1))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq43 X1
       have i₂ := eq32 X0 (τ X1)
       grind)
    | exact superpose eq32 eq43
    | (have j1 := eq32 X0 (τ X1)
       grind)
    | exact resolve eq43 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq900 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (k X0 (σ (τ X1))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq897 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq897
    | (have j0 := eq897 X0 X1
       grind)
    | exact resolve eq897 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq897
  have eq913 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq824 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq824
    | (have j0 := eq824 X0 X1
       grind)
    | exact resolve eq824 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824
  have eq920 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq900 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq900
    | (have j0 := eq900 X0 X1
       grind)
    | exact resolve eq900 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900
  have eq975 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq1000 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (σ (k X0 (τ X1))) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq43 X1
       have i₂ := eq913 X0 (τ X1)
       grind)
    | (have i₁ := eq43 X0
       have i₂ := eq913 (M.op (τ X0) (τ X0)) X1
       grind)
    | exact superpose eq913 eq43
    | (have j1 := eq913 X0 (τ X1)
       grind)
    | exact resolve eq43 eq913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq1005 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1000 X0 X1
       have i₂ := eq17 X1 X0
       grind)
    | exact superpose eq17 eq1000
    | (have j0 := eq1000 X0 X1
       grind)
    | exact resolve eq1000 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1000
  have eq1530 : ∀ X0 : G, (k (M.op X0 (M.op X0 X0)) X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq145 x x X0
       have i₂ := eq8 X0 x x
       grind)
    | exact superpose eq8 eq145
    | (have j0 := eq145 X0 x X0
       grind)
    | exact resolve eq145 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq1862 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq87 X0 X0
       grind)
    | exact superpose eq87 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq87 X0 X0
       grind)
    | exact resolve eq12 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq2342 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (τ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq367 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq367
    | exact resolve eq367 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367
  have eq2393 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (τ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2342 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq2342
    | (have j0 := eq2342 X0 X1
       grind)
    | exact resolve eq2342 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2342
  have eq3316 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X0)) ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq163 X1 (σ X0)
       grind)
    | exact superpose eq163 eq13
    | (have j1 := eq163 X1 (σ X0)
       grind)
    | exact resolve eq13 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3364 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X0)) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3316 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq3316
    | (have j0 := eq3316 X0 X1
       grind)
    | exact resolve eq3316 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3316
  have eq3538 : ∀ X0 X1 : G, (M.op (τ X1) X0) = (k (τ X1) X0) ∨ (σ X0) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq3364 X0 (τ X1)
       grind)
    | exact superpose eq3364 eq16
    | (have j1 := eq3364 X0 (τ X1)
       grind)
    | exact resolve eq16 eq3364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3364
  have eq5020 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2393 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2393
    | (have j0 := eq2393 X1 (τ X0)
       grind)
    | exact resolve eq2393 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5350 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (M.op (σ X1) (σ X1))) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq226 X0 X1 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq6364 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k X0 (σ (τ X0))) = (M.op X0 (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq800 (τ X0)
       have i₂ := eq302 X0 (τ X0)
       grind)
    | exact superpose eq302 eq800
    | (have j0 := eq800 (τ X0)
       have j1 := eq302 X0 (τ X0)
       grind)
    | (have r₁ := eq800 (τ X0)
       have r₂ := eq302 X0 (τ X0)
       grind)
    | exact resolve eq800 eq302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302 eq800
  have eq6395 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k X0 (σ (τ X0))) = (M.op X0 (σ (τ X0))) := by
    intro X0
    first
    | (have j0 := eq6364 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6364
  have eq6411 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq6395 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6395
    | (have j0 := eq6395 X0
       grind)
    | exact resolve eq6395 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6395
  have eq7447 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq394 x y
       grind)
    | exact superpose eq394 eq14
    | (have j1 := eq394 x y
       grind)
    | exact resolve eq14 eq394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7512 : y = (k x y) := by
    first
    | (have j1 := eq975 x y
       grind)
    | (have r₁ := eq7447
       have r₂ := eq975 x y
       grind)
    | exact resolve eq7447 eq975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq975 eq7447
  have eq8038 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq913 x y
       have i₂ := eq7512
       grind)
    | exact superpose eq7512 eq913
    | (have j0 := eq913 x y
       grind)
    | exact resolve eq913 eq7512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11702 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X1 X1)
       have i₂ := eq338 X0 X1
       grind)
    | (have i₁ := eq9 X0
       have i₂ := eq338 X0 X1
       grind)
    | exact superpose eq338 eq9
    | (have j1 := eq338 X0 X1
       grind)
    | exact resolve eq9 eq338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq11770 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X1 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11702 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq11702
    | (have j0 := eq11702 X0 X1
       grind)
    | exact resolve eq11702 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11702
  have eq26397 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (τ X0) (τ X1)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq101 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq101
    | exact resolve eq101 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq26904 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq26397 X0 X1
       have i₂ := eq76 X1 X0
       grind)
    | exact superpose eq76 eq26397
    | (have j0 := eq26397 X0 X1
       grind)
    | exact resolve eq26397 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26397
  have eq28380 : ∀ X0 X1 : G, (k (τ X0) X1) = X1 ∨ (τ (k X0 (σ X1))) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq86 X1
       have i₂ := eq26904 X0 (σ X1)
       grind)
    | (have i₁ := eq86 X0
       have i₂ := eq26904 (M.op (σ X0) (σ X0)) X1
       grind)
    | exact superpose eq26904 eq86
    | (have j1 := eq26904 X0 (σ X1)
       grind)
    | exact resolve eq86 eq26904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq26904
  have eq28477 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (k (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28380 X0 X1
       have i₂ := eq24 X0 X1
       grind)
    | exact superpose eq24 eq28380
    | (have j0 := eq28380 X0 X1
       grind)
    | exact resolve eq28380 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28380
  have eq32549 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq857 X1 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq857
    | (have j0 := eq857 X1 (σ X0)
       grind)
    | exact resolve eq857 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32741 : ∀ X0 X1 : G, (τ (k X0 (σ X1))) = (M.op (τ X0) X1) ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (τ X0) X1)
       have i₂ := eq857 X1 X0
       grind)
    | exact superpose eq857 eq9
    | (have j1 := eq857 X1 X0
       grind)
    | exact resolve eq9 eq857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32849 : ∀ X0 : G, (k X0 (σ (τ X0))) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq857 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857
  have eq32850 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq32849 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq32849
    | (have j0 := eq32849 X0
       grind)
    | exact resolve eq32849 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32849
  have eq32855 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq32741 X0 X1
       have i₂ := eq24 X0 X1
       grind)
    | exact superpose eq24 eq32741
    | (have j0 := eq32741 X0 X1
       grind)
    | exact resolve eq32741 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32741
  have eq32894 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq32549 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq32549
    | (have j0 := eq32549 X0 X1
       grind)
    | exact resolve eq32549 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32549
  have eq33691 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) ∨ (k X0 (τ (σ X0))) = (M.op X0 (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq32850 (σ X0)
       have i₂ := eq163 X0 (σ X0)
       grind)
    | exact superpose eq163 eq32850
    | (have j0 := eq32850 (σ X0)
       have j1 := eq163 X0 (σ X0)
       grind)
    | (have r₁ := eq32850 (σ X0)
       have r₂ := eq163 X0 (σ X0)
       grind)
    | exact resolve eq32850 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq33697 : ∀ X0 : G, (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) ∨ (k X0 (τ (σ X0))) = (M.op X0 (τ (σ X0))) := by
    intro X0
    first
    | (have j0 := eq33691 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33691
  have eq33699 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k X0 (τ (σ X0))) = (M.op X0 (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq33697 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq33697
    | (have j0 := eq33697 X0
       grind)
    | exact resolve eq33697 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33697
  have eq33707 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq33699 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq33699
    | (have j0 := eq33699 X0
       grind)
    | exact resolve eq33699 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33699
  have eq36531 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (k X1 X1) = X0 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq33707 X1
       have i₂ := eq913 X0 X1
       grind)
    | (have i₁ := eq33707 X0
       have i₂ := eq913 (M.op X0 X0) X1
       grind)
    | exact superpose eq913 eq33707
    | (have j1 := eq913 X0 X1
       grind)
    | exact resolve eq33707 eq913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq913 eq33707
  have eq37616 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq32855 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq32855
    | (have j0 := eq32855 (σ X0) X1
       grind)
    | exact resolve eq32855 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32855
  have eq51056 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1005 X1 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1005
    | (have j0 := eq1005 X1 (σ X0)
       grind)
    | exact resolve eq1005 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51366 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq51056 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq51056
    | (have j0 := eq51056 X0 X1
       grind)
    | exact resolve eq51056 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51056
  have eq51387 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq51366 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq51366
    | (have j0 := eq51366 X0 X1
       grind)
    | exact resolve eq51366 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51366
  have eq78076 : ∀ X0 : G, (σ (τ X0)) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X0)) = (k X0 (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq390 (τ X0)
       have i₂ := eq3538 (τ X0) X0
       grind)
    | exact superpose eq3538 eq390
    | (have j0 := eq390 (τ X0)
       have j1 := eq3538 (τ X0) X0
       grind)
    | exact resolve eq390 eq3538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3538
  have eq78160 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X0)) = (k X0 (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq78076 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq78076
    | (have j0 := eq78076 X0
       grind)
    | exact resolve eq78076 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78076
  have eq78187 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (σ (τ X0)) = (k X0 (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq78160 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq78160
    | (have j0 := eq78160 X0
       grind)
    | exact resolve eq78160 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78160
  have eq78200 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (σ (M.op (τ X0) (τ X0))) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq78187 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq78187
    | (have j0 := eq78187 X0
       grind)
    | exact resolve eq78187 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78187
  have eq78209 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq78200 X0
       have j1 := eq93 X0 X0
       grind)
    | (have r₁ := eq78200 x
       have r₂ := eq93 x x
       grind)
    | exact resolve eq78200 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78200
  have eq82954 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X1 X0)) ∨ (τ X0) = (k (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28477 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq28477
    | (have j0 := eq28477 X1 (τ X0)
       grind)
    | exact resolve eq28477 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28477
  have eq83282 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ (τ X0) = (k (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq82954 X0 X1
       have i₂ := eq76 X0 X1
       grind)
    | exact superpose eq76 eq82954
    | (have j0 := eq82954 X0 X1
       grind)
    | exact resolve eq82954 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82954
  have eq83330 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ (τ X0) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq83282 X0 X1
       have i₂ := eq76 X0 X1
       grind)
    | exact superpose eq76 eq83282
    | (have j0 := eq83282 X0 X1
       grind)
    | exact resolve eq83282 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83282
  have eq85275 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq390 X0
       have i₂ := eq51387 X0 X0
       grind)
    | exact superpose eq51387 eq390
    | (have j0 := eq390 X0
       have j1 := eq51387 X0 X0
       grind)
    | (have r₁ := eq390 x
       have r₂ := eq51387 x x
       grind)
    | exact resolve eq390 eq51387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85463 : ∀ X0 X1 : G, (σ X1) ≠ (σ (M.op X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq51387 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51387
  have eq85493 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq85275 X0
       have j1 := eq390 X0
       grind)
    | (have r₁ := eq85275 X0
       have r₂ := eq390 X0
       grind)
    | exact resolve eq85275 eq390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85275
  have eq119893 : ∀ X0 X1 : G, (τ X1) ≠ (τ (M.op X0 X1)) ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq83330 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83330
  have eq128813 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (k y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq11770 x y
       grind)
    | exact superpose eq11770 eq14
    | (have j1 := eq11770 x y
       grind)
    | exact resolve eq14 eq11770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11770
  have eq128823 : x = (k y y) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq36531 x y
       grind)
    | (have r₁ := eq128813
       have r₂ := eq36531 (M.op x y) (k x y)
       grind)
    | (have r₁ := eq128813
       have r₂ := eq36531 (k x y) (M.op x y)
       grind)
    | (have r₁ := eq128813
       have r₂ := eq36531 x y
       grind)
    | exact resolve eq128813 eq36531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36531 eq128813
  have eq132696 : ∀ X0 X1 : G, (σ X0) ≠ X1 ∨ (σ (k X0 X0)) = X1 ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1862 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1862
  have eq132697 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq132696 X0 X1
       have j1 := eq339 X1 X0
       grind)
    | (have r₁ := eq132696 (k X1 X1) X0
       have r₂ := eq339 X0 X1
       grind)
    | (have r₁ := eq132696 X0 (σ (k X1 X1))
       have r₂ := eq339 (σ X0) X1
       grind)
    | (have r₁ := eq132696 X1 X0
       have r₂ := eq339 X0 X1
       grind)
    | exact resolve eq132696 eq339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339 eq132696
  have eq132743 : ∀ X0 X1 : G, (k X1 (σ (τ X1))) = X0 ∨ (k X0 (σ (τ X1))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (τ X1)
       have i₂ := eq132697 (τ X1) X0
       grind)
    | (have i₁ := eq16 X0 X1
       have i₂ := eq132697 X0 (σ (k (τ X0) X1))
       grind)
    | exact superpose eq132697 eq16
    | (have j1 := eq132697 (τ X1) X0
       grind)
    | exact resolve eq16 eq132697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132744 : ∀ X0 X1 : G, (τ X0) = (k X1 X1) ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X1 X1)
       have i₂ := eq132697 X1 X0
       grind)
    | (have i₁ := eq9 X0
       have i₂ := eq132697 X0 (σ X0)
       grind)
    | exact superpose eq132697 eq9
    | (have j1 := eq132697 X1 X0
       grind)
    | exact resolve eq9 eq132697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132697
  have eq132780 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (k X0 (σ (τ X1))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq132743 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq132743
    | (have j0 := eq132743 X0 X1
       grind)
    | exact resolve eq132743 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132743
  have eq132786 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq132780 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq132780
    | (have j0 := eq132780 X0 X1
       grind)
    | exact resolve eq132780 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132780
  have eq133092 : ∀ X0 X1 : G, (σ X0) = (k X1 (σ (τ X1))) ∨ (k X0 (τ X1)) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (τ X1)
       have i₂ := eq132786 X0 (τ X1)
       grind)
    | (have i₁ := eq16 X0 X1
       have i₂ := eq132786 (k (τ X0) X1) X1
       grind)
    | exact superpose eq132786 eq16
    | (have j1 := eq132786 X0 (τ X1)
       grind)
    | exact resolve eq16 eq132786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133103 : ∀ X0 X1 : G, (σ X0) = (k X1 X1) ∨ (k X0 (τ X1)) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq133092 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq133092
    | (have j0 := eq133092 X0 X1
       grind)
    | exact resolve eq133092 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133092
  have eq133300 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (τ (σ X0)) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq132744 (σ X0) X1
       grind)
    | exact superpose eq132744 eq13
    | (have j1 := eq132744 (σ X0) X1
       grind)
    | exact resolve eq13 eq132744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132744
  have eq133316 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq133300 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq133300
    | (have j0 := eq133300 X0 X1
       grind)
    | exact resolve eq133300 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133300
  have eq133916 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (σ (τ X0)) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq76 X1 X0
       have i₂ := eq133103 (τ X0) X1
       grind)
    | exact superpose eq133103 eq76
    | (have j1 := eq133103 (τ X0) X1
       grind)
    | exact resolve eq76 eq133103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133103
  have eq133919 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq133916 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq133916
    | (have j0 := eq133916 X0 X1
       grind)
    | exact resolve eq133916 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133916
  have eq134384 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq133316 x y
       grind)
    | exact superpose eq133316 eq14
    | (have j1 := eq133316 x y
       grind)
    | exact resolve eq14 eq133316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134513 : (σ (M.op x y)) ≠ (σ y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq134384
       have i₂ := eq7512
       grind)
    | exact superpose eq7512 eq134384
    | exact resolve eq134384 eq7512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7512 eq134384
  have eq134568 : (σ y) ≠ (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq134513
       have i₂ := eq8038
       grind)
    | exact superpose eq8038 eq134513
    | (have r₁ := eq134513
       have r₂ := eq8038
       grind)
    | exact resolve eq134513 eq8038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8038
  have eq134571 : x = (k y y) ∨ x = (M.op y y) := by grind
  clear eq134568
  have eq134693 : x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq12 y y
       have i₂ := eq134571
       grind)
    | exact superpose eq134571 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq134571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134727 : x = (M.op y y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq132786 y y
       have i₂ := eq134571
       grind)
    | exact superpose eq134571 eq132786
    | exact resolve eq132786 eq134571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134571
  have eq134732 : x = (M.op y y) ∨ x = y := by grind
  clear eq134727
  have eq134748 : y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq134693
  have eq135319 : x ≠ y ∨ x = (M.op y y) := by grind
  clear eq134748
  have eq135339 : x = (M.op y y) := by
    first
    | (have r₁ := eq135319
       have r₂ := eq134732
       grind)
    | exact resolve eq135319 eq134732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134732 eq135319
  have eq135395 : y = (k (M.op y x) y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq1530 y
       have i₂ := eq135339
       grind)
    | exact superpose eq135339 eq1530
    | exact resolve eq1530 eq135339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1530
  have eq135413 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq85493 y
       have i₂ := eq135339
       grind)
    | exact superpose eq135339 eq85493
    | (have j0 := eq85493 y
       grind)
    | exact resolve eq85493 eq135339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85493
  have eq135420 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq8 X0 y y
       have i₂ := eq135339
       grind)
    | exact superpose eq135339 eq8
    | exact resolve eq8 eq135339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135422 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op x X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X0 X1 X2 y y
       have i₂ := eq135339
       grind)
    | exact superpose eq135339 eq18
    | exact resolve eq18 eq135339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq135425 : ∀ X0 : G, (k X0 x) = (M.op X0 x) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq30 X0 y y
       have i₂ := eq135339
       grind)
    | exact superpose eq135339 eq30
    | exact resolve eq30 eq135339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq135464 : ∀ X0 X1 X2 : G, (M.op x X0) ≠ X0 ∨ (k (M.op X1 X2) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq237 y y X0 X1 X2
       have i₂ := eq135339
       grind)
    | exact superpose eq135339 eq237
    | (have j0 := eq237 X0 X1 X0 X1 X2
       grind)
    | exact resolve eq237 eq135339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237
  have eq135626 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (M.op x (σ X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq135420 (σ X0)
       have i₂ := eq133316 X0 X0
       grind)
    | exact superpose eq133316 eq135420
    | (have j1 := eq133316 X0 X0
       grind)
    | exact resolve eq135420 eq133316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135659 : (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq135420 y
       have i₂ := eq135339
       grind)
    | exact superpose eq135339 eq135420
    | exact resolve eq135420 eq135339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136112 : x ≠ (M.op x y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq93 y x
       have i₂ := eq135659
       grind)
    | exact superpose eq135659 eq93
    | (have j0 := eq93 y x
       grind)
    | exact resolve eq93 eq135659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136200 : (τ x) ≠ (τ (M.op x y)) ∨ (τ x) = (τ (k y x)) := by
    first
    | (have i₁ := eq119893 y x
       have i₂ := eq135659
       grind)
    | exact superpose eq135659 eq119893
    | (have j0 := eq119893 y x
       grind)
    | exact resolve eq119893 eq135659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119893
  have eq136399 : ∀ X0 X1 X2 : G, (M.op (σ (k X0 X1)) X2) = (M.op x X2) ∨ (k X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq135422 (σ X0) (σ X1) X2
       have i₂ := eq394 X0 X1
       grind)
    | exact superpose eq394 eq135422
    | (have j1 := eq394 X0 X1
       grind)
    | exact resolve eq135422 eq394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136406 : ∀ X0 X1 X2 : G, (M.op (σ (k X0 X1)) X2) = (M.op x X2) ∨ (k X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq135422 (σ X0) (σ X1) X2
       have i₂ := eq133316 X0 X1
       grind)
    | exact superpose eq133316 eq135422
    | (have j1 := eq133316 X0 X1
       grind)
    | exact resolve eq135422 eq133316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133316
  have eq136454 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (M.op x X1) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq135422 (τ X0) (τ X0) X1
       have i₂ := eq6411 X0
       grind)
    | exact superpose eq6411 eq135422
    | (have j1 := eq6411 X0
       grind)
    | exact resolve eq135422 eq6411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139930 : (σ y) = (σ (M.op (M.op y x) y)) ∨ (σ (M.op y y)) = (σ (M.op y x)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq32894 (M.op y x) y
       have i₂ := eq135395
       grind)
    | exact superpose eq135395 eq32894
    | (have j0 := eq32894 (M.op y x) y
       grind)
    | exact resolve eq32894 eq135395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32894 eq135395
  have eq139941 : (σ y) = (σ (M.op y (M.op y y))) ∨ (σ (M.op y y)) = (σ (M.op y x)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq139930
       have i₂ := eq8 y y x
       grind)
    | exact superpose eq8 eq139930
    | exact resolve eq139930 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139930
  have eq139969 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op y y)) = (σ (M.op y x)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq139941
       have i₂ := eq135420 y
       grind)
    | exact superpose eq135420 eq139941
    | exact resolve eq139941 eq135420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139941
  have eq139996 : (σ (M.op y y)) = (σ (M.op y x)) ∨ x = (k y y) := by
    first
    | (have r₁ := eq139969
       have r₂ := eq134513
       grind)
    | exact resolve eq139969 eq134513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139969
  have eq140017 : (σ (M.op x y)) = (σ (M.op y y)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq139996
       have i₂ := eq135659
       grind)
    | exact superpose eq135659 eq139996
    | exact resolve eq139996 eq135659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139996
  have eq140027 : (σ (M.op x y)) = (σ x) ∨ x = (k y y) := by
    first
    | (have i₁ := eq140017
       have i₂ := eq135339
       grind)
    | exact superpose eq135339 eq140017
    | exact resolve eq140017 eq135339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140017
  have eq142217 : ∀ X0 X1 : G, (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (k (M.op X0 X1) (M.op x x)) := by
    intro X0 X1
    first
    | (have i₁ := eq135464 (M.op x x) X0 X1
       have i₂ := eq135420 x
       grind)
    | exact superpose eq135420 eq135464
    | (have j0 := eq135464 (M.op x x) X0 X1
       grind)
    | (have r₁ := eq135464 (M.op x x) X1 x
       have r₂ := eq135420 x
       grind)
    | exact resolve eq135464 eq135420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135464
  have eq142218 : ∀ X0 X1 : G, (M.op x x) = (k (M.op X0 X1) (M.op x x)) := by
    intro X0 X1
    first
    | (have j0 := eq142217 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142217
  have eq142593 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by
    first
    | (have i₁ := eq390 (M.op x x)
       have i₂ := eq142218 x x
       grind)
    | exact superpose eq142218 eq390
    | (have j0 := eq390 (M.op x x)
       grind)
    | exact resolve eq390 eq142218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390
  have eq142595 : (τ (M.op x x)) ≠ (τ (M.op x x)) ∨ (τ (M.op x x)) = (M.op (τ (M.op x x)) (τ (M.op x x))) := by
    first
    | (have i₁ := eq812 (M.op x x)
       have i₂ := eq142218 x x
       grind)
    | exact superpose eq142218 eq812
    | (have j0 := eq812 (M.op x x)
       grind)
    | exact resolve eq812 eq142218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq812 eq142218
  have eq142651 : (τ (M.op x x)) = (M.op (τ (M.op x x)) (τ (M.op x x))) := by grind
  clear eq142595
  have eq142653 : (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by grind
  clear eq142593
  have eq144481 : (σ x) ≠ (σ y) ∨ x = (k y y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq134513
       have i₂ := eq140027
       grind)
    | exact superpose eq140027 eq134513
    | exact resolve eq134513 eq140027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134513 eq140027
  have eq144531 : (σ x) ≠ (σ y) ∨ x = (k y y) := by grind
  clear eq144481
  have eq144552 : x = (k y y) := by
    first
    | (have r₁ := eq144531
       have r₂ := eq128823
       grind)
    | exact resolve eq144531 eq128823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128823 eq144531
  have eq144684 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq132786 X0 y
       have i₂ := eq144552
       grind)
    | exact superpose eq144552 eq132786
    | (have j0 := eq132786 X0 y
       grind)
    | exact resolve eq132786 eq144552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132786
  have eq144915 : ∀ X0 : G, (k X0 (τ y)) = (τ (M.op (σ X0) y)) ∨ (σ X0) = x := by
    intro X0
    first
    | (have i₁ := eq40 X0 y
       have i₂ := eq144684 (σ X0)
       grind)
    | exact superpose eq144684 eq40
    | (have j1 := eq144684 (σ X0)
       grind)
    | exact resolve eq40 eq144684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq144924 : ∀ X0 : G, (k X0 (σ y)) = (σ (M.op (τ X0) y)) ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq16 X0 y
       have i₂ := eq144684 (τ X0)
       grind)
    | exact superpose eq144684 eq16
    | (have j1 := eq144684 (τ X0)
       grind)
    | exact resolve eq16 eq144684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144684
  have eq145731 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ (σ (k X1 (τ X0))) ∨ (σ (k X1 (τ X0))) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq5350 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5350
    | exact resolve eq5350 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5350
  have eq145738 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ (k (σ X1) X0) ∨ (σ (k X1 (τ X0))) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq145731 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq145731
    | (have j0 := eq145731 X0 X1
       grind)
    | exact resolve eq145731 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145731
  have eq145743 : ∀ X0 X1 : G, (k (σ X1) X0) ≠ (M.op x X0) ∨ (σ (k X1 (τ X0))) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq145738 X0 X1
       have i₂ := eq135420 X0
       grind)
    | exact superpose eq135420 eq145738
    | (have j0 := eq145738 X0 X1
       grind)
    | exact resolve eq145738 eq135420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135420 eq145738
  have eq145747 : ∀ X0 X1 : G, (k (σ X1) X0) ≠ (M.op x X0) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq145743 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq145743
    | (have j0 := eq145743 X0 X1
       grind)
    | exact resolve eq145743 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145743
  have eq156830 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (σ X0) x) = (k (σ X0) x) := by
    intro X0
    first
    | (have i₁ := eq142651
       have i₂ := eq2393 x x
       grind)
    | (have i₁ := eq142651
       have i₂ := eq2393 X0 (τ (M.op x x))
       grind)
    | exact superpose eq2393 eq142651
    | (have j1 := eq2393 x X0
       grind)
    | exact resolve eq142651 eq2393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2393
  have eq156989 : ∀ X0 : G, (M.op x X0) = (M.op (τ (M.op x x)) X0) := by
    intro X0
    first
    | (have i₁ := eq135422 (τ (M.op x x)) (τ (M.op x x)) X0
       have i₂ := eq142651
       grind)
    | exact superpose eq142651 eq135422
    | exact resolve eq135422 eq142651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq157148 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (M.op x X1) ∨ (k X0 x) = (M.op X0 x) := by
    intro X0 X1
    first
    | (have i₁ := eq156989 X1
       have i₂ := eq5020 X0 x
       grind)
    | (have i₁ := eq156989 X0
       have i₂ := eq5020 (M.op x x) X1
       grind)
    | exact superpose eq5020 eq156989
    | (have j1 := eq5020 X0 x
       grind)
    | exact resolve eq156989 eq5020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq157184 : (τ (M.op x x)) = (M.op x (τ (M.op x x))) := by
    first
    | (have i₁ := eq142651
       have i₂ := eq156989 (τ (M.op x x))
       grind)
    | exact superpose eq156989 eq142651
    | exact resolve eq142651 eq156989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142651 eq156989
  have eq157452 : ∀ X0 : G, (τ X0) = (M.op x (τ X0)) ∨ (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq157184
       have i₂ := eq5020 (M.op x x) x
       grind)
    | (have i₁ := eq157184
       have i₂ := eq5020 X0 x
       grind)
    | exact superpose eq5020 eq157184
    | (have j1 := eq5020 X0 x
       grind)
    | exact resolve eq157184 eq5020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5020 eq157184
  have eq158807 : ∀ X0 : G, (M.op x X0) = (M.op (σ (M.op x x)) X0) := by
    intro X0
    first
    | (have i₁ := eq135422 (σ (M.op x x)) (σ (M.op x x)) X0
       have i₂ := eq142653
       grind)
    | exact superpose eq142653 eq135422
    | exact resolve eq135422 eq142653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq159047 : (σ (M.op x x)) = (M.op x (σ (M.op x x))) := by
    first
    | (have i₁ := eq142653
       have i₂ := eq158807 (σ (M.op x x))
       grind)
    | exact superpose eq158807 eq142653
    | exact resolve eq142653 eq158807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142653 eq158807
  have eq159338 : ∀ X0 : G, (σ X0) = (M.op x (σ X0)) ∨ (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq159047
       have i₂ := eq37616 (M.op x x) x
       grind)
    | (have i₁ := eq159047
       have i₂ := eq37616 X0 x
       grind)
    | exact superpose eq37616 eq159047
    | (have j1 := eq37616 X0 x
       grind)
    | exact resolve eq159047 eq37616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37616 eq159047
  have eq161342 : ∀ X0 : G, (σ (τ X0)) = (k X0 X0) ∨ (k X0 X0) = X0 ∨ (k (σ (τ X0)) x) = (M.op (σ (τ X0)) x) := by
    intro X0
    first
    | (have i₁ := eq920 X0 X0
       have i₂ := eq156830 (τ X0)
       grind)
    | exact superpose eq156830 eq920
    | (have j0 := eq920 X0 X0
       have j1 := eq156830 (τ X0)
       grind)
    | exact resolve eq920 eq156830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq920
  have eq161343 : ∀ X0 : G, (k (σ (σ (τ (τ X0)))) X0) = X0 ∨ (M.op (σ (τ (τ X0))) x) = (k (σ (τ (τ X0))) x) := by
    intro X0
    first
    | (have i₁ := eq176 X0
       have i₂ := eq156830 (τ (τ X0))
       grind)
    | exact superpose eq156830 eq176
    | (have j1 := eq156830 (τ (τ X0))
       grind)
    | exact resolve eq176 eq156830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq161346 : ∀ X0 : G, (k X0 (τ x)) = (τ (M.op (σ X0) x)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq40 X0 x
       have i₂ := eq156830 X0
       grind)
    | exact superpose eq156830 eq40
    | (have j1 := eq156830 X0
       grind)
    | exact resolve eq40 eq156830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156830
  have eq161369 : ∀ X0 : G, (k (σ (τ X0)) X0) = X0 ∨ (M.op (σ (τ (τ X0))) x) = (k (σ (τ (τ X0))) x) := by
    intro X0
    first
    | (have i₁ := eq161343 X0
       have i₂ := eq10 (τ X0)
       grind)
    | exact superpose eq10 eq161343
    | (have j0 := eq161343 X0
       grind)
    | exact resolve eq161343 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161343
  have eq161370 : ∀ X0 : G, (k X0 X0) = X0 ∨ (k X0 X0) = X0 ∨ (k (σ (τ X0)) x) = (M.op (σ (τ X0)) x) := by
    intro X0
    first
    | (have i₁ := eq161342 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq161342
    | (have j0 := eq161342 X0
       grind)
    | exact resolve eq161342 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161342
  have eq161371 : ∀ X0 : G, (k X0 X0) = X0 ∨ (k (σ (τ X0)) x) = (M.op (σ (τ X0)) x) := by
    intro X0
    first
    | (have j0 := eq161370 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161370
  have eq161399 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op (σ (τ (τ X0))) x) = (k (σ (τ (τ X0))) x) := by
    intro X0
    first
    | (have i₁ := eq161369 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq161369
    | (have j0 := eq161369 X0
       grind)
    | exact resolve eq161369 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161369
  have eq161400 : ∀ X0 : G, (k X0 x) = (M.op X0 x) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq161371 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq161371
    | (have j0 := eq161371 X0
       grind)
    | exact resolve eq161371 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161371
  have eq161408 : ∀ X0 : G, (M.op (τ X0) x) = (k (τ X0) x) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq161399 X0
       have i₂ := eq10 (τ X0)
       grind)
    | exact superpose eq10 eq161399
    | (have j0 := eq161399 X0
       grind)
    | exact resolve eq161399 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161399
  have eq161554 : ∀ X0 : G, X0 ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 ∨ (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq32850 X0
       have i₂ := eq161400 X0
       grind)
    | exact superpose eq161400 eq32850
    | (have j0 := eq32850 X0
       have j1 := eq161400 X0
       grind)
    | (have r₁ := eq32850 X0
       have r₂ := eq161400 X0
       grind)
    | exact resolve eq32850 eq161400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32850
  have eq161605 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq161400 X0
       grind)
    | exact superpose eq161400 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq161400 X0
       grind)
    | exact resolve eq12 eq161400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq161663 : x = y ∨ (k y x) = (M.op y x) := by
    first
    | (have i₁ := eq144552
       have i₂ := eq161400 y
       grind)
    | exact superpose eq161400 eq144552
    | (have j1 := eq161400 y
       grind)
    | exact resolve eq144552 eq161400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161400
  have eq161673 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq161605 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161605
  have eq161677 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = X0 ∨ (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq161554 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161554
  have eq161691 : (M.op x y) = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq161663
       have i₂ := eq135659
       grind)
    | exact superpose eq135659 eq161663
    | exact resolve eq161663 eq135659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161663
  have eq162057 : ∀ X0 : G, (k (σ (σ (τ (τ X0)))) X0) = X0 ∨ (k (τ (τ X0)) x) = (M.op (τ (τ X0)) x) := by
    intro X0
    first
    | (have i₁ := eq176 X0
       have i₂ := eq161673 (τ (τ X0))
       grind)
    | exact superpose eq161673 eq176
    | (have j1 := eq161673 (τ (τ X0))
       grind)
    | exact resolve eq176 eq161673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq161673
  have eq162161 : ∀ X0 : G, (k (σ (τ X0)) X0) = X0 ∨ (k (τ (τ X0)) x) = (M.op (τ (τ X0)) x) := by
    intro X0
    first
    | (have i₁ := eq162057 X0
       have i₂ := eq10 (τ X0)
       grind)
    | exact superpose eq10 eq162057
    | (have j0 := eq162057 X0
       grind)
    | exact resolve eq162057 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162057
  have eq162179 : ∀ X0 : G, (k X0 X0) = X0 ∨ (k (τ (τ X0)) x) = (M.op (τ (τ X0)) x) := by
    intro X0
    first
    | (have i₁ := eq162161 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq162161
    | (have j0 := eq162161 X0
       grind)
    | exact resolve eq162161 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162161
  have eq162591 : ∀ X0 : G, (τ (M.op X0 y)) = (k (τ X0) (τ y)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq144915 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq144915
    | exact resolve eq144915 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144915
  have eq162618 : ∀ X0 : G, (τ (k X0 y)) = (τ (M.op X0 y)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq162591 X0
       have i₂ := eq76 y X0
       grind)
    | exact superpose eq76 eq162591
    | (have j0 := eq162591 X0
       grind)
    | exact resolve eq162591 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162591
  have eq162774 : ∀ X0 : G, (σ (M.op X0 y)) = (k (σ X0) (σ y)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq144924 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq144924
    | exact resolve eq144924 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq162804 : ∀ X0 : G, (σ (k X0 y)) = (σ (M.op X0 y)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq162774 X0
       have i₂ := eq13 X0 y
       grind)
    | exact superpose eq13 eq162774
    | (have j0 := eq162774 X0
       grind)
    | exact resolve eq162774 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162774
  have eq163255 : ∀ X0 : G, (k X0 (σ x)) = (σ (M.op (τ X0) x)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 x
       have i₂ := eq161408 X0
       grind)
    | exact superpose eq161408 eq16
    | (have j1 := eq161408 X0
       grind)
    | exact resolve eq16 eq161408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161408
  have eq163400 : ∀ X0 : G, (σ (τ X0)) = (k (σ x) X0) ∨ (k (σ x) X0) = X0 ∨ (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq1005 x X0
       have i₂ := eq157452 X0
       grind)
    | exact superpose eq157452 eq1005
    | (have j0 := eq1005 x X0
       have j1 := eq157452 X0
       grind)
    | exact resolve eq1005 eq157452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1005 eq157452
  have eq163485 : ∀ X0 : G, (k (σ x) X0) = X0 ∨ (k (σ x) X0) = X0 ∨ (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq163400 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq163400
    | (have j0 := eq163400 X0
       grind)
    | exact resolve eq163400 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163400
  have eq163486 : ∀ X0 : G, (k (σ x) X0) = X0 ∨ (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq163485 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163485
  have eq163563 : ∀ X0 : G, (σ (τ X0)) = (k (σ (σ x)) X0) ∨ (M.op (τ X0) x) = (k (τ X0) x) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (σ x)
       have i₂ := eq163486 (τ X0)
       grind)
    | exact superpose eq163486 eq17
    | (have j1 := eq163486 (τ X0)
       grind)
    | exact resolve eq17 eq163486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq163586 : ∀ X0 : G, (k (σ (σ x)) X0) = X0 ∨ (M.op (τ X0) x) = (k (τ X0) x) := by
    intro X0
    first
    | (have i₁ := eq163563 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq163563
    | (have j0 := eq163563 X0
       grind)
    | exact resolve eq163563 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163563
  have eq163669 : ∀ X0 : G, (M.op (τ X0) x) = (k (τ X0) x) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq159338 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq159338
    | (have j0 := eq159338 (τ X0)
       grind)
    | exact resolve eq159338 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159338
  have eq165548 : ∀ X0 X1 X2 : G, (M.op x X2) = (M.op (τ (k X0 X1)) X2) ∨ (k X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq135422 (τ X0) (τ X1) X2
       have i₂ := eq133919 X0 X1
       grind)
    | exact superpose eq133919 eq135422
    | (have j1 := eq133919 X0 X1
       grind)
    | exact resolve eq135422 eq133919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133919
  have eq168062 : ∀ X0 : G, (M.op (σ x) X0) = (M.op x X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq136399 y y x
       have i₂ := eq144552
       grind)
    | exact superpose eq144552 eq136399
    | exact resolve eq136399 eq144552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136399
  have eq168251 : (σ (M.op x y)) ≠ (M.op x (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq168062 (σ y)
       grind)
    | exact superpose eq168062 eq14
    | exact resolve eq14 eq168062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168062
  have eq169063 : ∀ X0 X1 X2 : G, (τ X0) = (k X1 (τ (σ X1))) ∨ (M.op (σ (k X0 (σ X1))) X2) = (M.op x X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq40 X1 (σ X1)
       have i₂ := eq136406 X0 (σ X1) X2
       grind)
    | (have i₁ := eq40 X0 X1
       have i₂ := eq136406 (k (σ X0) X1) X1 X2
       grind)
    | exact superpose eq136406 eq40
    | (have j1 := eq136406 X0 (σ X1) X2
       grind)
    | exact resolve eq40 eq136406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136406
  have eq169077 : ∀ X0 X1 X2 : G, (τ X0) = (k X1 X1) ∨ (M.op (σ (k X0 (σ X1))) X2) = (M.op x X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq169063 X0 X1 X2
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq169063
    | (have j0 := eq169063 X0 X1 X2
       grind)
    | exact resolve eq169063 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169063
  have eq171862 : ∀ X0 : G, (τ X0) = (M.op x (τ X0)) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq6411 X0
       have i₂ := eq136454 X0 (τ X0)
       grind)
    | exact superpose eq136454 eq6411
    | (have j0 := eq6411 X0
       have j1 := eq136454 X0 x
       grind)
    | exact resolve eq6411 eq136454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6411 eq136454
  have eq172023 : ∀ X0 : G, (τ X0) = (M.op x (τ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq171862 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171862
  have eq172683 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (τ (σ X0)) = (M.op x (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq172023 (σ X0)
       grind)
    | exact superpose eq172023 eq13
    | (have j1 := eq172023 (σ X0)
       grind)
    | exact resolve eq13 eq172023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172023
  have eq172699 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq172683 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq172683
    | (have j0 := eq172683 X0
       grind)
    | exact resolve eq172683 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172683
  have eq174884 : ∀ X0 X1 : G, (M.op x X1) = (M.op (τ (M.op X0 y)) X1) ∨ (k y y) = X0 ∨ x = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq165548 X0 y X1
       have i₂ := eq162618 X0
       grind)
    | exact superpose eq162618 eq165548
    | (have j0 := eq165548 X0 y x
       have j1 := eq162618 X0
       grind)
    | exact resolve eq165548 eq162618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162618 eq165548
  have eq175140 : ∀ X0 X1 : G, x = X0 ∨ (M.op x X1) = (M.op (τ (M.op X0 y)) X1) ∨ x = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq174884 X0 X1
       have i₂ := eq144552
       grind)
    | exact superpose eq144552 eq174884
    | (have j0 := eq174884 X0 X1
       grind)
    | exact resolve eq174884 eq144552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174884
  have eq175141 : ∀ X0 X1 : G, (M.op x X1) = (M.op (τ (M.op X0 y)) X1) ∨ x = X0 := by
    intro X0 X1
    first
    | (have j0 := eq175140 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175140
  have eq175218 : ∀ X0 X1 X2 : G, (M.op x X0) = (M.op (τ (M.op x y)) X0) ∨ (M.op X1 X2) = x := by
    intro X0 X1 X2
    first
    | (have i₁ := eq175141 (M.op X1 X2) X0
       have i₂ := eq135422 X1 X2 y
       grind)
    | exact superpose eq135422 eq175141
    | (have j0 := eq175141 x X0
       grind)
    | exact resolve eq175141 eq135422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175141
  have eq178455 : ∀ X0 X1 : G, (M.op (σ (k X0 X0)) X1) = (M.op x X1) ∨ (M.op x X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq135422 (σ X0) (σ X0) X1
       have i₂ := eq172699 X0
       grind)
    | exact superpose eq172699 eq135422
    | (have j1 := eq172699 X0
       grind)
    | exact resolve eq135422 eq172699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172699
  have eq179543 : ∀ X0 : G, (σ (τ X0)) ≠ X0 ∨ (k X0 X0) = X0 ∨ (k (τ X0) (τ x)) = (τ (M.op (σ (τ X0)) x)) := by
    intro X0
    first
    | (have i₁ := eq78209 X0
       have i₂ := eq161346 (τ X0)
       grind)
    | exact superpose eq161346 eq78209
    | (have j0 := eq78209 X0
       have j1 := eq161346 (τ X0)
       grind)
    | exact resolve eq78209 eq161346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78209 eq161346
  have eq179552 : ∀ X0 : G, (k X0 X0) = X0 ∨ (k (τ X0) (τ x)) = (τ (M.op (σ (τ X0)) x)) := by
    intro X0
    first
    | (have j0 := eq179543 X0
       grind)
    | (have r₁ := eq179543 X0
       have r₂ := eq10 X0
       grind)
    | exact resolve eq179543 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179543
  have eq179569 : ∀ X0 : G, (τ (M.op X0 x)) = (k (τ X0) (τ x)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq179552 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq179552
    | (have j0 := eq179552 X0
       grind)
    | exact resolve eq179552 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179552
  have eq179571 : ∀ X0 : G, (τ (k X0 x)) = (τ (M.op X0 x)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq179569 X0
       have i₂ := eq76 x X0
       grind)
    | exact superpose eq76 eq179569
    | (have j0 := eq179569 X0
       grind)
    | exact resolve eq179569 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq179569
  have eq179726 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (τ (k X0 x)) = (τ (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq179571 X0
       grind)
    | exact superpose eq179571 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq179571 X0
       grind)
    | exact resolve eq12 eq179571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179571
  have eq179740 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ (k X0 x)) = (τ (M.op X0 x)) := by
    intro X0
    first
    | (have j0 := eq179726 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179726
  have eq181692 : ∀ X0 : G, (M.op (σ x) X0) = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq178455 y X0
       have i₂ := eq144552
       grind)
    | exact superpose eq144552 eq178455
    | (have j0 := eq178455 y x
       grind)
    | exact resolve eq178455 eq144552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178455
  have eq181838 : (σ (M.op x y)) ≠ (M.op x (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq181692 (σ y)
       grind)
    | exact superpose eq181692 eq14
    | exact resolve eq14 eq181692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181692
  have eq182163 : ∀ X0 : G, (σ (M.op x (τ X0))) = X0 ∨ (k X0 x) = (M.op X0 x) ∨ (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq161677 X0
       have i₂ := eq157148 X0 (τ X0)
       grind)
    | exact superpose eq157148 eq161677
    | (have j0 := eq161677 X0
       have j1 := eq157148 X0 x
       grind)
    | exact resolve eq161677 eq157148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157148 eq161677
  have eq182237 : ∀ X0 : G, (σ (M.op x (τ X0))) = X0 ∨ (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq182163 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182163
  have eq182264 : ∀ X0 : G, (M.op (σ X0) x) = (k (σ X0) x) ∨ (σ X0) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq182237 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq182237
    | (have j0 := eq182237 (σ X0)
       grind)
    | exact resolve eq182237 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182237
  have eq182538 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ X0))) ∨ (k (σ X0) (σ x)) = (σ (M.op (τ (σ X0)) x)) := by
    intro X0
    first
    | (have i₁ := eq40 X0 (σ X0)
       have i₂ := eq163255 (σ X0)
       grind)
    | exact superpose eq163255 eq40
    | (have j1 := eq163255 (σ X0)
       grind)
    | exact resolve eq40 eq163255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq163255
  have eq182549 : ∀ X0 : G, (k X0 X0) = X0 ∨ (k (σ X0) (σ x)) = (σ (M.op (τ (σ X0)) x)) := by
    intro X0
    first
    | (have i₁ := eq182538 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq182538
    | (have j0 := eq182538 X0
       grind)
    | exact resolve eq182538 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182538
  have eq182564 : ∀ X0 : G, (σ (M.op X0 x)) = (k (σ X0) (σ x)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq182549 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq182549
    | (have j0 := eq182549 X0
       grind)
    | exact resolve eq182549 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182549
  have eq182569 : ∀ X0 : G, (σ (M.op X0 x)) = (σ (k X0 x)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq182564 X0
       have i₂ := eq13 X0 x
       grind)
    | exact superpose eq13 eq182564
    | (have j0 := eq182564 X0
       grind)
    | exact resolve eq182564 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182564
  have eq182722 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (σ (M.op X0 x)) = (σ (k X0 x)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq182569 X0
       grind)
    | exact superpose eq182569 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq182569 X0
       grind)
    | exact resolve eq12 eq182569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182569
  have eq182736 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ (M.op X0 x)) = (σ (k X0 x)) := by
    intro X0
    first
    | (have j0 := eq182722 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182722
  have eq186277 : ∀ X0 : G, x ≠ (M.op x X0) ∨ x = (M.op (τ (M.op x y)) X0) := by
    intro X0
    first
    | (have j0 := eq175218 X0 (τ (M.op x y)) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175218
  have eq214113 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (k (τ (τ X0)) x) = (M.op (τ (τ X0)) x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq162179 X0
       grind)
    | exact superpose eq162179 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq162179 X0
       grind)
    | exact resolve eq12 eq162179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162179
  have eq214117 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (τ (τ X0)) x) = (M.op (τ (τ X0)) x) := by
    intro X0
    first
    | (have j0 := eq214113 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214113
  have eq223699 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op x X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq145747 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq145747
    | exact resolve eq145747 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq223711 : ∀ X0 : G, (M.op x X0) ≠ X0 ∨ (M.op (σ x) X0) = X0 ∨ (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq145747 X0 x
       have i₂ := eq163486 X0
       grind)
    | exact superpose eq163486 eq145747
    | (have j1 := eq163486 X0
       grind)
    | exact resolve eq145747 eq163486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145747 eq163486
  have eq223736 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq223711 X0
       have j1 := eq135425 X0
       grind)
    | (have r₁ := eq223711 X0
       have r₂ := eq135425 X0
       grind)
    | exact resolve eq223711 eq135425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135425 eq223711
  have eq224839 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ y) x) = (k (σ y) x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq223736 (σ y)
       grind)
    | exact superpose eq223736 eq14
    | (have j1 := eq223736 (σ y)
       grind)
    | exact resolve eq14 eq223736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223736
  have eq224995 : (M.op (σ y) x) = (k (σ y) x) := by
    first
    | (have j1 := eq182264 y
       grind)
    | (have r₁ := eq224839
       have r₂ := eq182264 y
       grind)
    | exact resolve eq224839 eq182264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182264 eq224839
  have eq225376 : ∀ X0 : G, (M.op x X0) ≠ X0 ∨ (M.op (σ (σ x)) X0) = X0 ∨ (M.op (τ X0) x) = (k (τ X0) x) := by
    intro X0
    first
    | (have i₁ := eq223699 (σ (σ x)) X0
       have i₂ := eq163586 X0
       grind)
    | exact superpose eq163586 eq223699
    | (have j0 := eq223699 (τ X0) x
       have j1 := eq163586 X0
       grind)
    | exact resolve eq223699 eq163586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163586 eq223699
  have eq225570 : ∀ X0 : G, (M.op (σ (σ x)) X0) = X0 ∨ (M.op (τ X0) x) = (k (τ X0) x) := by
    intro X0
    first
    | (have j0 := eq225376 X0
       have j1 := eq163669 X0
       grind)
    | (have r₁ := eq225376 X0
       have r₂ := eq163669 X0
       grind)
    | exact resolve eq225376 eq163669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163669 eq225376
  have eq246612 : (M.op (σ y) (σ x)) = (M.op x (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq135626 y
       have i₂ := eq144552
       grind)
    | exact superpose eq144552 eq135626
    | exact resolve eq135626 eq144552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135626
  have eq246666 : (σ (k y x)) = (M.op x (σ y)) ∨ x = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq394 y x
       have i₂ := eq246612
       grind)
    | exact superpose eq246612 eq394
    | (have j0 := eq394 y x
       grind)
    | exact resolve eq394 eq246612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394
  have eq250197 : ∀ X0 X1 X2 : G, (k X0 X0) = X1 ∨ (M.op x X2) = (M.op (σ (k (σ X1) (σ X0))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1
       have i₂ := eq169077 (σ X1) X0 X2
       grind)
    | exact superpose eq169077 eq9
    | (have j1 := eq169077 (σ X1) X0 X2
       grind)
    | exact resolve eq9 eq169077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169077
  have eq250233 : ∀ X0 X1 X2 : G, (M.op x X2) = (M.op (σ (σ (k X1 X0))) X2) ∨ (k X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq250197 X0 X1 X2
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq250197
    | (have j0 := eq250197 X0 X1 X2
       grind)
    | exact resolve eq250197 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250197
  have eq250258 : ∀ X0 X1 : G, (M.op x X1) = (M.op (σ (σ (M.op X0 y))) X1) ∨ (k y y) = X0 ∨ x = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq250233 y X0 X1
       have i₂ := eq162804 X0
       grind)
    | exact superpose eq162804 eq250233
    | (have j0 := eq250233 y X0 x
       have j1 := eq162804 X0
       grind)
    | exact resolve eq250233 eq162804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162804 eq250233
  have eq250330 : ∀ X0 X1 : G, x = X0 ∨ (M.op x X1) = (M.op (σ (σ (M.op X0 y))) X1) ∨ x = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq250258 X0 X1
       have i₂ := eq144552
       grind)
    | exact superpose eq144552 eq250258
    | (have j0 := eq250258 X0 X1
       grind)
    | exact resolve eq250258 eq144552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144552 eq250258
  have eq250331 : ∀ X0 X1 : G, (M.op x X1) = (M.op (σ (σ (M.op X0 y))) X1) ∨ x = X0 := by
    intro X0 X1
    first
    | (have j0 := eq250330 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250330
  have eq250350 : ∀ X0 X1 X2 : G, (M.op x X0) = (M.op (σ (σ (M.op x y))) X0) ∨ (M.op X1 X2) = x := by
    intro X0 X1 X2
    first
    | (have i₁ := eq250331 (M.op X1 X2) X0
       have i₂ := eq135422 X1 X2 y
       grind)
    | exact superpose eq135422 eq250331
    | (have j0 := eq250331 x X0
       grind)
    | exact resolve eq250331 eq135422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135422 eq250331
  have eq251216 : ∀ X0 : G, x ≠ (M.op x X0) ∨ x = (M.op (σ (σ (M.op x y))) X0) := by
    intro X0
    first
    | (have j0 := eq250350 X0 (σ (σ (M.op x y))) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250350
  have eq261067 : (σ (M.op x y)) = (M.op x (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq246666
       have i₂ := eq161691
       grind)
    | exact superpose eq161691 eq246666
    | exact resolve eq246666 eq161691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246666
  have eq261069 : (σ (M.op x y)) = (M.op x (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq261067
  have eq261070 : x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq261069
       have r₂ := eq168251
       grind)
    | exact resolve eq261069 eq168251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261069
  have eq261106 : x ≠ x ∨ x = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq136112
       have i₂ := eq261070
       grind)
    | exact superpose eq261070 eq136112
    | (have r₁ := eq136112
       have r₂ := eq261070
       grind)
    | exact resolve eq136112 eq261070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136112
  have eq261108 : (τ x) ≠ (τ x) ∨ (τ x) = (τ (k y x)) ∨ x = y := by
    first
    | (have i₁ := eq136200
       have i₂ := eq261070
       grind)
    | exact superpose eq261070 eq136200
    | exact resolve eq136200 eq261070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136200
  have eq261135 : (σ x) ≠ (M.op x (σ y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq181838
       have i₂ := eq261070
       grind)
    | exact superpose eq261070 eq181838
    | exact resolve eq181838 eq261070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181838
  have eq261233 : x ≠ x ∨ x = (M.op (τ x) y) ∨ x = y := by
    first
    | (have i₁ := eq186277 y
       have i₂ := eq261070
       grind)
    | exact superpose eq261070 eq186277
    | (have r₁ := eq186277 y
       have r₂ := eq261070
       grind)
    | exact resolve eq186277 eq261070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186277
  have eq261253 : x ≠ x ∨ x = (M.op (σ (σ x)) y) ∨ x = y := by
    first
    | (have i₁ := eq251216 y
       have i₂ := eq261070
       grind)
    | exact superpose eq261070 eq251216
    | (have r₁ := eq251216 y
       have r₂ := eq261070
       grind)
    | exact resolve eq251216 eq261070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251216 eq261070
  have eq261440 : x = (M.op (σ (σ x)) y) ∨ x = y := by grind
  clear eq261253
  have eq261443 : x = (M.op (τ x) y) ∨ x = y := by grind
  clear eq261233
  have eq261456 : (σ x) ≠ (M.op x (σ y)) ∨ x = y := by grind
  clear eq261135
  have eq261461 : (τ x) = (τ (k y x)) ∨ x = y := by grind
  clear eq261108
  have eq261463 : x = (k y x) ∨ x = y := by grind
  clear eq261106
  have eq261621 : (τ x) = (τ (M.op y x)) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq179740 y
       have i₂ := eq261463
       grind)
    | exact superpose eq261463 eq179740
    | (have j0 := eq179740 y
       grind)
    | exact resolve eq179740 eq261463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179740
  have eq261626 : (σ x) = (σ (M.op y x)) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq182736 y
       have i₂ := eq261463
       grind)
    | exact superpose eq261463 eq182736
    | (have j0 := eq182736 y
       grind)
    | exact resolve eq182736 eq261463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182736 eq261463
  have eq261768 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq261626
       have i₂ := eq135659
       grind)
    | exact superpose eq135659 eq261626
    | exact resolve eq261626 eq135659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261626
  have eq261773 : (τ x) = (τ (M.op x y)) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq261621
       have i₂ := eq135659
       grind)
    | exact superpose eq135659 eq261621
    | exact resolve eq261621 eq135659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135659 eq261621
  have eq261828 : x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq261768
       have i₂ := eq135339
       grind)
    | exact superpose eq135339 eq261768
    | exact resolve eq261768 eq135339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261768
  have eq261829 : (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq261828
  have eq261834 : x = y ∨ (τ x) = (τ (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq261773
       have i₂ := eq135339
       grind)
    | exact superpose eq135339 eq261773
    | exact resolve eq261773 eq135339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261773
  have eq261835 : (τ x) = (τ (M.op x y)) ∨ x = y := by grind
  clear eq261834
  have eq261863 : (σ x) = (k x (σ y)) ∨ x = (τ x) ∨ x = y := by
    first
    | (have i₁ := eq144924 x
       have i₂ := eq261443
       grind)
    | exact superpose eq261443 eq144924
    | (have j0 := eq144924 x
       grind)
    | exact resolve eq144924 eq261443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144924 eq261443
  have eq263010 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ x)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq13 X0 (M.op x y)
       have i₂ := eq261829
       grind)
    | exact superpose eq261829 eq13
    | exact resolve eq13 eq261829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261829
  have eq263071 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (σ (k X0 x)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq263010 X0
       have i₂ := eq13 X0 x
       grind)
    | exact superpose eq13 eq263010
    | exact resolve eq263010 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263010
  have eq263463 : x = y ∨ (k (τ y) x) = (M.op (τ y) x) ∨ x = y := by
    first
    | (have i₁ := eq225570 y
       have i₂ := eq261440
       grind)
    | exact superpose eq261440 eq225570
    | (have j0 := eq225570 y
       grind)
    | exact resolve eq225570 eq261440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225570 eq261440
  have eq263665 : (k (τ y) x) = (M.op (τ y) x) ∨ x = y := by grind
  clear eq263463
  have eq266141 : (σ x) = (M.op x (σ y)) ∨ (σ x) = (σ y) ∨ x = (τ x) ∨ x = y := by
    first
    | (have i₁ := eq28 x (σ y)
       have i₂ := eq261863
       grind)
    | exact superpose eq261863 eq28
    | exact resolve eq28 eq261863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq261863
  have eq266143 : x = (τ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq266141
       have r₂ := eq261456
       grind)
    | exact resolve eq266141 eq261456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261456 eq266141
  have eq266157 : (σ x) = (σ y) ∨ x = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq266143
       grind)
    | exact superpose eq266143 eq10
    | exact resolve eq10 eq266143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266143
  have eq266179 : y = (τ (σ x)) ∨ x = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq266157
       grind)
    | exact superpose eq266157 eq9
    | exact resolve eq9 eq266157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266157
  have eq266191 : x = y ∨ x = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq266179
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq266179
    | exact resolve eq266179 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266179
  have eq266192 : x = (σ x) ∨ x = y := by grind
  clear eq266191
  have eq266278 : (M.op x (σ y)) = (M.op (σ y) x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq246612
       have i₂ := eq266192
       grind)
    | exact superpose eq266192 eq246612
    | exact resolve eq246612 eq266192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246612
  have eq266293 : x = (τ x) ∨ x = y := by
    first
    | (have i₁ := eq9 x
       have i₂ := eq266192
       grind)
    | exact superpose eq266192 eq9
    | exact resolve eq9 eq266192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266295 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq266192
       grind)
    | exact superpose eq266192 eq13
    | exact resolve eq13 eq266192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266300 : ∀ X0 : G, (τ (k X0 x)) = (k (τ X0) x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq24 X0 x
       have i₂ := eq266192
       grind)
    | exact superpose eq266192 eq24
    | exact resolve eq24 eq266192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq266522 : (M.op x (σ y)) = (M.op (σ y) x) ∨ x = y := by grind
  clear eq266278
  have eq267942 : ∀ X0 : G, (k X0 x) = (σ (k (τ X0) x)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq266295 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq266295
    | exact resolve eq266295 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266295
  have eq268115 : ∀ X0 : G, (k X0 x) = (k X0 (σ x)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq267942 X0
       have i₂ := eq16 X0 x
       grind)
    | exact superpose eq16 eq267942
    | exact resolve eq267942 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267942
  have eq268924 : (τ x) = (k (τ y) x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq261461
       have i₂ := eq266300 y
       grind)
    | exact superpose eq266300 eq261461
    | exact resolve eq261461 eq266300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261461
  have eq268937 : (τ x) = (k (τ y) x) ∨ x = y := by grind
  clear eq268924
  have eq269053 : (τ x) = (M.op (τ y) x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq263665
       have i₂ := eq268937
       grind)
    | exact superpose eq268937 eq263665
    | exact resolve eq263665 eq268937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263665
  have eq269148 : (τ x) = (M.op (τ y) x) ∨ x = y := by grind
  clear eq269053
  have eq269385 : x ≠ (τ x) ∨ x = (k (τ y) x) ∨ x = y := by
    first
    | (have i₁ := eq93 (τ y) x
       have i₂ := eq269148
       grind)
    | exact superpose eq269148 eq93
    | (have j0 := eq93 (τ y) x
       grind)
    | exact resolve eq93 eq269148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269148
  have eq269558 : x = (k (τ y) x) ∨ x = y := by
    first
    | (have r₁ := eq269385
       have r₂ := eq266293
       grind)
    | exact resolve eq269385 eq266293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266293 eq269385
  have eq269649 : (τ x) = (k (τ (τ y)) x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq266300 (τ y)
       have i₂ := eq269558
       grind)
    | exact superpose eq269558 eq266300
    | exact resolve eq266300 eq269558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266300 eq269558
  have eq269694 : (τ x) = (k (τ (τ y)) x) ∨ x = y := by grind
  clear eq269649
  have eq271178 : (τ x) = (M.op (τ (τ y)) x) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq214117 y
       have i₂ := eq269694
       grind)
    | exact superpose eq269694 eq214117
    | (have j0 := eq214117 y
       grind)
    | exact resolve eq214117 eq269694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214117
  have eq271186 : (σ (τ x)) = (k (τ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq16 (τ y) x
       have i₂ := eq269694
       grind)
    | exact superpose eq269694 eq16
    | exact resolve eq16 eq269694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269694
  have eq271238 : x = (k (τ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq271186
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq271186
    | exact resolve eq271186 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271186
  have eq271241 : x = y ∨ (τ x) = (M.op (τ (τ y)) x) ∨ x = y := by
    first
    | (have i₁ := eq271178
       have i₂ := eq135339
       grind)
    | exact superpose eq135339 eq271178
    | exact resolve eq271178 eq135339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271178
  have eq271242 : (τ x) = (M.op (τ (τ y)) x) ∨ x = y := by grind
  clear eq271241
  have eq271267 : (σ x) = (k y (σ (σ x))) ∨ x = y := by
    first
    | (have i₁ := eq16 y (σ x)
       have i₂ := eq271238
       grind)
    | exact superpose eq271238 eq16
    | exact resolve eq16 eq271238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271238
  have eq271755 : (σ x) ≠ (σ (τ x)) ∨ (σ x) = (σ (k (τ (τ y)) x)) ∨ x = y := by
    first
    | (have i₁ := eq85463 (τ (τ y)) x
       have i₂ := eq271242
       grind)
    | exact superpose eq271242 eq85463
    | (have j0 := eq85463 (τ (τ y)) x
       grind)
    | exact resolve eq85463 eq271242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85463 eq271242
  have eq271903 : x ≠ (σ x) ∨ (σ x) = (σ (k (τ (τ y)) x)) ∨ x = y := by
    first
    | (have i₁ := eq271755
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq271755
    | exact resolve eq271755 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271755
  have eq271930 : (σ x) = (σ (k (τ (τ y)) x)) ∨ x = y := by
    first
    | (have r₁ := eq271903
       have r₂ := eq266192
       grind)
    | exact resolve eq271903 eq266192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266192 eq271903
  have eq271933 : (σ x) = (k (τ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq271930
       have i₂ := eq16 (τ y) x
       grind)
    | exact superpose eq16 eq271930
    | exact resolve eq271930 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271930
  have eq272573 : (σ x) = (k (τ y) x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq268115 (τ y)
       have i₂ := eq271933
       grind)
    | exact superpose eq271933 eq268115
    | exact resolve eq268115 eq271933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271933
  have eq272596 : (σ x) = (k (τ y) x) ∨ x = y := by grind
  clear eq272573
  have eq272642 : (σ x) = (τ x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq268937
       have i₂ := eq272596
       grind)
    | exact superpose eq272596 eq268937
    | exact resolve eq268937 eq272596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268937
  have eq272656 : (σ (σ x)) = (k y (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq16 y x
       have i₂ := eq272596
       grind)
    | exact superpose eq272596 eq16
    | exact resolve eq16 eq272596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq272596
  have eq272739 : (σ x) = (τ x) ∨ x = y := by grind
  clear eq272642
  have eq272884 : x = (σ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq272739
       grind)
    | exact superpose eq272739 eq10
    | exact resolve eq10 eq272739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272739
  have eq273665 : (k y x) = (σ (σ x)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq268115 y
       have i₂ := eq272656
       grind)
    | exact superpose eq272656 eq268115
    | exact resolve eq268115 eq272656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268115 eq272656
  have eq273701 : (k y x) = (σ (σ x)) ∨ x = y := by grind
  clear eq273665
  have eq273757 : (M.op x y) = (σ (σ x)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq161691
       have i₂ := eq273701
       grind)
    | exact superpose eq273701 eq161691
    | exact resolve eq161691 eq273701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161691
  have eq273902 : (M.op x y) = (σ (σ x)) ∨ x = y := by grind
  clear eq273757
  have eq274089 : (σ x) = (k y (M.op x y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq271267
       have i₂ := eq273902
       grind)
    | exact superpose eq273902 eq271267
    | exact resolve eq271267 eq273902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271267
  have eq274122 : (σ x) = (k y (M.op x y)) ∨ x = y := by grind
  clear eq274089
  have eq274300 : (σ (k y x)) = (σ (σ x)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq263071 y
       have i₂ := eq274122
       grind)
    | exact superpose eq274122 eq263071
    | exact resolve eq263071 eq274122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263071
  have eq274334 : (σ (k y x)) = (σ (σ x)) ∨ x = y := by grind
  clear eq274300
  have eq274645 : (σ (σ x)) = (σ (σ (σ x))) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq274334
       have i₂ := eq273701
       grind)
    | exact superpose eq273701 eq274334
    | exact resolve eq274334 eq273701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273701 eq274334
  have eq274759 : (σ (σ x)) = (σ (σ (σ x))) ∨ x = y := by grind
  clear eq274645
  have eq274819 : (M.op x y) = (σ (M.op x y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq274759
       have i₂ := eq273902
       grind)
    | exact superpose eq273902 eq274759
    | exact resolve eq274759 eq273902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273902 eq274759
  have eq274852 : (M.op x y) = (σ (M.op x y)) ∨ x = y := by grind
  clear eq274819
  have eq274943 : (M.op x y) = (τ (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq9 (M.op x y)
       have i₂ := eq274852
       grind)
    | exact superpose eq274852 eq9
    | exact resolve eq9 eq274852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274852
  have eq275011 : (M.op x y) = (τ x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq261835
       have i₂ := eq274943
       grind)
    | exact superpose eq274943 eq261835
    | exact resolve eq261835 eq274943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261835 eq274943
  have eq275065 : (M.op x y) = (τ x) ∨ x = y := by grind
  clear eq275011
  have eq275137 : (σ (τ x)) ≠ (M.op x (σ y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq168251
       have i₂ := eq275065
       grind)
    | exact superpose eq275065 eq168251
    | exact resolve eq168251 eq275065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168251
  have eq275207 : (σ x) = (k y (τ x)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq274122
       have i₂ := eq275065
       grind)
    | exact superpose eq275065 eq274122
    | exact resolve eq274122 eq275065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274122 eq275065
  have eq275459 : (σ x) = (k y (τ x)) ∨ x = y := by grind
  clear eq275207
  have eq275479 : (σ (τ x)) ≠ (M.op x (σ y)) ∨ x = y := by grind
  clear eq275137
  have eq275566 : x ≠ (M.op x (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq275479
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq275479
    | exact resolve eq275479 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275479
  have eq275862 : (σ (σ x)) = (k (σ y) x) ∨ x = y := by
    first
    | (have i₁ := eq17 x y
       have i₂ := eq275459
       grind)
    | exact superpose eq275459 eq17
    | exact resolve eq17 eq275459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq275459
  have eq275951 : (σ (σ x)) = (M.op (σ y) x) ∨ x = y := by
    first
    | (have i₁ := eq275862
       have i₂ := eq224995
       grind)
    | exact superpose eq224995 eq275862
    | exact resolve eq275862 eq224995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275862
  have eq276249 : x ≠ (σ (σ x)) ∨ x = (k (σ y) x) ∨ x = y := by
    first
    | (have i₁ := eq93 (σ y) x
       have i₂ := eq275951
       grind)
    | exact superpose eq275951 eq93
    | (have j0 := eq93 (σ y) x
       grind)
    | exact resolve eq93 eq275951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq275951
  have eq276370 : x = (k (σ y) x) ∨ x = y := by
    first
    | (have r₁ := eq276249
       have r₂ := eq272884
       grind)
    | exact resolve eq276249 eq272884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272884 eq276249
  have eq276401 : x = (M.op (σ y) x) ∨ x = y := by
    first
    | (have i₁ := eq276370
       have i₂ := eq224995
       grind)
    | exact superpose eq224995 eq276370
    | exact resolve eq276370 eq224995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224995 eq276370
  have eq278916 : x = (M.op x (σ y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq276401
       have i₂ := eq266522
       grind)
    | exact superpose eq266522 eq276401
    | exact resolve eq276401 eq266522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266522 eq276401
  have eq278985 : x = (M.op x (σ y)) ∨ x = y := by grind
  clear eq278916
  have eq278999 : x = y := by
    first
    | (have r₁ := eq278985
       have r₂ := eq275566
       grind)
    | exact resolve eq278985 eq275566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275566 eq278985
  have eq279005 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq278999
       grind)
    | exact superpose eq278999 eq14
    | exact resolve eq14 eq278999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq279084 : x = (M.op x x) := by
    first
    | (have i₁ := eq135339
       have i₂ := eq278999
       grind)
    | exact superpose eq278999 eq135339
    | exact resolve eq135339 eq278999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135339
  have eq279103 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq135413
       have i₂ := eq278999
       grind)
    | exact superpose eq278999 eq135413
    | exact resolve eq135413 eq278999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135413 eq278999
  have eq279438 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq279103
  have eq279484 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq279005
       have i₂ := eq279084
       grind)
    | exact superpose eq279084 eq279005
    | exact resolve eq279005 eq279084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279005 eq279084
  have eq279494 : False := by grind
  exact eq279494

/-- `Equation4392`: `x ◇ (x ◇ x) = (y ◇ z) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation4392 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4392 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4392.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X2) X1) := by
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
  have eq18 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X3 X4) X3) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq8 x X3 X4
       have i₂ := eq8 x X0 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X2)) = (M.op (M.op (M.op X0 X1) X0) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 X3 (M.op X3 X3)
       have i₂ := eq8 X3 X0 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 X1)) = (M.op (M.op X0 (M.op X0 X0)) (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 (M.op X2 X3) X2
       have i₂ := eq8 X0 X2 X3
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 x x
       have i₂ := eq8 X1 x x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  have eq26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  clear eq16
  have eq27 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq23 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq23
    | exact resolve eq23 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq30 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X2) = (M.op X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 X2 X3
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq33 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq36 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq12 X0 (τ X1)
       grind)
    | exact superpose eq12 eq17
    | (have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq17 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq67 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X0 X1
       have i₂ := eq12 X0 (σ X1)
       grind)
    | exact superpose eq12 eq26
    | (have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq26 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X1)) = (M.op X2 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 X1 X2
       have i₂ := eq12 X2 X0
       grind)
    | (have i₁ := eq21 X0 X1
       have i₂ := eq12 X0 (M.op X1 X1)
       grind)
    | exact superpose eq12 eq21
    | (have j1 := eq12 X2 X0
       grind)
    | exact resolve eq21 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X2) = (M.op (M.op X0 (M.op X0 X0)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq18 X1 (M.op X1 X1) X2 X3
       have i₂ := eq21 X1 X0
       grind)
    | (have i₁ := eq18 X1 (M.op X1 X1) X2 X3
       have i₂ := eq21 X0 X1
       grind)
    | exact superpose eq21 eq18
    | exact resolve eq18 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X1)) = (M.op (M.op X0 (M.op X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2 (M.op X2 X2)
       have i₂ := eq21 X2 X0
       grind)
    | (have i₁ := eq8 X1 X2 (M.op X2 X2)
       have i₂ := eq21 X0 X2
       grind)
    | exact superpose eq21 eq8
    | exact resolve eq8 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, (k (τ X1) X0) = (M.op (τ X1) X0) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq27 X1
       have i₂ := eq12 (τ X1) X0
       grind)
    | (have i₁ := eq27 X0
       have i₂ := eq12 X0 (M.op (τ X0) (τ X0))
       grind)
    | exact superpose eq12 eq27
    | (have j1 := eq12 (τ X1) X0
       grind)
    | exact resolve eq27 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq31 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq31
    | exact resolve eq31 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq31 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq119 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq41
  have eq133 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq119 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq119
    | exact resolve eq119 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq139 : ∀ X0 X1 X2 X4 X5 X6 : G, (M.op (M.op (M.op X0 X1) X0) X2) = (M.op (M.op (M.op X4 X5) X4) X6) := by
    intro X0 X1 X2 X4 X5 X6
    first
    | (have i₁ := eq19 X4 X5 x X6
       have i₂ := eq19 X0 X1 x X2
       grind)
    | (have i₁ := eq19 X0 X1 (M.op (M.op X0 X1) X0) x
       have i₂ := eq19 X0 X1 X2 (M.op (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0))
       grind)
    | exact superpose eq19 eq19
    | exact resolve eq19 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq170 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X5) X4) = (M.op (M.op (M.op (M.op X0 X1) X0) X2) X3) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq18 X3 (M.op X3 X3) X4 X5
       have i₂ := eq19 X0 X1 X3 X2
       grind)
    | (have i₁ := eq18 (M.op (M.op X0 X1) X0) X3 X3 X4
       have i₂ := eq19 X0 X1 X2 X3
       grind)
    | exact superpose eq19 eq18
    | exact resolve eq18 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq171 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X3 X3)) = (M.op (M.op (M.op (M.op X0 X1) X0) X2) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 X3 X4 (M.op X4 X4)
       have i₂ := eq19 X0 X1 X4 X2
       grind)
    | (have i₁ := eq8 X0 (M.op (M.op X0 X1) X0) X3
       have i₂ := eq19 X0 X1 X2 X3
       grind)
    | exact superpose eq19 eq8
    | exact resolve eq8 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq194 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op (M.op X1 X2) X1) ∨ (M.op (M.op X1 X2) X1) = (k (M.op (M.op X1 X2) X1) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq111 (M.op (M.op X1 X2) X1) X3
       have i₂ := eq19 X1 X2 X0 X3
       grind)
    | (have i₁ := eq111 X2 (M.op X2 X2)
       have i₂ := eq19 X0 X1 X2 X3
       grind)
    | exact superpose eq19 eq111
    | (have j0 := eq111 (M.op (M.op X1 X2) X1) X3
       grind)
    | (have r₁ := eq111 (M.op (M.op (M.op X0 X1) X0) X3) (M.op (M.op (M.op (M.op X0 X1) X0) X3) (M.op (M.op (M.op X0 X1) X0) X3))
       have r₂ := eq19 X0 X1 (M.op (M.op (M.op X0 X1) X0) X3) X3
       grind)
    | exact resolve eq111 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : ∀ X1 X2 X3 : G, (M.op (M.op X1 X2) X1) = (k (M.op (M.op X1 X2) X1) X3) := by
    intro X1 X2 X3
    first
    | (have j0 := eq194 x X1 X2 X3
       grind)
    | (have r₁ := eq194 x X1 X2 X3
       have r₂ := eq8 x X1 X2
       grind)
    | exact resolve eq194 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq332 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X0) = X3 ∨ (M.op X2 X3) = (k X2 X3) ∨ (M.op X2 X2) = (k X2 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X2 X3
       have i₂ := eq30 X2 X2 X0 X1
       grind)
    | exact superpose eq30 eq12
    | (have j0 := eq12 X2 (k X2 X2)
       have j1 := eq30 X3 X2 X2 X3
       grind)
    | exact resolve eq12 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq362 : ∀ X0 X1 X2 X3 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (M.op X2 X3) X2) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq30 (σ X1) (σ X0) X2 X3
       grind)
    | exact superpose eq30 eq13
    | (have j1 := eq30 (σ X1) (σ X0) X2 X3
       grind)
    | exact resolve eq13 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq370 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq133 X1
       have i₂ := eq12 (σ X1) X0
       grind)
    | (have i₁ := eq133 X0
       have i₂ := eq12 X0 (M.op (σ X0) (σ X0))
       grind)
    | exact superpose eq12 eq133
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq133 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq757 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X0) ≠ (M.op X2 (M.op X2 X2)) ∨ (M.op X2 (M.op X2 X2)) = (k (M.op X2 (M.op X2 X2)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq111 (M.op X2 (M.op X2 X2)) X3
       have i₂ := eq87 X2 X3 X0 X1
       grind)
    | (have i₁ := eq111 (M.op X2 X3) X2
       have i₂ := eq87 X0 X1 X2 X3
       grind)
    | exact superpose eq87 eq111
    | (have j0 := eq111 (M.op X2 (M.op X2 X2)) X3
       grind)
    | (have r₁ := eq111 (M.op (M.op X0 (M.op X0 X0)) X1) (M.op X0 (M.op X0 X0))
       have r₂ := eq87 X0 X1 (M.op X0 (M.op X0 X0)) X1
       grind)
    | exact resolve eq111 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq758 : ∀ X2 X3 : G, (M.op X2 (M.op X2 X2)) = (k (M.op X2 (M.op X2 X2)) X3) := by
    intro X2 X3
    first
    | (have j0 := eq757 x x X2 X3
       grind)
    | (have r₁ := eq757 x X2 x X3
       have r₂ := eq8 x x X2
       grind)
    | exact resolve eq757 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757
  have eq784 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq33 x y
       grind)
    | exact superpose eq33 eq14
    | (have j1 := eq33 x y
       grind)
    | exact resolve eq14 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq808 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq9
    | (have j1 := eq33 X0 X1
       grind)
    | exact resolve eq9 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq841 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq33 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq1268 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X0 X0))) = (k (σ (M.op X0 (M.op X0 X0))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (M.op X0 (M.op X0 X0))
       have i₂ := eq758 X0 (τ X1)
       grind)
    | exact superpose eq758 eq17
    | exact resolve eq17 eq758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq1869 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 : G, (M.op (M.op (M.op X3 X4) X3) X5) = (M.op (M.op (M.op (M.op (M.op X0 X1) X0) X2) X6) X7) := by
    intro X0 X1 X2 X3 X4 X5 X6 X7
    first
    | (have i₁ := eq139 X3 X4 X5 X6 (M.op X6 X6) X7
       have i₂ := eq19 X0 X1 X6 X2
       grind)
    | (have i₁ := eq139 X0 X1 X2 (M.op (M.op X0 X1) X0) X3 X6
       have i₂ := eq19 X0 X1 X2 X3
       grind)
    | exact superpose eq19 eq139
    | exact resolve eq139 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq2393 : ∀ X0 X1 X2 X3 X4 X5 X8 X9 : G, (M.op (M.op X4 X5) X4) = (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) X0) X2) X3) X8) X9) := by
    intro X0 X1 X2 X3 X4 X5 X8 X9
    first
    | (have i₁ := eq170 x x X8 X9 X4 X5
       have i₂ := eq170 X0 X1 X2 X3 x x
       grind)
    | (have i₁ := eq170 (M.op (M.op X0 X1) X0) X2 X2 X3 X4 X5
       have i₂ := eq170 X0 X1 X2 (M.op (M.op X0 X1) X0) X4 X5
       grind)
    | exact superpose eq170 eq170
    | exact resolve eq170 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170
  have eq2774 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X5 (M.op X5 X5)) X6) = (M.op (M.op (M.op (M.op (M.op X0 X1) X0) X2) X3) X4) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq87 X5 X6 X4 (M.op X4 X4)
       have i₂ := eq171 X0 X1 X2 X4 X3
       grind)
    | (have i₁ := eq87 X0 X1 (M.op (M.op (M.op X0 X1) X0) X2) X4
       have i₂ := eq171 X0 X1 X2 X3 X4
       grind)
    | exact superpose eq171 eq87
    | exact resolve eq87 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171
  have eq2948 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq36 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq36
    | exact resolve eq36 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3032 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = X1 ∨ (k (σ (τ X1)) X0) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq27 X1
       have i₂ := eq36 (τ X1) X0
       grind)
    | exact superpose eq36 eq27
    | (have j1 := eq36 (τ X1) X0
       grind)
    | exact resolve eq27 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq3034 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq36 X0 X1
       grind)
    | exact superpose eq36 eq10
    | (have j1 := eq36 X0 X1
       grind)
    | exact resolve eq10 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq3052 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (k (σ (τ X1)) X0) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3032 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3032
    | (have j0 := eq3032 X0 X1
       grind)
    | exact resolve eq3032 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3032
  have eq3074 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2948 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq2948
    | (have j0 := eq2948 X0 X1
       grind)
    | exact resolve eq2948 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2948
  have eq3099 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X1) (τ X0))) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3052 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq3052
    | (have j0 := eq3052 X0 X1
       grind)
    | exact resolve eq3052 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3052
  have eq3162 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq3865 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq77 (σ y) X0 (σ x)
       grind)
    | exact superpose eq77 eq14
    | (have j1 := eq77 (σ y) x (σ x)
       grind)
    | exact resolve eq14 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq3900 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    intro X0
    first
    | (have i₁ := eq3865 X0
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq3865
    | (have j0 := eq3865 X0
       grind)
    | exact resolve eq3865 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3865
  have eq4758 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X1) = (M.op (M.op (σ X0) (σ (k X0 X0))) X3) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq87 (σ X0) X3 X1 X2
       have i₂ := eq104 X0 X0
       grind)
    | exact superpose eq104 eq87
    | (have j1 := eq104 X0 X0
       grind)
    | exact resolve eq87 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq5501 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq91 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq91
    | (have j0 := eq91 X1 (σ X0)
       grind)
    | exact resolve eq91 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq5570 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5501 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq5501
    | (have j0 := eq5501 X0 X1
       grind)
    | exact resolve eq5501 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5501
  have eq6214 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq841 X0
       have i₂ := eq5570 X0 X0
       grind)
    | exact superpose eq5570 eq841
    | (have j0 := eq841 X0
       have j1 := eq5570 X0 X0
       grind)
    | (have r₁ := eq841 x
       have r₂ := eq5570 x x
       grind)
    | exact resolve eq841 eq5570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5570
  have eq6241 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq6214 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6214
  have eq7736 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq784
       have i₂ := eq3162 y x
       grind)
    | exact superpose eq3162 eq784
    | (have j1 := eq3162 y x
       grind)
    | (have r₁ := eq784
       have r₂ := eq3162 y x
       grind)
    | exact resolve eq784 eq3162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3162
  have eq7737 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq784
       have i₂ := eq3074 y x
       grind)
    | exact superpose eq3074 eq784
    | (have j1 := eq3074 (σ y) (σ x)
       grind)
    | (have r₁ := eq784
       have r₂ := eq3074 y x
       grind)
    | exact resolve eq784 eq3074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq784
  have eq7738 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq7737
  have eq7739 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by grind
  clear eq7736
  have eq7751 : x = (k x (τ (σ y))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq133 x
       have i₂ := eq7738
       grind)
    | exact superpose eq7738 eq133
    | exact resolve eq133 eq7738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7810 : x = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq7751
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq7751
    | exact resolve eq7751 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7751
  have eq7916 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq7810
       grind)
    | exact superpose eq7810 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq7810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7919 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq3074 y x
       have i₂ := eq7810
       grind)
    | exact superpose eq7810 eq3074
    | (have j0 := eq3074 y x
       grind)
    | exact resolve eq3074 eq7810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3074 eq7810
  have eq7920 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by grind
  clear eq7919
  have eq7921 : x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq7916
  have eq8473 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq8 X0 x y
       have i₂ := eq7921
       grind)
    | exact superpose eq7921 eq8
    | exact resolve eq8 eq7921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8475 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op x x) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1 x y
       have i₂ := eq7921
       grind)
    | exact superpose eq7921 eq18
    | exact resolve eq18 eq7921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7921
  have eq10722 : x = (k x (τ (σ y))) ∨ x = (k x y) := by
    first
    | (have i₁ := eq133 x
       have i₂ := eq7739
       grind)
    | exact superpose eq7739 eq133
    | exact resolve eq133 eq7739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq7739
  have eq10790 : x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq10722
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq10722
    | exact resolve eq10722 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10722
  have eq10791 : x = (k x y) := by grind
  clear eq10790
  have eq11365 : (σ y) = (σ (k x x)) ∨ x = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq808 x x
       have i₂ := eq7738
       grind)
    | exact superpose eq7738 eq808
    | exact resolve eq808 eq7738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq808
  have eq11449 : (σ y) = (σ (k x x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq11365
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq11365
    | exact resolve eq11365 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11365
  have eq12170 : (M.op (σ x) (σ y)) = (M.op x x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq8473 (σ x)
       have i₂ := eq7738
       grind)
    | exact superpose eq7738 eq8473
    | exact resolve eq8473 eq7738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12324 : (M.op (σ x) (σ y)) = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq12170
  have eq13105 : ∀ X0 : G, (M.op x x) = (M.op (M.op x x) X0) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq8475 X0 (M.op X0 X0)
       have i₂ := eq8473 X0
       grind)
    | exact superpose eq8473 eq8475
    | exact resolve eq8475 eq8473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8473
  have eq13317 : ∀ X0 : G, (M.op x x) = (M.op (M.op x x) X0) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq13105 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13105
  have eq14866 : (σ (M.op x y)) ≠ (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq12324
       grind)
    | exact superpose eq12324 eq14
    | exact resolve eq14 eq12324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12324
  have eq15332 : (σ x) ≠ (M.op x x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14866
       have i₂ := eq7920
       grind)
    | exact superpose eq7920 eq14866
    | exact resolve eq14866 eq7920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7920 eq14866
  have eq15333 : (σ x) ≠ (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq15332
  have eq31624 : ∀ X0 X1 : G, (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 (τ (σ X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq26 (σ X0) X1
       have i₂ := eq370 (σ X1) X0
       grind)
    | exact superpose eq370 eq26
    | (have j1 := eq370 (σ X1) X0
       grind)
    | exact resolve eq26 eq370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq370
  have eq31654 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 (τ (σ X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq31624 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq31624
    | (have j0 := eq31624 X0 X1
       grind)
    | exact resolve eq31624 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31624
  have eq31694 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq31654 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq31654
    | (have j0 := eq31654 X0 X1
       grind)
    | exact resolve eq31654 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31654
  have eq34793 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op (M.op X1 X2) X1) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq332 X1 X2 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332
  have eq34794 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X1) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq34793 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34793
  have eq35071 : ∀ X0 X3 : G, (k X0 X3) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X3
    first
    | (have i₁ := eq195 x x X3
       have i₂ := eq34794 X0 x x
       grind)
    | (have i₁ := eq195 x x X3
       have i₂ := eq34794 (M.op (M.op x x) x) x x
       grind)
    | exact superpose eq34794 eq195
    | (have j1 := eq34794 X0 x x
       grind)
    | exact resolve eq195 eq34794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq35131 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq20 (M.op x x) X1 x x
       have i₂ := eq34794 X0 (M.op x x) (M.op (M.op x x) (M.op x x))
       grind)
    | (have i₁ := eq20 X0 X1 x x
       have i₂ := eq34794 (M.op (M.op X0 (M.op X0 X0)) (M.op x x)) X1 x
       grind)
    | exact superpose eq34794 eq20
    | (have j1 := eq34794 X0 X1 x
       grind)
    | exact resolve eq20 eq34794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq34794
  have eq36096 : ∀ X0 X1 X2 X3 : G, (σ (k X0 X1)) ≠ (M.op (M.op X2 X3) X2) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq362 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362
  have eq59799 : (k x x) = (τ (σ y)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq11449
       grind)
    | exact superpose eq11449 eq9
    | exact resolve eq9 eq11449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11449
  have eq59878 : y = (k x x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq59799
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq59799
    | exact resolve eq59799 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59799
  have eq60960 : x = y ∨ y = (M.op x x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq35071 x x
       have i₂ := eq59878
       grind)
    | exact superpose eq59878 eq35071
    | exact resolve eq35071 eq59878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35071 eq59878
  have eq60965 : y = (M.op x x) ∨ x = y := by grind
  clear eq60960
  have eq131398 : ∀ X0 : G, (k (σ (τ X0)) X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq3034 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3034
  have eq131399 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq131398 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq131398
    | (have j0 := eq131398 X0
       grind)
    | exact resolve eq131398 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131398
  have eq173488 : (k x x) = (τ (σ y)) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq31694 x x
       have i₂ := eq7738
       grind)
    | exact superpose eq7738 eq31694
    | (have j0 := eq31694 x x
       grind)
    | exact resolve eq31694 eq7738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7738 eq31694
  have eq173622 : y = (k x x) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq173488
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq173488
    | exact resolve eq173488 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173488
  have eq229825 : x ≠ y ∨ x = (σ (M.op (τ x) (τ x))) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq131399 x
       have i₂ := eq173622
       grind)
    | exact superpose eq173622 eq131399
    | (have j0 := eq131399 x
       grind)
    | (have r₁ := eq131399 x
       have r₂ := eq173622
       grind)
    | exact resolve eq131399 eq173622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173622
  have eq229859 : x ≠ y ∨ x = (σ (M.op (τ x) (τ x))) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq131399 x
       grind)
    | (have r₁ := eq229825
       have r₂ := eq131399 x
       grind)
    | exact resolve eq229825 eq131399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131399 eq229825
  have eq229867 : x = (σ (M.op (τ x) (τ x))) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq229859
       have r₂ := eq60965
       grind)
    | exact resolve eq229859 eq60965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60965 eq229859
  have eq230637 : x = (k x x) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq3099 x x
       have i₂ := eq229867
       grind)
    | exact superpose eq229867 eq3099
    | (have j0 := eq3099 x x
       grind)
    | exact resolve eq3099 eq229867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3099
  have eq230651 : (τ x) = (M.op (τ x) (τ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (M.op (τ x) (τ x))
       have i₂ := eq229867
       grind)
    | exact superpose eq229867 eq9
    | exact resolve eq9 eq229867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229867
  have eq230676 : x = (k x x) ∨ y = (M.op x x) := by grind
  clear eq230637
  have eq230959 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq841 x
       have i₂ := eq230676
       grind)
    | exact superpose eq230676 eq841
    | (have j0 := eq841 x
       grind)
    | exact resolve eq841 eq230676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230676
  have eq230994 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq230959
  have eq232110 : (M.op x x) = (M.op (τ x) (τ x)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq8475 (τ x) (τ x)
       have i₂ := eq230651
       grind)
    | exact superpose eq230651 eq8475
    | exact resolve eq8475 eq230651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8475
  have eq232129 : (M.op x x) = (M.op (τ x) (τ x)) ∨ y = (M.op x x) := by grind
  clear eq232110
  have eq236709 : (M.op x x) = (τ x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq230651
       have i₂ := eq232129
       grind)
    | exact superpose eq232129 eq230651
    | exact resolve eq230651 eq232129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230651 eq232129
  have eq236840 : (M.op x x) = (τ x) ∨ y = (M.op x x) := by grind
  clear eq236709
  have eq237212 : ∀ X0 : G, (τ x) = (M.op (τ x) X0) ∨ y = (τ x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq13317 X0
       have i₂ := eq236840
       grind)
    | exact superpose eq236840 eq13317
    | exact resolve eq13317 eq236840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13317
  have eq237213 : (σ x) ≠ (τ x) ∨ y = (τ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq15333
       have i₂ := eq236840
       grind)
    | exact superpose eq236840 eq15333
    | exact resolve eq15333 eq236840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15333
  have eq237396 : y ≠ (τ x) ∨ y = (M.op x x) := by grind
  clear eq236840
  have eq237403 : (σ x) ≠ (τ x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq237213
       have r₂ := eq237396
       grind)
    | exact resolve eq237213 eq237396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237213
  have eq237404 : ∀ X0 : G, (τ x) = (M.op (τ x) X0) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq237212 X0
       grind)
    | (have r₁ := eq237212 X0
       have r₂ := eq237396
       grind)
    | exact resolve eq237212 eq237396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237212 eq237396
  have eq239229 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (τ x) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (τ x) X0 X1
       have i₂ := eq237404 (M.op (τ x) (τ x))
       grind)
    | exact superpose eq237404 eq8
    | exact resolve eq8 eq237404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237404
  have eq250337 : (M.op (σ x) (σ x)) = (τ x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq239229 (σ x) (σ x)
       have i₂ := eq230994
       grind)
    | exact superpose eq230994 eq239229
    | exact resolve eq239229 eq230994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239229
  have eq250985 : (M.op (σ x) (σ x)) = (τ x) ∨ y = (M.op x x) := by grind
  clear eq250337
  have eq255598 : (σ x) = (τ x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq230994
       have i₂ := eq250985
       grind)
    | exact superpose eq250985 eq230994
    | exact resolve eq230994 eq250985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230994 eq250985
  have eq255746 : (σ x) = (τ x) ∨ y = (M.op x x) := by grind
  clear eq255598
  have eq255759 : y = (M.op x x) := by
    first
    | (have r₁ := eq255746
       have r₂ := eq237403
       grind)
    | exact resolve eq255746 eq237403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237403 eq255746
  have eq255944 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq21 X0 x
       have i₂ := eq255759
       grind)
    | exact superpose eq255759 eq21
    | exact resolve eq21 eq255759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq255949 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op x y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq88 x X0 X1
       have i₂ := eq255759
       grind)
    | exact superpose eq255759 eq88
    | exact resolve eq88 eq255759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq256001 : ∀ X0 : G, (M.op x y) = (k (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq758 x x
       have i₂ := eq255759
       grind)
    | exact superpose eq255759 eq758
    | exact resolve eq758 eq255759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq758
  have eq256009 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq1268 x x
       have i₂ := eq255759
       grind)
    | exact superpose eq255759 eq1268
    | exact resolve eq1268 eq255759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1268
  have eq256030 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op x y) = X0 := by
    intro X0
    first
    | (have i₁ := eq35131 X0 x
       have i₂ := eq255759
       grind)
    | exact superpose eq255759 eq35131
    | (have j0 := eq35131 X0 x
       grind)
    | exact resolve eq35131 eq255759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq256046 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq8 X0 x x
       have i₂ := eq255759
       grind)
    | exact superpose eq255759 eq8
    | exact resolve eq8 eq255759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq256048 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1 x x
       have i₂ := eq255759
       grind)
    | exact superpose eq255759 eq18
    | exact resolve eq18 eq255759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq256060 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X0) X2) = (M.op (M.op y x) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq139 X0 X1 X2 x x X3
       have i₂ := eq255759
       grind)
    | exact superpose eq255759 eq139
    | exact resolve eq139 eq255759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq256223 : ∀ X1 : G, (M.op y x) = (M.op (M.op x y) X1) := by
    intro X1
    first
    | (have i₁ := eq255949 x X1
       have i₂ := eq256046 x
       grind)
    | exact superpose eq256046 eq255949
    | exact resolve eq255949 eq256046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255949
  have eq257232 : ∀ X0 X1 X5 : G, (M.op (M.op X0 (M.op X0 X0)) X1) = (M.op (M.op x y) X5) := by
    intro X0 X1 X5
    first
    | (have i₁ := eq2774 x x x (M.op (M.op (M.op (M.op x x) x) x) (M.op (M.op (M.op x x) x) x)) X5 X0 X1
       have i₂ := eq255944 (M.op (M.op (M.op x x) x) x)
       grind)
    | exact superpose eq255944 eq2774
    | exact resolve eq2774 eq255944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2774
  have eq257255 : ∀ X0 X1 X2 : G, (M.op x y) = (M.op (M.op (M.op X0 X1) X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1869 x x x X0 X1 X2 x (M.op (M.op (M.op (M.op (M.op x x) x) x) x) (M.op (M.op (M.op (M.op x x) x) x) x))
       have i₂ := eq255944 (M.op (M.op (M.op (M.op x x) x) x) x)
       grind)
    | exact superpose eq255944 eq1869
    | exact resolve eq1869 eq255944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1869
  have eq257267 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2393 x x x x X0 X1 x (M.op (M.op (M.op (M.op (M.op (M.op x x) x) x) x) x) (M.op (M.op (M.op (M.op (M.op x x) x) x) x) x))
       have i₂ := eq255944 (M.op (M.op (M.op (M.op (M.op x x) x) x) x) x)
       grind)
    | exact superpose eq255944 eq2393
    | exact resolve eq2393 eq255944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2393 eq255944
  have eq257275 : ∀ X2 : G, (M.op x y) = (M.op (M.op y x) X2) := by
    intro X2
    first
    | (have i₁ := eq257255 x x X2
       have i₂ := eq256048 x x
       grind)
    | exact superpose eq256048 eq257255
    | exact resolve eq257255 eq256048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257255
  have eq257287 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) X1) = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq257232 X0 X1 x
       have i₂ := eq256223 x
       grind)
    | exact superpose eq256223 eq257232
    | exact resolve eq257232 eq256223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256223 eq257232
  have eq257755 : ∀ X1 : G, (M.op y x) = (M.op (M.op y x) X1) := by
    intro X1
    first
    | (have i₁ := eq257287 x X1
       have i₂ := eq256046 x
       grind)
    | exact superpose eq256046 eq257287
    | exact resolve eq257287 eq256046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257287
  have eq257998 : (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq257755 x
       have i₂ := eq257275 x
       grind)
    | exact superpose eq257275 eq257755
    | exact resolve eq257755 eq257275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257755
  have eq258917 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X1) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq36096 (M.op x y) X0 X2 x
       have i₂ := eq256001 X0
       grind)
    | exact superpose eq256001 eq36096
    | exact resolve eq36096 eq256001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36096 eq256001
  have eq258961 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq258917 X0 x x
       have i₂ := eq256048 x x
       grind)
    | exact superpose eq256048 eq258917
    | (have j0 := eq258917 X0 x x
       grind)
    | exact resolve eq258917 eq256048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258917
  have eq258967 : ∀ X0 : G, (M.op x y) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq258961 X0
       have i₂ := eq257998
       grind)
    | exact superpose eq257998 eq258961
    | (have j0 := eq258961 X0
       grind)
    | exact resolve eq258961 eq257998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258961
  have eq261568 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op y x) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq256048 X1 (M.op X1 X1)
       have i₂ := eq35131 X0 X1
       grind)
    | (have i₁ := eq256048 X0 X1
       have i₂ := eq35131 (M.op X0 X1) X1
       grind)
    | exact superpose eq35131 eq256048
    | (have j1 := eq35131 X0 X1
       grind)
    | exact resolve eq256048 eq35131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35131
  have eq262986 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op x y) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq261568 X0 X1
       have i₂ := eq257998
       grind)
    | exact superpose eq257998 eq261568
    | (have j0 := eq261568 X0 X1
       grind)
    | exact resolve eq261568 eq257998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261568
  have eq291748 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq256009 (σ (M.op x y))
       have i₂ := eq256030 (σ (M.op x y))
       grind)
    | exact superpose eq256030 eq256009
    | (have j1 := eq256030 (σ (M.op x y))
       grind)
    | exact resolve eq256009 eq256030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256009 eq256030
  have eq291782 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq258967 (M.op x y)
       grind)
    | (have r₁ := eq291748
       have r₂ := eq258967 x
       grind)
    | exact resolve eq291748 eq258967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258967 eq291748
  have eq361155 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) X1) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq87 X0 X1 (σ (M.op x y)) (σ (M.op x y))
       have i₂ := eq291782
       grind)
    | exact superpose eq291782 eq87
    | exact resolve eq87 eq291782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq361241 : ∀ X0 X1 : G, (M.op (M.op y x) X1) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq256060 (σ (M.op x y)) (σ (M.op x y)) X0 X1
       have i₂ := eq291782
       grind)
    | exact superpose eq291782 eq256060
    | exact resolve eq256060 eq291782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256060
  have eq361247 : ∀ X0 X1 : G, (M.op (σ (M.op x y)) X0) = (M.op (M.op y x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq361241 X0 X1
       have i₂ := eq291782
       grind)
    | exact superpose eq291782 eq361241
    | exact resolve eq361241 eq291782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361241
  have eq361288 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op X0 (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq361155 X0 X1
       have i₂ := eq291782
       grind)
    | exact superpose eq291782 eq361155
    | exact resolve eq361155 eq291782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291782 eq361155
  have eq361372 : ∀ X0 : G, (M.op x y) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq361247 X0 x
       have i₂ := eq257275 x
       grind)
    | exact superpose eq257275 eq361247
    | exact resolve eq361247 eq257275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361247
  have eq361397 : ∀ X1 : G, (σ (M.op x y)) = (M.op (M.op y x) X1) := by
    intro X1
    first
    | (have i₁ := eq361288 x X1
       have i₂ := eq256046 x
       grind)
    | exact superpose eq256046 eq361288
    | exact resolve eq361288 eq256046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256046 eq361288
  have eq361471 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq361397 x
       have i₂ := eq257275 x
       grind)
    | exact superpose eq257275 eq361397
    | exact resolve eq361397 eq257275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257275 eq361397
  have eq362090 : (M.op x y) = (τ (M.op x y)) := by
    first
    | (have i₁ := eq9 (M.op x y)
       have i₂ := eq361471
       grind)
    | exact superpose eq361471 eq9
    | exact resolve eq9 eq361471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq363907 : (M.op x y) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq3900 (σ (M.op x y))
       have i₂ := eq361372 (M.op (σ (M.op x y)) (σ (M.op x y)))
       grind)
    | exact superpose eq361372 eq3900
    | exact resolve eq3900 eq361372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3900 eq361372
  have eq363969 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have r₁ := eq363907
       have r₂ := eq361471
       grind)
    | exact resolve eq363907 eq361471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363907
  have eq364243 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq363969
       have i₂ := eq10791
       grind)
    | exact superpose eq10791 eq363969
    | exact resolve eq363969 eq10791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10791 eq363969
  have eq364647 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq364243
       grind)
    | exact superpose eq364243 eq14
    | exact resolve eq14 eq364243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq364924 : (M.op x y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq257267 (σ x) (σ y)
       have i₂ := eq364243
       grind)
    | exact superpose eq364243 eq257267
    | exact resolve eq257267 eq364243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257267
  have eq365123 : (M.op x y) ≠ (σ x) := by
    first
    | (have i₁ := eq364647
       have i₂ := eq361471
       grind)
    | exact superpose eq361471 eq364647
    | exact resolve eq364647 eq361471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364647
  have eq365416 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (σ x) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq365123
       have i₂ := eq262986 X0 X1
       grind)
    | (have i₁ := eq365123
       have i₂ := eq262986 x y
       grind)
    | exact superpose eq262986 eq365123
    | (have j1 := eq262986 X0 X1
       grind)
    | exact resolve eq365123 eq262986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262986
  have eq365941 : (M.op x y) = (σ x) ∨ (M.op x x) = (k x x) := by
    first
    | (have i₁ := eq6241 x
       have i₂ := eq364924
       grind)
    | exact superpose eq364924 eq6241
    | (have j0 := eq6241 x
       grind)
    | exact resolve eq6241 eq364924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6241
  have eq365970 : (k (τ (σ x)) x) = (τ (M.op x y)) ∨ (M.op x y) = (σ x) := by
    first
    | (have i₁ := eq67 (σ x) x
       have i₂ := eq364924
       grind)
    | exact superpose eq364924 eq67
    | exact resolve eq67 eq364924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq366595 : (k (τ (σ x)) x) = (τ (M.op x y)) := by
    first
    | (have r₁ := eq365970
       have r₂ := eq365123
       grind)
    | exact resolve eq365970 eq365123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365970
  have eq366607 : (M.op x x) = (k x x) := by
    first
    | (have j1 := eq365416 x x
       grind)
    | (have r₁ := eq365941
       have r₂ := eq365416 x y
       grind)
    | exact resolve eq365941 eq365416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365416 eq365941
  have eq366730 : (M.op x y) = (k (τ (σ x)) x) := by
    first
    | (have i₁ := eq366595
       have i₂ := eq362090
       grind)
    | exact superpose eq362090 eq366595
    | exact resolve eq366595 eq362090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362090 eq366595
  have eq366735 : y = (k x x) := by
    first
    | (have i₁ := eq366607
       have i₂ := eq255759
       grind)
    | exact superpose eq255759 eq366607
    | exact resolve eq366607 eq255759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255759 eq366607
  have eq366815 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq366730
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq366730
    | exact resolve eq366730 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366730
  have eq366868 : y = (M.op x y) := by
    first
    | (have i₁ := eq366815
       have i₂ := eq366735
       grind)
    | exact superpose eq366735 eq366815
    | exact resolve eq366815 eq366735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366815
  have eq367410 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq841 x
       have i₂ := eq366735
       grind)
    | exact superpose eq366735 eq841
    | (have j0 := eq841 x
       grind)
    | exact resolve eq841 eq366735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq841
  have eq367497 : (M.op x y) = (σ x) ∨ (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq367410
       have i₂ := eq364924
       grind)
    | exact superpose eq364924 eq367410
    | exact resolve eq367410 eq364924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364924 eq367410
  have eq367508 : (σ x) ≠ (σ y) := by
    first
    | (have r₁ := eq367497
       have r₂ := eq365123
       grind)
    | exact resolve eq367497 eq365123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367497
  have eq367938 : y = (σ y) := by
    first
    | (have i₁ := eq361471
       have i₂ := eq366868
       grind)
    | exact superpose eq366868 eq361471
    | exact resolve eq361471 eq366868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361471
  have eq367940 : y ≠ (σ x) := by
    first
    | (have i₁ := eq365123
       have i₂ := eq366868
       grind)
    | exact superpose eq366868 eq365123
    | exact resolve eq365123 eq366868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365123
  have eq368701 : (σ x) = (M.op (σ x) y) := by
    first
    | (have i₁ := eq364243
       have i₂ := eq367938
       grind)
    | exact superpose eq367938 eq364243
    | exact resolve eq364243 eq367938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367938
  have eq375721 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op (σ x) (σ y)) X2) ∨ (σ x) = (σ y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4758 x X1 X2 x
       have i₂ := eq366735
       grind)
    | exact superpose eq366735 eq4758
    | exact resolve eq4758 eq366735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4758 eq366735
  have eq375925 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op (σ x) (σ y)) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq375721 X0 X1 X2
       grind)
    | (have r₁ := eq375721 X0 X1 X2
       have r₂ := eq367508
       grind)
    | exact resolve eq375721 eq367508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367508 eq375721
  have eq375939 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op (σ x) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq375925 X0 X1 X2
       have i₂ := eq364243
       grind)
    | exact superpose eq364243 eq375925
    | exact resolve eq375925 eq364243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364243 eq375925
  have eq375943 : ∀ X2 : G, (M.op y x) = (M.op (σ x) X2) := by
    intro X2
    first
    | (have i₁ := eq375939 x x X2
       have i₂ := eq256048 x x
       grind)
    | exact superpose eq256048 eq375939
    | exact resolve eq375939 eq256048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256048 eq375939
  have eq375944 : ∀ X2 : G, (M.op x y) = (M.op (σ x) X2) := by
    intro X2
    first
    | (have i₁ := eq375943 X2
       have i₂ := eq257998
       grind)
    | exact superpose eq257998 eq375943
    | exact resolve eq375943 eq257998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257998 eq375943
  have eq375945 : ∀ X2 : G, y = (M.op (σ x) X2) := by
    intro X2
    first
    | (have i₁ := eq375944 X2
       have i₂ := eq366868
       grind)
    | exact superpose eq366868 eq375944
    | exact resolve eq375944 eq366868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366868 eq375944
  have eq376225 : y = (σ x) := by
    first
    | (have i₁ := eq368701
       have i₂ := eq375945 y
       grind)
    | exact superpose eq375945 eq368701
    | exact resolve eq368701 eq375945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368701 eq375945
  have eq377518 : False := by grind
  exact eq377518

/-- `Equation4393`: `x ◇ (x ◇ x) = (y ◇ z) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation4393 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4393 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4393.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X2) X2) := by
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
  have eq18 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X3 X4) X4) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq8 x X3 X4
       have i₂ := eq8 x X0 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 X3 : G, (M.op X1 (M.op X1 X1)) = (M.op (M.op X0 (M.op X0 X0)) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq8 X1 (M.op x X3) X3
       have i₂ := eq8 X0 x X3
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 x x
       have i₂ := eq8 X1 x x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  clear eq16
  have eq31 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq33 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq36 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq12 X0 (τ X1)
       grind)
    | exact superpose eq12 eq17
    | (have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq17 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  clear eq17
  have eq55 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X2 X3) X3) = (M.op (M.op (M.op X0 X1) X1) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq18 X2 X3 (M.op x X5) X5
       have i₂ := eq18 x X5 X0 X1
       grind)
    | (have i₁ := eq18 X2 X3 (M.op x X5) X5
       have i₂ := eq18 X0 X1 x X5
       grind)
    | exact superpose eq18 eq18
    | exact resolve eq18 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X1 X2) X2) = (M.op (M.op X0 (M.op X0 X0)) X4) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq18 X1 X2 (M.op x X4) X4
       have i₂ := eq8 X0 x X4
       grind)
    | exact superpose eq8 eq18
    | exact resolve eq18 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X1)) = (M.op X2 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 X1 X2
       have i₂ := eq12 X2 X0
       grind)
    | (have i₁ := eq21 X0 X1
       have i₂ := eq12 X0 (M.op X1 X1)
       grind)
    | exact superpose eq12 eq21
    | (have j1 := eq12 X2 X0
       grind)
    | exact resolve eq21 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq31 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq119 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq41
  have eq133 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq119 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq119
    | exact resolve eq119 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq139 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X0 (M.op X0 X0)) X1) = (M.op (M.op X3 (M.op X3 X3)) X4) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq20 X3 x X4
       have i₂ := eq20 X0 x X1
       grind)
    | (have i₁ := eq20 X0 (M.op X0 (M.op X0 X0)) X3
       have i₂ := eq20 X0 X1 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))
       grind)
    | exact superpose eq20 eq20
    | exact resolve eq20 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op X1 (M.op X1 X1)) ∨ (M.op X1 (M.op X1 X1)) = (k (M.op X1 (M.op X1 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq111 (M.op X1 (M.op X1 X1)) X2
       have i₂ := eq20 X1 X0 X2
       grind)
    | (have i₁ := eq111 X1 (M.op X1 X1)
       have i₂ := eq20 X0 X1 x
       grind)
    | exact superpose eq20 eq111
    | (have j0 := eq111 (M.op X1 (M.op X1 X1)) X2
       grind)
    | (have r₁ := eq111 (M.op (M.op X0 (M.op X0 X0)) x) (M.op (M.op (M.op X0 (M.op X0 X0)) x) (M.op (M.op X0 (M.op X0 X0)) x))
       have r₂ := eq20 X0 (M.op (M.op X0 (M.op X0 X0)) x) x
       grind)
    | (have r₁ := eq111 (M.op X1 (M.op X1 X1)) x
       have r₂ := eq20 X1 X1 x
       grind)
    | exact resolve eq111 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq189 : ∀ X1 X2 : G, (M.op X1 (M.op X1 X1)) = (k (M.op X1 (M.op X1 X1)) X2) := by
    intro X1 X2
    first
    | (have j0 := eq188 x X1 X2
       grind)
    | (have r₁ := eq188 x X1 X2
       have r₂ := eq21 x X1
       grind)
    | (have r₁ := eq188 X1 x X2
       have r₂ := eq21 x X1
       grind)
    | exact resolve eq188 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq580 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X1) ≠ (M.op (M.op X2 X3) X3) ∨ (M.op (M.op X2 X3) X3) = (k (M.op (M.op X2 X3) X3) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq111 (M.op (M.op X2 X3) X3) X4
       have i₂ := eq55 X2 X3 X0 X1 X4
       grind)
    | (have i₁ := eq111 (M.op X2 X3) X3
       have i₂ := eq55 X0 X1 X2 X3 x
       grind)
    | exact superpose eq55 eq111
    | (have j0 := eq111 (M.op (M.op X2 X3) X3) X4
       grind)
    | (have r₁ := eq111 (M.op (M.op (M.op X0 X1) X1) x) x
       have r₂ := eq55 X0 X1 (M.op (M.op X0 X1) X1) x x
       grind)
    | (have r₁ := eq111 (M.op (M.op X2 X3) X3) x
       have r₂ := eq55 X2 X3 X2 X3 x
       grind)
    | exact resolve eq111 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq581 : ∀ X2 X3 X4 : G, (M.op (M.op X2 X3) X3) = (k (M.op (M.op X2 X3) X3) X4) := by
    intro X2 X3 X4
    first
    | (have j0 := eq580 x x X2 X3 X4
       grind)
    | (have r₁ := eq580 x x X3 X4 X4
       have r₂ := eq18 x x X3 X4
       grind)
    | (have r₁ := eq580 X3 X4 x x X4
       have r₂ := eq18 x x X3 X4
       grind)
    | exact resolve eq580 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580
  have eq760 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq33 x y
       grind)
    | exact superpose eq33 eq14
    | (have j1 := eq33 x y
       grind)
    | exact resolve eq14 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq817 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq33 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq1831 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq36 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq36
    | exact resolve eq36 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq1935 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1831 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1831
    | (have j0 := eq1831 X0 X1
       grind)
    | exact resolve eq1831 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1831
  have eq2015 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq2572 : ∀ X0 X1 X2 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X2 (M.op X2 X2)) = (M.op X0 (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq26 X0 X1
       have i₂ := eq77 (σ X1) X2 X0
       grind)
    | exact superpose eq77 eq26
    | (have j1 := eq77 (σ X1) X2 X0
       grind)
    | exact resolve eq26 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq77
  have eq6106 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq760
       have i₂ := eq2015 y x
       grind)
    | exact superpose eq2015 eq760
    | (have j1 := eq2015 y x
       grind)
    | (have r₁ := eq760
       have r₂ := eq2015 y x
       grind)
    | exact resolve eq760 eq2015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2015
  have eq6107 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq760
       have i₂ := eq1935 y x
       grind)
    | exact superpose eq1935 eq760
    | (have j1 := eq1935 (σ y) (σ x)
       grind)
    | (have r₁ := eq760
       have r₂ := eq1935 y x
       grind)
    | exact resolve eq760 eq1935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq760 eq1935
  have eq6108 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq6107
  have eq6109 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by grind
  clear eq6106
  have eq6121 : x = (k x (τ (σ y))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq133 x
       have i₂ := eq6108
       grind)
    | exact superpose eq6108 eq133
    | exact resolve eq133 eq6108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6175 : x = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq6121
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq6121
    | exact resolve eq6121 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6121
  have eq6281 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq6175
       grind)
    | exact superpose eq6175 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq6175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6175
  have eq6286 : x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq6281
  have eq6755 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq8 X0 x y
       have i₂ := eq6286
       grind)
    | exact superpose eq6286 eq8
    | exact resolve eq8 eq6286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6757 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op X0 X1) X1) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1 x y
       have i₂ := eq6286
       grind)
    | exact superpose eq6286 eq18
    | exact resolve eq18 eq6286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq6768 : ∀ X0 : G, (M.op x y) = (k (M.op x y) X0) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq581 x y x
       have i₂ := eq6286
       grind)
    | exact superpose eq6286 eq581
    | exact resolve eq581 eq6286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581
  have eq8612 : x = (k x (τ (σ y))) ∨ x = (k x y) := by
    first
    | (have i₁ := eq133 x
       have i₂ := eq6109
       grind)
    | exact superpose eq6109 eq133
    | exact resolve eq133 eq6109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq6109
  have eq8677 : x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq8612
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq8612
    | exact resolve eq8612 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8612
  have eq8678 : x = (k x y) := by grind
  clear eq8677
  have eq10007 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq6755 (σ x)
       have i₂ := eq6108
       grind)
    | exact superpose eq6108 eq6755
    | exact resolve eq6755 eq6108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6108 eq6755
  have eq10139 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq10007
  have eq10736 : ∀ X1 : G, (M.op x y) = (M.op (M.op x y) X1) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    intro X1
    first
    | (have i₁ := eq6757 (M.op x X1) X1
       have i₂ := eq6757 x X1
       grind)
    | exact superpose eq6757 eq6757
    | exact resolve eq6757 eq6757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6757
  have eq10895 : ∀ X1 : G, (M.op x y) = (M.op (M.op x y) X1) ∨ y = (M.op x x) := by
    intro X1
    first
    | (have j0 := eq10736 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10736
  have eq11466 : ∀ X0 : G, x = (k x X0) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq6768 X0
       have i₂ := eq6286
       grind)
    | exact superpose eq6286 eq6768
    | exact resolve eq6768 eq6286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6768
  have eq11503 : ∀ X0 : G, x = (k x X0) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq11466 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11466
  have eq11892 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq817 x
       have i₂ := eq11503 x
       grind)
    | exact superpose eq11503 eq817
    | (have j0 := eq817 x
       grind)
    | exact resolve eq817 eq11503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11503
  have eq11917 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq11892
  have eq18765 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq10139
       grind)
    | exact superpose eq10139 eq14
    | exact resolve eq14 eq10139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10139
  have eq19412 : x ≠ (σ x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq18765
       have i₂ := eq6286
       grind)
    | exact superpose eq6286 eq18765
    | exact resolve eq18765 eq6286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18765
  have eq19415 : x ≠ (σ x) ∨ y = (M.op x x) := by grind
  clear eq19412
  have eq21828 : ∀ X0 : G, x = (M.op x X0) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq10895 x
       have i₂ := eq6286
       grind)
    | exact superpose eq6286 eq10895
    | exact resolve eq10895 eq6286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6286 eq10895
  have eq22060 : ∀ X0 : G, x = (M.op x X0) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq21828 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21828
  have eq23109 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = x ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq21 X0 x
       have i₂ := eq22060 (M.op x x)
       grind)
    | exact superpose eq22060 eq21
    | exact resolve eq21 eq22060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22060
  have eq24232 : x = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq23109 (σ x)
       have i₂ := eq11917
       grind)
    | exact superpose eq11917 eq23109
    | exact resolve eq23109 eq11917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23109
  have eq24452 : x = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq24232
  have eq31833 : x = (σ x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq11917
       have i₂ := eq24452
       grind)
    | exact superpose eq24452 eq11917
    | exact resolve eq11917 eq24452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11917 eq24452
  have eq31960 : x = (σ x) ∨ y = (M.op x x) := by grind
  clear eq31833
  have eq31965 : y = (M.op x x) := by
    first
    | (have r₁ := eq31960
       have r₂ := eq19415
       grind)
    | exact resolve eq31960 eq19415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19415 eq31960
  have eq32748 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq21 X0 x
       have i₂ := eq31965
       grind)
    | exact superpose eq31965 eq21
    | exact resolve eq21 eq31965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq32762 : ∀ X0 : G, (M.op x y) = (k (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq189 x x
       have i₂ := eq31965
       grind)
    | exact superpose eq31965 eq189
    | exact resolve eq189 eq31965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq32788 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq8 X0 x x
       have i₂ := eq31965
       grind)
    | exact superpose eq31965 eq8
    | exact resolve eq8 eq31965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31965
  have eq35653 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op X0 (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq139 X0 X1 x (M.op (M.op x (M.op x x)) (M.op x (M.op x x)))
       have i₂ := eq32748 (M.op x (M.op x x))
       grind)
    | exact superpose eq32748 eq139
    | exact resolve eq139 eq32748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq35663 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq55 x x X0 X1 (M.op (M.op (M.op x x) x) (M.op (M.op x x) x))
       have i₂ := eq32748 (M.op (M.op x x) x)
       grind)
    | exact superpose eq32748 eq55
    | exact resolve eq55 eq32748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq35686 : ∀ X1 : G, (M.op x y) = (M.op (M.op y x) X1) := by
    intro X1
    first
    | (have i₁ := eq35653 x X1
       have i₂ := eq32788 x
       grind)
    | exact superpose eq32788 eq35653
    | exact resolve eq35653 eq32788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35653
  have eq39276 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq817 (M.op x y)
       have i₂ := eq32762 (M.op x y)
       grind)
    | exact superpose eq32762 eq817
    | (have j0 := eq817 (M.op x y)
       grind)
    | exact resolve eq817 eq32762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq817 eq32762
  have eq39316 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq39276
  have eq222174 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) X1) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq56 X0 (σ (M.op x y)) (σ (M.op x y)) X1
       have i₂ := eq39316
       grind)
    | exact superpose eq39316 eq56
    | exact resolve eq56 eq39316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq222292 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op X0 (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq222174 X0 X1
       have i₂ := eq39316
       grind)
    | exact superpose eq39316 eq222174
    | exact resolve eq222174 eq39316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39316 eq222174
  have eq222427 : ∀ X1 : G, (σ (M.op x y)) = (M.op (M.op y x) X1) := by
    intro X1
    first
    | (have i₁ := eq222292 x X1
       have i₂ := eq32788 x
       grind)
    | exact superpose eq32788 eq222292
    | exact resolve eq222292 eq32788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32788 eq222292
  have eq222527 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq222427 x
       have i₂ := eq35686 x
       grind)
    | exact superpose eq35686 eq222427
    | exact resolve eq222427 eq35686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35686 eq222427
  have eq249003 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) ≠ (σ (M.op x y)) ∨ (k (τ (σ x)) y) = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq2572 (σ x) y X0
       grind)
    | exact superpose eq2572 eq14
    | (have j1 := eq2572 (σ x) y x
       grind)
    | exact resolve eq14 eq2572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2572
  have eq249009 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op x y) ∨ (k (τ (σ x)) y) = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq249003 X0
       have i₂ := eq222527
       grind)
    | exact superpose eq222527 eq249003
    | exact resolve eq249003 eq222527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249003
  have eq249063 : (k (τ (σ x)) y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq249009 x
       have r₂ := eq32748 x
       grind)
    | exact resolve eq249009 eq32748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32748 eq249009
  have eq249091 : (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq249063
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq249063
    | exact resolve eq249063 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249063
  have eq249097 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq249091
       have i₂ := eq8678
       grind)
    | exact superpose eq8678 eq249091
    | exact resolve eq249091 eq8678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8678 eq249091
  have eq249150 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 (M.op (σ x) (σ y))
       have i₂ := eq249097
       grind)
    | exact superpose eq249097 eq10
    | exact resolve eq10 eq249097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249097
  have eq249594 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq249150
       grind)
    | exact superpose eq249150 eq14
    | exact resolve eq14 eq249150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq249741 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq35663 (σ x) (σ y)
       have i₂ := eq249150
       grind)
    | exact superpose eq249150 eq35663
    | exact resolve eq35663 eq249150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35663
  have eq249745 : (M.op x y) = (σ x) := by
    first
    | (have i₁ := eq249741
       have i₂ := eq249150
       grind)
    | exact superpose eq249150 eq249741
    | exact resolve eq249741 eq249150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249150 eq249741
  have eq249868 : (M.op x y) ≠ (σ x) := by
    first
    | (have i₁ := eq249594
       have i₂ := eq222527
       grind)
    | exact superpose eq222527 eq249594
    | exact resolve eq249594 eq222527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222527 eq249594
  have eq249930 : False := by grind
  exact eq249930

/-- `Equation4397`: `x ◇ (x ◇ y) = (x ◇ x) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxy_y_x_pyx_Equation4397 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4397 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4397.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X0) X2) := by
    intro X0 X1 X2
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
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
  have eq17 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X3) = (M.op X0 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq8 X0 (M.op X0 x) X3
       have i₂ := eq8 X0 x X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X0) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq8 X0 x X3
       have i₂ := eq8 X0 x X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X0) X2)) = (M.op (M.op X0 (M.op X0 X1)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op X0 X0) X2 X3
       have i₂ := eq8 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 X2)) := by
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
  have eq23 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X2)) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X2 (M.op (M.op X0 X0) x)
       have i₂ := eq8 (M.op X0 X0) x X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq32 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq12 (τ X1) X0
       grind)
    | exact superpose eq12 eq15
    | (have j1 := eq12 (τ X1) X0
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
  have eq112 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq39 X1 X0
       have i₂ := eq12 (σ X1) X0
       grind)
    | exact superpose eq12 eq39
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq39 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq161 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X2) ≠ (M.op (M.op X0 X0) X1) ∨ (k X0 (M.op (M.op X0 X0) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X0 (M.op (M.op X0 X0) X2)
       have i₂ := eq17 X0 X2 X1
       grind)
    | exact superpose eq17 eq11
    | (have j0 := eq11 X0 (M.op (M.op X0 X0) X2)
       grind)
    | (have r₁ := eq11 (M.op X0 X0) (M.op X0 (M.op (M.op X0 X0) X1))
       have r₂ := eq17 X0 X1 (M.op X0 (M.op (M.op X0 X0) X1))
       grind)
    | (have r₁ := eq11 X0 (M.op (M.op X0 X0) x)
       have r₂ := eq17 X0 x x
       grind)
    | exact resolve eq11 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq165 : ∀ X0 X2 : G, (k X0 (M.op (M.op X0 X0) X2)) = X0 := by
    intro X0 X2
    first
    | (have j0 := eq161 X0 x X2
       grind)
    | (have r₁ := eq161 X0 x x
       have r₂ := eq19 X0 x x
       grind)
    | (have r₁ := eq161 X0 x x
       have r₂ := eq19 X0 x x
       grind)
    | exact resolve eq161 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161
  have eq170 : ∀ X0 X1 : G, (k X0 (M.op X0 (M.op (M.op X0 X0) X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq165 X0 x
       have i₂ := eq17 X0 X1 x
       grind)
    | exact superpose eq17 eq165
    | exact resolve eq165 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq165
  have eq210 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X2)) = (M.op (M.op (M.op X0 X0) X1) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq23 X0 X3 X2
       have i₂ := eq19 X0 (M.op X0 X0) X1
       grind)
    | (have i₁ := eq23 X0 X3 X2
       have i₂ := eq19 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq19 eq23
    | exact resolve eq23 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq211 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X2)) = (M.op (M.op X0 (M.op X0 X1)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq23 X0 X3 X2
       have i₂ := eq8 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq8 eq23
    | exact resolve eq23 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq426 : ∀ X0 X1 X2 : G, (k X0 (M.op X0 (M.op (M.op X0 (M.op X0 X1)) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq170 X0 (M.op (M.op X0 X0) x)
       have i₂ := eq21 X0 X1 x X2
       grind)
    | exact superpose eq21 eq170
    | exact resolve eq170 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq170
  have eq513 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 X1
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq31
    | (have j0 := eq31 X0 X1
       have j1 := eq31 X0 X1
       grind)
    | exact resolve eq31 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq542 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq31 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq976 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X0 X4)) = (M.op (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) X2) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq210 X0 X1 X4 (M.op (M.op (M.op X0 X0) X1) x)
       have i₂ := eq210 (M.op (M.op X0 X0) X1) X2 x X3
       grind)
    | exact superpose eq210 eq210
    | exact resolve eq210 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1181 : ∀ X0 X1 X2 X3 X5 : G, (M.op X0 (M.op X0 X3)) = (M.op (M.op (M.op (M.op X0 X0) X1) X2) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq211 X0 x X3 X5
       have i₂ := eq210 X0 X1 x X2
       grind)
    | exact superpose eq210 eq211
    | exact resolve eq211 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq2096 : ∀ X0 X1 X2 X4 : G, (k X0 (M.op X0 (M.op (M.op (M.op X0 (M.op X0 X1)) X2) X4))) = X0 := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq426 X0 x X4
       have i₂ := eq211 X0 X1 x X2
       grind)
    | exact superpose eq211 eq426
    | exact resolve eq426 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426
  have eq5345 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq32 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq32
    | exact resolve eq32 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq5403 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5345 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq5345
    | (have j0 := eq5345 X0 X1
       grind)
    | exact resolve eq5345 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5345
  have eq46984 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq513 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq513
    | exact resolve eq513 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513
  have eq47190 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq46984 X0 X1
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq46984
    | (have j0 := eq46984 X0 X1
       grind)
    | exact resolve eq46984 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46984
  have eq47193 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq47190 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq47190
    | (have j0 := eq47190 X0 X1
       grind)
    | exact resolve eq47190 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47190
  have eq47195 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq47193 X0 X1
       have j1 := eq11 X0 (σ X1)
       grind)
    | (have r₁ := eq47193 X0 X1
       have r₂ := eq11 X0 (σ X1)
       grind)
    | exact resolve eq47193 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47193
  have eq47211 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq47195 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq47195
    | exact resolve eq47195 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47240 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq39 X0 (σ X1)
       have i₂ := eq47195 (σ X0) X1
       grind)
    | exact superpose eq47195 eq39
    | (have j1 := eq47195 (σ X0) X1
       grind)
    | exact resolve eq39 eq47195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq47195
  have eq47314 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq47240 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq47240
    | (have j0 := eq47240 X0 X1
       grind)
    | exact resolve eq47240 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47240
  have eq47337 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq47314 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq47314
    | (have j0 := eq47314 X0 X1
       grind)
    | exact resolve eq47314 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47314
  have eq47345 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq47337 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq47337
    | (have j0 := eq47337 X0 X1
       grind)
    | exact resolve eq47337 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47337
  have eq47694 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ X1)) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq47211 X1 (τ X0)
       grind)
    | exact superpose eq47211 eq15
    | (have j1 := eq47211 X1 (τ X0)
       grind)
    | exact resolve eq15 eq47211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq47719 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq47694 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq47694
    | (have j0 := eq47694 X0 X1
       grind)
    | exact resolve eq47694 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47694
  have eq52325 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq47345 x y
       grind)
    | exact superpose eq47345 eq14
    | (have j1 := eq47345 x y
       grind)
    | exact resolve eq14 eq47345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47345
  have eq52666 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq52325
       have i₂ := eq47211 y x
       grind)
    | exact superpose eq47211 eq52325
    | (have j1 := eq47211 y x
       grind)
    | exact resolve eq52325 eq47211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47211 eq52325
  have eq52675 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) := by grind
  clear eq52666
  have eq52676 : x = (k x y) := by grind
  clear eq52675
  have eq53396 : x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq52676
       grind)
    | exact superpose eq52676 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq52676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53399 : (σ x) = (σ (M.op y x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq5403 x y
       have i₂ := eq52676
       grind)
    | exact superpose eq52676 eq5403
    | (have j0 := eq5403 x y
       grind)
    | exact resolve eq5403 eq52676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5403
  have eq56392 : ∀ X0 X1 : G, (M.op (M.op y x) X1) = (M.op y (M.op y X0)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq211 y x X0 X1
       have i₂ := eq53396
       grind)
    | exact superpose eq53396 eq211
    | exact resolve eq211 eq53396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq70780 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq47719 X0 X1
       grind)
    | exact superpose eq47719 eq16
    | (have j1 := eq47719 X0 X1
       grind)
    | exact resolve eq16 eq47719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq47719
  have eq141628 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq70780 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq70780
    | (have j0 := eq70780 (σ X0) X1
       grind)
    | exact resolve eq70780 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70780
  have eq141660 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq141628 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq141628
    | (have j0 := eq141628 X0 X1
       grind)
    | exact resolve eq141628 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141628
  have eq141663 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq141660 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq141660
    | (have j0 := eq141660 X0 X1
       grind)
    | exact resolve eq141660 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141660
  have eq145919 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq542 X0
       have i₂ := eq141663 X0 X0
       grind)
    | exact superpose eq141663 eq542
    | (have j0 := eq542 X0
       have j1 := eq141663 X0 X0
       grind)
    | (have r₁ := eq542 x
       have r₂ := eq141663 x x
       grind)
    | exact resolve eq542 eq141663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141663
  have eq145949 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq145919 X0
       have j1 := eq542 X0
       grind)
    | (have r₁ := eq145919 X0
       have r₂ := eq542 X0
       grind)
    | exact resolve eq145919 eq542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145919
  have eq163661 : ∀ X0 : G, (M.op y x) = (M.op x X0) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq56392 x x
       have i₂ := eq53396
       grind)
    | exact superpose eq53396 eq56392
    | exact resolve eq56392 eq53396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56392
  have eq163947 : ∀ X0 : G, (M.op y x) = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq163661 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163661
  have eq164151 : ∀ X0 : G, x = (M.op x X0) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq53396
       have i₂ := eq163947 X0
       grind)
    | exact superpose eq163947 eq53396
    | exact resolve eq53396 eq163947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53396
  have eq164152 : ∀ X0 : G, (σ x) = (σ (M.op x X0)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq53399
       have i₂ := eq163947 X0
       grind)
    | exact superpose eq163947 eq53399
    | exact resolve eq53399 eq163947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53399 eq163947
  have eq164569 : ∀ X0 : G, (σ x) = (σ (M.op x X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq164152 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164152
  have eq164570 : ∀ X0 : G, x = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq164151 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164151
  have eq165419 : x = (k x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2096 x x x x
       have i₂ := eq164570 (M.op (M.op (M.op x (M.op x x)) x) x)
       grind)
    | exact superpose eq164570 eq2096
    | exact resolve eq2096 eq164570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2096 eq164570
  have eq166521 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq542 x
       have i₂ := eq165419
       grind)
    | exact superpose eq165419 eq542
    | (have j0 := eq542 x
       grind)
    | exact resolve eq542 eq165419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542 eq165419
  have eq166540 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq166521
  have eq170999 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (σ x) X1 x
       have i₂ := eq166540
       grind)
    | exact superpose eq166540 eq19
    | exact resolve eq19 eq166540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq188369 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq166540
       have i₂ := eq170999 (σ x) X0
       grind)
    | (have i₁ := eq166540
       have i₂ := eq170999 X0 (σ x)
       grind)
    | exact superpose eq170999 eq166540
    | exact resolve eq166540 eq170999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166540 eq170999
  have eq188500 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq188369 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188369
  have eq188604 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq188500 (σ y)
       grind)
    | exact superpose eq188500 eq14
    | exact resolve eq14 eq188500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188500
  have eq188859 : y = (M.op x y) := by
    first
    | (have r₁ := eq188604
       have r₂ := eq164569 y
       grind)
    | exact resolve eq188604 eq164569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164569 eq188604
  have eq188901 : ∀ X0 : G, (M.op x y) = (M.op x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq22 x X0 y
       have i₂ := eq188859
       grind)
    | exact superpose eq188859 eq22
    | exact resolve eq22 eq188859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq189101 : ∀ X0 : G, y = (M.op x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq188901 X0
       have i₂ := eq188859
       grind)
    | exact superpose eq188859 eq188901
    | exact resolve eq188901 eq188859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188901
  have eq192007 : ∀ X1 X2 X3 : G, y = (M.op (M.op (M.op (M.op (M.op x x) X1) (M.op (M.op x x) X1)) X2) X3) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq976 x X1 X2 X3 x
       have i₂ := eq189101 x
       grind)
    | exact superpose eq189101 eq976
    | exact resolve eq976 eq189101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq976
  have eq192023 : ∀ X1 X2 X3 : G, y = (M.op (M.op (M.op (M.op x x) X1) X2) X3) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq1181 x X1 X2 x X3
       have i₂ := eq189101 x
       grind)
    | exact superpose eq189101 eq1181
    | exact resolve eq1181 eq189101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1181 eq189101
  have eq192384 : ∀ X3 : G, y = (M.op y X3) := by
    intro X3
    first
    | (have i₁ := eq192007 x x X3
       have i₂ := eq192023 x (M.op (M.op x x) x) x
       grind)
    | exact superpose eq192023 eq192007
    | exact resolve eq192007 eq192023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192007 eq192023
  have eq192848 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq145949 y
       have i₂ := eq192384 y
       grind)
    | exact superpose eq192384 eq145949
    | (have j0 := eq145949 y
       grind)
    | exact resolve eq145949 eq192384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145949
  have eq193310 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq192848
  have eq195862 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op (σ y) (σ y)) X0) := by
    intro X0
    first
    | (have i₁ := eq23 (σ y) x (σ y)
       have i₂ := eq193310
       grind)
    | exact superpose eq193310 eq23
    | exact resolve eq23 eq193310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq195970 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq195862 X0
       have i₂ := eq193310
       grind)
    | exact superpose eq193310 eq195862
    | exact resolve eq195862 eq193310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193310 eq195862
  have eq196668 : ∀ X0 : G, (τ (σ y)) = (k X0 (τ (σ y))) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq112 (σ y) X0
       have i₂ := eq195970 (σ X0)
       grind)
    | exact superpose eq195970 eq112
    | (have j0 := eq112 (σ y) X0
       grind)
    | exact resolve eq112 eq195970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq196686 : ∀ X0 : G, (σ y) = (M.op (σ X0) (σ y)) ∨ y = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq196668 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq196668
    | (have j0 := eq196668 X0
       grind)
    | exact resolve eq196668 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196668
  have eq319599 : (σ (M.op x y)) ≠ (σ y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq196686 x
       grind)
    | exact superpose eq196686 eq14
    | (have j1 := eq196686 x
       grind)
    | exact resolve eq14 eq196686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196686
  have eq319684 : (σ y) ≠ (σ y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq319599
       have i₂ := eq188859
       grind)
    | exact superpose eq188859 eq319599
    | exact resolve eq319599 eq188859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188859 eq319599
  have eq319685 : y = (k x y) := by grind
  clear eq319684
  have eq319686 : x = y := by
    first
    | (have i₁ := eq319685
       have i₂ := eq52676
       grind)
    | exact superpose eq52676 eq319685
    | exact resolve eq319685 eq52676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52676 eq319685
  have eq319689 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq319686
       grind)
    | exact superpose eq319686 eq14
    | exact resolve eq14 eq319686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq319862 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq192384 x
       have i₂ := eq319686
       grind)
    | exact superpose eq319686 eq192384
    | exact resolve eq192384 eq319686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192384
  have eq319932 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq195970 X0
       have i₂ := eq319686
       grind)
    | exact superpose eq319686 eq195970
    | exact resolve eq195970 eq319686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195970 eq319686
  have eq320098 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq319689
       have i₂ := eq319862 x
       grind)
    | exact superpose eq319862 eq319689
    | exact resolve eq319689 eq319862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319689 eq319862
  have eq320179 : False := by grind
  exact eq320179

/-- `Equation4400`: `x ◇ (x ◇ y) = (x ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxy_y_x_pxy_Equation4400 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4400 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4400.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X1) X2) := by
    intro X0 X1 X2
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
  have eq17 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X0 X1 X3
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op X0 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X0 (M.op X0 X1) X2
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 X3 : G, (M.op (M.op X0 (M.op X0 X1)) X3) = (M.op (M.op X0 X1) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq8 (M.op X0 X1) x x
       have i₂ := eq8 X0 X1 x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X0 X1 (M.op (M.op X0 X1) X2)
       have i₂ := eq8 (M.op X0 X1) X2 X3
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 (M.op X0 X1)) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq20 X0 X1 X3
       have i₂ := eq8 X0 X1 (M.op X0 (M.op X0 X1))
       grind)
    | exact superpose eq8 eq20
    | exact resolve eq20 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq26 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (k (τ X0) X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq13
    | exact resolve eq13 eq15
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
  have eq31 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
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
  clear eq15
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
  have eq60 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op (M.op X0 X1) X3) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 (M.op X0 X1) X3 X4
       have i₂ := eq17 X0 X1 (M.op (M.op X0 X1) X3) X2
       grind)
    | (have i₁ := eq8 (M.op X0 X1) X3 X4
       have i₂ := eq17 X0 X1 X2 (M.op (M.op X0 X1) X3)
       grind)
    | exact superpose eq17 eq8
    | exact resolve eq8 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq228 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) ≠ (M.op (M.op (M.op X0 X1) X2) X3) ∨ (k X0 (M.op (M.op X0 X1) X2)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq11 X0 (M.op (M.op X0 X1) X2)
       have i₂ := eq19 X0 X1 X2 X3
       grind)
    | exact superpose eq19 eq11
    | (have j0 := eq11 X0 (M.op (M.op X0 X1) X2)
       grind)
    | (have r₁ := eq11 (M.op (M.op X0 X1) X2) (M.op X0 (M.op (M.op X0 X1) X2))
       have r₂ := eq19 X0 X1 X2 (M.op X0 (M.op (M.op X0 X1) X2))
       grind)
    | exact resolve eq11 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq236 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op X0 X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq228 X0 X1 X2 x
       grind)
    | (have r₁ := eq228 X0 X1 x x
       have r₂ := eq60 X0 X1 x x x
       grind)
    | exact resolve eq228 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq277 : ∀ X0 X1 : G, (k X0 (M.op X0 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq236 X0 (M.op X0 X1) x
       have i₂ := eq24 X0 X1 x
       grind)
    | exact superpose eq24 eq236
    | exact resolve eq236 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq279 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq236 (M.op X0 X1) x x
       have i₂ := eq21 X0 X1 x x
       grind)
    | exact superpose eq21 eq236
    | exact resolve eq236 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq236
  have eq323 : ∀ X0 X1 X2 X3 : G, (k X0 (M.op X0 (M.op (M.op (M.op X0 X1) X2) X3))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq277 X0 (M.op (M.op X0 X1) X2)
       have i₂ := eq19 X0 X1 X2 X3
       grind)
    | exact superpose eq19 eq277
    | exact resolve eq277 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq339 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (M.op (σ X0) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 (M.op (σ X0) (M.op (σ X0) X1))
       have i₂ := eq277 (σ X0) X1
       grind)
    | exact superpose eq277 eq38
    | exact resolve eq38 eq277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq343 : ∀ X0 X1 : G, (k X0 (τ (M.op (σ X0) (M.op (σ X0) X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq339 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq339
    | exact resolve eq339 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339
  have eq422 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
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
  have eq425 : ∀ X0 X1 X2 X3 : G, (M.op (σ (k X0 X1)) X2) = (M.op (σ (k X0 X1)) X3) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq17 (σ X0) (σ X1) X2 X3
       have i₂ := eq30 X0 X1
       grind)
    | exact superpose eq30 eq17
    | (have j1 := eq30 X0 X1
       grind)
    | exact resolve eq17 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq434 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq30 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq553 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op X0 (M.op (M.op X0 X1) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 X0 X1 X3 x
       have i₂ := eq60 X0 X1 X2 X3 x
       grind)
    | exact superpose eq60 eq19
    | exact resolve eq19 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq60
  have eq821 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (M.op X0 (σ X1))) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq26 X0 X1 X2
       have i₂ := eq12 X0 (σ X1)
       grind)
    | exact superpose eq12 eq26
    | (have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq26 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq2580 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq434 (τ X0) (τ X1)
       have i₂ := eq61 X1 X0
       grind)
    | exact superpose eq61 eq434
    | (have j0 := eq434 (τ X0) (τ X1)
       grind)
    | exact resolve eq434 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2587 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2580 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq2580
    | (have j0 := eq2580 X0 X1
       grind)
    | exact resolve eq2580 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2580
  have eq2592 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2587 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq2587
    | (have j0 := eq2587 X0 X1
       grind)
    | exact resolve eq2587 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2587
  have eq2596 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2592 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2592
    | (have j0 := eq2592 X0 X1
       grind)
    | exact resolve eq2592 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2592
  have eq2597 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2596 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2596
    | (have j0 := eq2596 X0 X1
       grind)
    | exact resolve eq2596 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2596
  have eq2625 : ∀ X0 X1 X2 : G, (σ (M.op (M.op (τ X0) X1) X2)) = (k X0 (σ (M.op (τ X0) X1))) ∨ (M.op (τ X0) X1) = (M.op (M.op (τ X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31 X0 (M.op (τ X0) X1)
       have i₂ := eq8 (τ X0) X1 X2
       grind)
    | exact superpose eq8 eq31
    | exact resolve eq31 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq4565 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq422
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq422
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq422 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4566 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq4565
  have eq4572 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq8 (σ x) (σ y) x
       have i₂ := eq4566
       grind)
    | exact superpose eq4566 eq8
    | exact resolve eq8 eq4566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4573 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 (σ x) (σ y)
       have i₂ := eq4566
       grind)
    | exact superpose eq4566 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | (have r₁ := eq11 (σ x) (σ y)
       have r₂ := eq4566
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq4566
       grind)
    | exact resolve eq11 eq4566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4566
  have eq4600 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq4573
  have eq4607 : (σ x) = (σ (k x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4600
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq4600
    | exact resolve eq4600 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4600
  have eq4832 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4607
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq4607
    | (have j1 := eq12 x y
       grind)
    | exact resolve eq4607 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4835 : (k x y) = (τ (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq9 (k x y)
       have i₂ := eq4607
       grind)
    | exact superpose eq4607 eq9
    | exact resolve eq9 eq4607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4607
  have eq4856 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq4832
  have eq4870 : x = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4835
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq4835
    | exact resolve eq4835 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4835
  have eq4871 : x = (k x y) := by
    first
    | (have j1 := eq11 x y
       grind)
    | (have r₁ := eq4870
       have r₂ := eq11 x y
       grind)
    | exact resolve eq4870 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4870
  have eq5416 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq422
       have i₂ := eq4871
       grind)
    | exact superpose eq4871 eq422
    | exact resolve eq422 eq4871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422
  have eq5419 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq4871
       grind)
    | exact superpose eq4871 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq4871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6191 : ∀ X0 : G, (M.op x y) = (M.op y X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq8 x y x
       have i₂ := eq5419
       grind)
    | exact superpose eq5419 eq8
    | exact resolve eq8 eq5419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6193 : ∀ X0 X1 : G, (M.op y X0) = (M.op y X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq17 x y x x
       have i₂ := eq5419
       grind)
    | exact superpose eq5419 eq17
    | exact resolve eq17 eq5419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6215 : y = (k y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq279 x y
       have i₂ := eq5419
       grind)
    | exact superpose eq5419 eq279
    | exact resolve eq279 eq5419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279
  have eq6222 : ∀ X0 X1 : G, (M.op y X0) = (M.op x (M.op y X1)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq553 x y x x
       have i₂ := eq5419
       grind)
    | exact superpose eq5419 eq553
    | exact resolve eq553 eq5419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553
  have eq6224 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq8135 : ∀ X0 X1 X2 X3 : G, (M.op (σ (τ (k X0 X1))) X2) = (M.op (σ (τ (k X0 X1))) X3) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq425 (τ X1) (τ X0) X2 X3
       have i₂ := eq61 X0 X1
       grind)
    | exact superpose eq61 eq425
    | (have j0 := eq425 (τ X0) (τ X1) X2 X3
       grind)
    | exact resolve eq425 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq8138 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq425 x y x x
       have i₂ := eq4871
       grind)
    | exact superpose eq4871 eq425
    | (have j0 := eq425 x y x x
       grind)
    | exact resolve eq425 eq4871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425
  have eq8302 : ∀ X0 X1 X2 X3 : G, (M.op (k X0 X1) X2) = (M.op (k X0 X1) X3) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8135 X0 X1 X2 X3
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq8135
    | (have j0 := eq8135 X0 X1 X2 X3
       grind)
    | exact resolve eq8135 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8135
  have eq8308 : ∀ X0 X1 X2 X3 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (M.op (k X0 X1) X2) = (M.op (k X0 X1) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8302 X0 X0 X2 X3
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8302
    | (have j0 := eq8302 X0 X1 X2 X3
       grind)
    | exact resolve eq8302 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8302
  have eq8309 : ∀ X0 X1 X2 X3 : G, (M.op (k X0 X1) X2) = (M.op (k X0 X1) X3) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8308 X0 X1 X2 X3
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8308
    | (have j0 := eq8308 X0 X1 X2 X3
       grind)
    | exact resolve eq8308 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8308
  have eq8753 : y = (k y y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6215
       have i₂ := eq5419
       grind)
    | exact superpose eq5419 eq6215
    | exact resolve eq6215 eq5419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5419 eq6215
  have eq8760 : y = (k y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq8753
       have r₂ := eq6224
       grind)
    | exact resolve eq8753 eq6224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6224 eq8753
  have eq9608 : y = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 y y
       have i₂ := eq8760
       grind)
    | exact superpose eq8760 eq12
    | (have j0 := eq12 y y
       grind)
    | exact resolve eq12 eq8760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8760
  have eq9609 : y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq9608
  have eq9817 : ∀ X0 : G, y = (M.op y X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq6193 y X0
       have i₂ := eq9609
       grind)
    | exact superpose eq9609 eq6193
    | exact resolve eq6193 eq9609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6193 eq9609
  have eq9862 : ∀ X0 : G, y = (M.op y X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq9817 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9817
  have eq12680 : ∀ X0 : G, y = (M.op x (M.op y X0)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9862 x
       have i₂ := eq6222 x X0
       grind)
    | exact superpose eq6222 eq9862
    | exact resolve eq9862 eq6222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6222 eq9862
  have eq12787 : ∀ X0 : G, y = (M.op x (M.op y X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq12680 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12680
  have eq13029 : y = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12787 x
       have i₂ := eq6191 x
       grind)
    | exact superpose eq6191 eq12787
    | exact resolve eq12787 eq6191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6191 eq12787
  have eq13086 : y = (M.op x (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq13029
  have eq33480 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq4572 X0
       grind)
    | exact superpose eq4572 eq14
    | exact resolve eq14 eq4572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36950 : ∀ X0 : G, (σ x) ≠ (M.op (σ y) X0) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq33480 X0
       have i₂ := eq4856
       grind)
    | exact superpose eq4856 eq33480
    | exact resolve eq33480 eq4856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4856 eq33480
  have eq36984 : ∀ X0 : G, (σ x) ≠ (M.op (σ y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq36950 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36950
  have eq37409 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq36984 x
       have i₂ := eq4572 x
       grind)
    | exact superpose eq4572 eq36984
    | exact resolve eq36984 eq4572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4572 eq36984
  have eq37441 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq37409
  have eq56808 : ∀ X0 X1 X2 : G, (τ (σ (k X0 (k (τ X1) X2)))) = (k X0 (τ (M.op X1 (σ X2)))) ∨ (σ X2) = (M.op X1 (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq38 X0 (M.op X1 (σ X2))
       have i₂ := eq821 X1 X2 X0
       grind)
    | exact superpose eq821 eq38
    | (have j1 := eq821 X1 X2 X2
       grind)
    | exact resolve eq38 eq821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821
  have eq56847 : ∀ X0 X1 X2 : G, (k X0 (k (τ X1) X2)) = (k X0 (τ (M.op X1 (σ X2)))) ∨ (σ X2) = (M.op X1 (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56808 X0 X1 X2
       have i₂ := eq9 (k X0 (k (τ X1) X2))
       grind)
    | exact superpose eq9 eq56808
    | (have j0 := eq56808 X0 X1 X2
       grind)
    | exact resolve eq56808 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56808
  have eq113921 : ∀ X0 X1 X2 : G, (τ (σ (M.op (M.op (τ (σ X0)) X1) X2))) = (k X0 (τ (σ (M.op (τ (σ X0)) X1)))) ∨ (M.op (τ (σ X0)) X1) = (M.op (M.op (τ (σ X0)) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq38 X0 (σ (M.op (τ (σ X0)) X1))
       have i₂ := eq2625 (σ X0) X1 X2
       grind)
    | exact superpose eq2625 eq38
    | (have j1 := eq2625 (σ X0) X1 X2
       grind)
    | exact resolve eq38 eq2625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq2625
  have eq114041 : ∀ X0 X1 X2 : G, (τ (σ (M.op (M.op (τ (σ X0)) X1) X2))) = (k X0 (M.op (τ (σ X0)) X1)) ∨ (M.op (τ (σ X0)) X1) = (M.op (M.op (τ (σ X0)) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq113921 X0 X1 X2
       have i₂ := eq9 (M.op (τ (σ X0)) X1)
       grind)
    | exact superpose eq9 eq113921
    | (have j0 := eq113921 X0 X1 X2
       grind)
    | exact resolve eq113921 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113921
  have eq114146 : ∀ X0 X1 X2 : G, (k X0 (M.op X0 X1)) = (τ (σ (M.op (M.op X0 X1) X2))) ∨ (M.op (τ (σ X0)) X1) = (M.op (M.op (τ (σ X0)) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq114041 X0 X1 X2
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq114041
    | (have j0 := eq114041 X0 X1 X2
       grind)
    | exact resolve eq114041 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114041
  have eq114201 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (k X0 (M.op X0 X1)) ∨ (M.op (τ (σ X0)) X1) = (M.op (M.op (τ (σ X0)) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq114146 X0 X1 X2
       have i₂ := eq9 (M.op (M.op X0 X1) X2)
       grind)
    | exact superpose eq9 eq114146
    | (have j0 := eq114146 X0 X1 X2
       grind)
    | exact resolve eq114146 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114146
  have eq114219 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (k X0 (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq114201 X0 X1 X2
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq114201
    | (have j0 := eq114201 X0 X1 X2
       grind)
    | exact resolve eq114201 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114201
  have eq138455 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq8309 x y x x
       have i₂ := eq4871
       grind)
    | exact superpose eq4871 eq8309
    | (have j0 := eq8309 x y x x
       grind)
    | exact resolve eq8309 eq4871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8309
  have eq140154 : ∀ X0 : G, y = (M.op x (M.op x X0)) ∨ x = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq13086
       have i₂ := eq138455 y x
       grind)
    | (have i₁ := eq13086
       have i₂ := eq138455 X0 y
       grind)
    | exact superpose eq138455 eq13086
    | exact resolve eq13086 eq138455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13086
  have eq140458 : ∀ X0 : G, y ≠ (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    grind
  clear eq138455
  have eq140549 : ∀ X0 : G, x = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq140154 X0
       grind)
    | (have r₁ := eq140154 X0
       have r₂ := eq140458 (M.op x X0)
       grind)
    | (have r₁ := eq140154 X0
       have r₂ := eq140458 y
       grind)
    | exact resolve eq140154 eq140458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140154 eq140458
  have eq143729 : x = (k x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq323 x x x x
       have i₂ := eq140549 (M.op (M.op (M.op x x) x) x)
       grind)
    | exact superpose eq140549 eq323
    | exact resolve eq323 eq140549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323 eq140549
  have eq149782 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq434 x x
       have i₂ := eq143729
       grind)
    | exact superpose eq143729 eq434
    | (have j0 := eq434 x x
       grind)
    | exact resolve eq434 eq143729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434 eq143729
  have eq149803 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq149782
  have eq214574 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq17 (σ x) (σ x) x x
       have i₂ := eq149803
       grind)
    | exact superpose eq149803 eq17
    | exact resolve eq17 eq149803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq320387 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) X0) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq37441
       have i₂ := eq214574 (σ y) X0
       grind)
    | (have i₁ := eq37441
       have i₂ := eq214574 X0 (σ y)
       grind)
    | exact superpose eq214574 eq37441
    | exact resolve eq37441 eq214574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37441
  have eq320391 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq149803
       have i₂ := eq214574 (σ x) X0
       grind)
    | (have i₁ := eq149803
       have i₂ := eq214574 X0 (σ x)
       grind)
    | exact superpose eq214574 eq149803
    | exact resolve eq149803 eq214574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149803 eq214574
  have eq320531 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq320391 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320391
  have eq320534 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq320387 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320387
  have eq320582 : y = (M.op x y) := by
    first
    | (have r₁ := eq320534 x
       have r₂ := eq320531 x
       grind)
    | exact resolve eq320534 eq320531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320531 eq320534
  have eq828091 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) X0) = (M.op (σ x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14
       have i₂ := eq8138 X0 X1
       grind)
    | exact superpose eq8138 eq14
    | (have j1 := eq8138 X0 X1
       grind)
    | exact resolve eq14 eq8138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8138
  have eq828228 : ∀ X0 X1 : G, (σ y) ≠ (σ y) ∨ (M.op (σ x) X0) = (M.op (σ x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq828091 X0 X1
       have i₂ := eq320582
       grind)
    | exact superpose eq320582 eq828091
    | (have j0 := eq828091 X0 X1
       grind)
    | exact resolve eq828091 eq320582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828091
  have eq828229 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) := by
    intro X0 X1
    first
    | (have j0 := eq828228 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828228
  have eq829161 : ∀ X0 : G, x = (k x (τ (M.op (σ x) X0))) := by
    intro X0
    first
    | (have i₁ := eq343 x x
       have i₂ := eq828229 (M.op (σ x) x) X0
       grind)
    | (have i₁ := eq343 x x
       have i₂ := eq828229 X0 (M.op (σ x) x)
       grind)
    | exact superpose eq828229 eq343
    | exact resolve eq343 eq828229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343
  have eq829189 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq828229 (σ y) X0
       grind)
    | (have i₁ := eq14
       have i₂ := eq828229 X0 (σ y)
       grind)
    | exact superpose eq828229 eq14
    | exact resolve eq14 eq828229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828229
  have eq829625 : ∀ X0 : G, (σ y) ≠ (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq829189 X0
       have i₂ := eq320582
       grind)
    | exact superpose eq320582 eq829189
    | exact resolve eq829189 eq320582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320582 eq829189
  have eq830280 : ∀ X0 : G, x = (k x (k (τ (σ x)) X0)) ∨ (σ X0) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq56847 x (σ x) X0
       have i₂ := eq829161 (σ X0)
       grind)
    | exact superpose eq829161 eq56847
    | (have j0 := eq56847 X0 (σ x) X0
       grind)
    | exact resolve eq56847 eq829161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56847 eq829161
  have eq830363 : ∀ X0 : G, x = (k x (k x X0)) ∨ (σ X0) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq830280 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq830280
    | (have j0 := eq830280 X0
       grind)
    | exact resolve eq830280 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830280
  have eq843011 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq830363 y
       have i₂ := eq4871
       grind)
    | exact superpose eq4871 eq830363
    | (have j0 := eq830363 y
       grind)
    | exact resolve eq830363 eq4871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4871 eq830363
  have eq843038 : x = (k x x) := by
    first
    | (have r₁ := eq843011
       have r₂ := eq829625 (σ y)
       grind)
    | exact resolve eq843011 eq829625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843011
  have eq843093 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2597 x x
       have i₂ := eq843038
       grind)
    | exact superpose eq843038 eq2597
    | (have j0 := eq2597 x x
       grind)
    | (have r₁ := eq2597 x x
       have r₂ := eq843038
       grind)
    | exact resolve eq2597 eq843038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2597
  have eq843180 : x = (M.op x x) := by grind
  clear eq843093
  have eq843629 : ∀ X0 : G, (k x x) = (M.op x X0) ∨ x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq114219 x x x
       have i₂ := eq843180
       grind)
    | exact superpose eq843180 eq114219
    | exact resolve eq114219 eq843180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114219 eq843180
  have eq843734 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq843629 X0
       have i₂ := eq843038
       grind)
    | exact superpose eq843038 eq843629
    | (have j0 := eq843629 X0
       grind)
    | exact resolve eq843629 eq843038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843038 eq843629
  have eq843735 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq843734 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843734
  have eq844356 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5416
       have i₂ := eq843735 y
       grind)
    | exact superpose eq843735 eq5416
    | exact resolve eq5416 eq843735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5416 eq843735
  have eq844936 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq844356
  have eq845155 : False := by grind
  exact eq845155

/-- `Equation4400`: `x ◇ (x ◇ y) = (x ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxy_y_x_pyx_Equation4400 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4400 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4400.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X1) X2) := by
    intro X0 X1 X2
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
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
    | (have i₁ := eq8 X0 X1 X3
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op X0 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X0 (M.op X0 X1) X2
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 X3 : G, (M.op (M.op X0 (M.op X0 X1)) X3) = (M.op (M.op X0 X1) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq8 (M.op X0 X1) x x
       have i₂ := eq8 X0 X1 x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 (M.op X0 X1)) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq20 X0 X1 X3
       have i₂ := eq8 X0 X1 (M.op X0 (M.op X0 X1))
       grind)
    | exact superpose eq8 eq20
    | exact resolve eq20 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
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
  have eq30 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq31 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq12 (τ X1) X0
       grind)
    | exact superpose eq12 eq15
    | (have j1 := eq12 (τ X1) X0
       grind)
    | exact resolve eq15 eq12
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
  have eq60 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op (M.op X0 X1) X3) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 (M.op X0 X1) X3 X4
       have i₂ := eq17 X0 X1 (M.op (M.op X0 X1) X3) X2
       grind)
    | (have i₁ := eq8 (M.op X0 X1) X3 X4
       have i₂ := eq17 X0 X1 X2 (M.op (M.op X0 X1) X3)
       grind)
    | exact superpose eq17 eq8
    | exact resolve eq8 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq228 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) ≠ (M.op (M.op (M.op X0 X1) X2) X3) ∨ (k X0 (M.op (M.op X0 X1) X2)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq11 X0 (M.op (M.op X0 X1) X2)
       have i₂ := eq19 X0 X1 X2 X3
       grind)
    | exact superpose eq19 eq11
    | (have j0 := eq11 X0 (M.op (M.op X0 X1) X2)
       grind)
    | (have r₁ := eq11 (M.op (M.op X0 X1) X2) (M.op X0 (M.op (M.op X0 X1) X2))
       have r₂ := eq19 X0 X1 X2 (M.op X0 (M.op (M.op X0 X1) X2))
       grind)
    | exact resolve eq11 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq236 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op X0 X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq228 X0 X1 X2 x
       grind)
    | (have r₁ := eq228 X0 X1 x x
       have r₂ := eq60 X0 X1 x x x
       grind)
    | exact resolve eq228 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq228
  have eq277 : ∀ X0 X1 : G, (k X0 (M.op X0 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq236 X0 (M.op X0 X1) x
       have i₂ := eq24 X0 X1 x
       grind)
    | exact superpose eq24 eq236
    | exact resolve eq236 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq323 : ∀ X0 X1 X2 X3 : G, (k X0 (M.op X0 (M.op (M.op (M.op X0 X1) X2) X3))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq277 X0 (M.op (M.op X0 X1) X2)
       have i₂ := eq19 X0 X1 X2 X3
       grind)
    | exact superpose eq19 eq277
    | exact resolve eq277 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq339 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (M.op (σ X0) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 (M.op (σ X0) (M.op (σ X0) X1))
       have i₂ := eq277 (σ X0) X1
       grind)
    | exact superpose eq277 eq38
    | exact resolve eq38 eq277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq343 : ∀ X0 X1 : G, (k X0 (τ (M.op (σ X0) (M.op (σ X0) X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq339 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq339
    | exact resolve eq339 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339
  have eq431 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 X1
       have i₂ := eq30 X1 X0
       grind)
    | exact superpose eq30 eq30
    | (have j0 := eq30 X0 X1
       have j1 := eq30 X0 X1
       grind)
    | exact resolve eq30 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq433 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X1) (σ X0)
       have i₂ := eq30 X1 X0
       grind)
    | exact superpose eq30 eq11
    | (have j0 := eq11 (σ X1) (σ X0)
       have j1 := eq30 X1 X0
       grind)
    | (have r₁ := eq11 (σ X1) (σ X0)
       have r₂ := eq30 X0 X1
       grind)
    | exact resolve eq11 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq443 : ∀ X0 X1 X2 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) X2) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (σ X1) (σ X0) X2
       have i₂ := eq30 X0 X1
       grind)
    | exact superpose eq30 eq8
    | (have j1 := eq30 X0 X1
       grind)
    | exact resolve eq8 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq444 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X1) (σ X0)
       have i₂ := eq30 X0 X1
       grind)
    | exact superpose eq30 eq11
    | (have j0 := eq11 (σ X1) (σ X0)
       have j1 := eq30 X0 X1
       grind)
    | (have r₁ := eq11 (σ X1) (σ X0)
       have r₂ := eq30 X0 X1
       grind)
    | exact resolve eq11 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq454 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq30 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq455 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq444 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444
  have eq457 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq455 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq455
    | (have j0 := eq455 X0 X1
       grind)
    | exact resolve eq455 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455
  have eq459 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq433 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq433
    | (have j0 := eq433 X0 X1
       grind)
    | exact resolve eq433 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433
  have eq2622 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq31
    | exact resolve eq31 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq2672 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2622 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq2622
    | (have j0 := eq2622 X0 X1
       grind)
    | exact resolve eq2622 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2622
  have eq4653 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq457 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq457
    | exact resolve eq457 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4660 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq457 x y
       grind)
    | exact superpose eq457 eq14
    | (have j1 := eq457 x y
       grind)
    | exact resolve eq14 eq457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457
  have eq4697 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4653 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq4653
    | (have j0 := eq4653 X0 X1
       grind)
    | exact resolve eq4653 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4653
  have eq4699 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4697 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq4697
    | (have j0 := eq4697 X0 X1
       grind)
    | exact resolve eq4697 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4697
  have eq7569 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4699 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4699
    | exact resolve eq4699 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4699
  have eq7821 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq7569 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7569
  have eq8519 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) X1) ∨ (M.op (σ X0) (σ X2)) = (σ (k X2 X0)) ∨ (M.op (σ X0) (σ X2)) = (σ (k X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30 X0 X2
       have i₂ := eq443 X0 X2 X1
       grind)
    | (have i₁ := eq30 X0 X0
       have i₂ := eq443 X0 X1 (σ X0)
       grind)
    | exact superpose eq443 eq30
    | (have j0 := eq30 X0 X2
       have j1 := eq443 X0 X2 X2
       grind)
    | exact resolve eq30 eq443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq443
  have eq8699 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) X1) ∨ (M.op (σ X0) (σ X2)) = (σ (k X2 X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq8519 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8519
  have eq13182 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq459 (τ X0) (τ X1)
       have i₂ := eq61 X1 X0
       grind)
    | exact superpose eq61 eq459
    | (have j0 := eq459 (τ X0) (τ X1)
       grind)
    | exact resolve eq459 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq459
  have eq13212 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X1)) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq13182 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq13182
    | (have j0 := eq13182 X0 X1
       grind)
    | exact resolve eq13182 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13182
  have eq13224 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq13212 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13212
    | (have j0 := eq13212 X0 X1
       grind)
    | exact resolve eq13212 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13212
  have eq13232 : ∀ X0 X1 : G, (σ (τ X1)) = (k (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq13224 X0 X1
       have i₂ := eq16 X0 (τ X1)
       grind)
    | exact superpose eq16 eq13224
    | (have j0 := eq13224 X0 X1
       grind)
    | exact resolve eq13224 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13224
  have eq13235 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq13232 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13232
    | (have j0 := eq13232 X0 X1
       grind)
    | exact resolve eq13232 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13232
  have eq13236 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X1 X0) = X1 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13235 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13235
    | (have j0 := eq13235 X0 X1
       grind)
    | exact resolve eq13235 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13235
  have eq13237 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X1 X0) = X1 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13236 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13236
    | (have j0 := eq13236 X0 X1
       grind)
    | exact resolve eq13236 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13236
  have eq13238 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq13237 X0 X1
       have j1 := eq7821 X1 X0
       grind)
    | (have r₁ := eq13237 X1 X0
       have r₂ := eq7821 X0 X1
       grind)
    | (have r₁ := eq13237 X0 X1
       have r₂ := eq7821 X0 X1
       grind)
    | exact resolve eq13237 eq7821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7821 eq13237
  have eq13262 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13238 (σ X0) (σ X1)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq13238
    | (have j0 := eq13238 (σ X0) (σ X1)
       grind)
    | exact resolve eq13238 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13238
  have eq13293 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13262 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq13262
    | (have j0 := eq13262 X0 X1
       grind)
    | exact resolve eq13262 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13262
  have eq18343 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq431 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq431
    | exact resolve eq431 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431
  have eq18457 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18343 X0 X1
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq18343
    | (have j0 := eq18343 X0 X1
       grind)
    | exact resolve eq18343 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq18343
  have eq18459 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18457 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq18457
    | (have j0 := eq18457 X0 X1
       grind)
    | exact resolve eq18457 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq18457
  have eq18461 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq18459 X0 X1
       have j1 := eq11 X0 (σ X1)
       grind)
    | (have r₁ := eq18459 X0 X1
       have r₂ := eq11 X0 (σ X1)
       grind)
    | exact resolve eq18459 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18459
  have eq18477 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18461 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq18461
    | exact resolve eq18461 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18507 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 (σ X1)
       have i₂ := eq18461 (σ X0) X1
       grind)
    | exact superpose eq18461 eq38
    | (have j1 := eq18461 (σ X0) X1
       grind)
    | exact resolve eq38 eq18461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq18461
  have eq18579 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18507 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq18507
    | (have j0 := eq18507 X0 X1
       grind)
    | exact resolve eq18507 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18507
  have eq18602 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18579 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq18579
    | (have j0 := eq18579 X0 X1
       grind)
    | exact resolve eq18579 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18579
  have eq18610 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18602 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq18602
    | (have j0 := eq18602 X0 X1
       grind)
    | exact resolve eq18602 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18602
  have eq20776 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq18610 x y
       grind)
    | exact superpose eq18610 eq14
    | (have j1 := eq18610 x y
       grind)
    | exact resolve eq14 eq18610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18610
  have eq20990 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq20776
       have i₂ := eq18477 y x
       grind)
    | exact superpose eq18477 eq20776
    | (have j1 := eq18477 y x
       grind)
    | exact resolve eq20776 eq18477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18477 eq20776
  have eq20999 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) := by grind
  clear eq20990
  have eq21000 : x = (k x y) := by grind
  clear eq20999
  have eq21132 : x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq21000
       grind)
    | exact superpose eq21000 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq21000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21144 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq13293 x y
       have i₂ := eq21000
       grind)
    | exact superpose eq21000 eq13293
    | (have j0 := eq13293 x y
       grind)
    | exact resolve eq13293 eq21000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13293 eq21000
  have eq21145 : (σ y) = (σ (k y x)) := by grind
  clear eq21144
  have eq21152 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq4660
       have i₂ := eq2672 y x
       grind)
    | exact superpose eq2672 eq4660
    | (have j1 := eq2672 y x
       grind)
    | (have r₁ := eq4660
       have r₂ := eq2672 y x
       grind)
    | exact resolve eq4660 eq2672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2672 eq4660
  have eq21153 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y x) := by grind
  clear eq21152
  have eq22484 : ∀ X0 : G, (M.op y x) = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq8 y x x
       have i₂ := eq21132
       grind)
    | exact superpose eq21132 eq8
    | exact resolve eq8 eq21132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24252 : ∀ X0 : G, x = (M.op x X0) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq21132
       have i₂ := eq22484 X0
       grind)
    | exact superpose eq22484 eq21132
    | exact resolve eq21132 eq22484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21132 eq22484
  have eq24398 : ∀ X0 : G, x = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq24252 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24252
  have eq25562 : ∀ X0 X1 : G, x = (k x (M.op y X0)) ∨ x = (M.op x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq236 x y X0
       have i₂ := eq24398 X1
       grind)
    | exact superpose eq24398 eq236
    | (have j1 := eq24398 X1
       grind)
    | exact resolve eq236 eq24398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236 eq24398
  have eq27677 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq8699 x X0 y
       grind)
    | exact superpose eq8699 eq14
    | (have j1 := eq8699 x X0 x
       grind)
    | exact resolve eq14 eq8699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8699
  have eq27783 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq27677 X0
       have i₂ := eq21145
       grind)
    | exact superpose eq21145 eq27677
    | (have j0 := eq27677 X0
       grind)
    | exact resolve eq27677 eq21145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21145 eq27677
  have eq37319 : ∀ X3 : G, x = (k x (M.op y X3)) ∨ x = (k x x) := by
    intro X3
    first
    | (have i₁ := eq323 x x x x
       have i₂ := eq25562 X3 (M.op (M.op (M.op x x) x) x)
       grind)
    | exact superpose eq25562 eq323
    | (have j1 := eq25562 X3 x
       grind)
    | exact resolve eq323 eq25562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323 eq25562
  have eq52332 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) X0) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq27783 X0
       have i₂ := eq21153
       grind)
    | exact superpose eq21153 eq27783
    | (have j0 := eq27783 X0
       grind)
    | (have r₁ := eq27783 X0
       have r₂ := eq21153
       grind)
    | exact resolve eq27783 eq21153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21153 eq27783
  have eq52334 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq52332 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52332
  have eq52523 : x = (k x (τ (σ x))) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq343 x x
       have i₂ := eq52334 (M.op (σ x) x)
       grind)
    | exact superpose eq52334 eq343
    | exact resolve eq343 eq52334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343 eq52334
  have eq52689 : x = (k x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq52523
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq52523
    | exact resolve eq52523 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52523
  have eq53252 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq12 x x
       have i₂ := eq52689
       grind)
    | exact superpose eq52689 eq12
    | (have j0 := eq12 x x
       grind)
    | exact resolve eq12 eq52689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52689
  have eq53266 : x = (M.op y x) ∨ x = (M.op x x) := by grind
  clear eq53252
  have eq53369 : x = (k x x) ∨ x = (k x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq37319 x
       have i₂ := eq53266
       grind)
    | exact superpose eq53266 eq37319
    | exact resolve eq37319 eq53266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37319 eq53266
  have eq53445 : x = (k x x) ∨ x = (M.op x x) := by grind
  clear eq53369
  have eq53482 : x = (k x x) := by
    first
    | (have j1 := eq11 x x
       grind)
    | (have r₁ := eq53445
       have r₂ := eq11 x x
       grind)
    | exact resolve eq53445 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53445
  have eq53626 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq454 x
       have i₂ := eq53482
       grind)
    | exact superpose eq53482 eq454
    | (have j0 := eq454 x
       grind)
    | exact resolve eq454 eq53482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454
  have eq53627 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq12 x x
       have i₂ := eq53482
       grind)
    | exact superpose eq53482 eq12
    | (have j0 := eq12 x x
       grind)
    | exact resolve eq12 eq53482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53482
  have eq53641 : x = (M.op x x) := by grind
  clear eq53627
  have eq53642 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq53626
  have eq54068 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 x x x x
       have i₂ := eq53641
       grind)
    | exact superpose eq53641 eq17
    | exact resolve eq17 eq53641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55411 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq53641
       have i₂ := eq54068 x X0
       grind)
    | (have i₁ := eq53641
       have i₂ := eq54068 X0 x
       grind)
    | exact superpose eq54068 eq53641
    | exact resolve eq53641 eq54068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53641 eq54068
  have eq58103 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 (σ x) (σ x) x x
       have i₂ := eq53642
       grind)
    | exact superpose eq53642 eq17
    | exact resolve eq17 eq53642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq68849 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq58103 (σ y) X0
       grind)
    | (have i₁ := eq14
       have i₂ := eq58103 X0 (σ y)
       grind)
    | exact superpose eq58103 eq14
    | exact resolve eq14 eq58103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68850 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq53642
       have i₂ := eq58103 (σ x) X0
       grind)
    | (have i₁ := eq53642
       have i₂ := eq58103 X0 (σ x)
       grind)
    | exact superpose eq58103 eq53642
    | exact resolve eq53642 eq58103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53642 eq58103
  have eq69015 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq68849 x
       have i₂ := eq68850 x
       grind)
    | exact superpose eq68850 eq68849
    | exact resolve eq68849 eq68850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68849 eq68850
  have eq69075 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq69015
       have i₂ := eq55411 y
       grind)
    | exact superpose eq55411 eq69015
    | exact resolve eq69015 eq55411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55411 eq69015
  have eq69076 : False := by grind
  exact eq69076

/-- `Equation4404`: `x ◇ (x ◇ y) = (x ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxy_y_x_pyx_Equation4404 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4404 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4404.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X2) X3) := by
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
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
  have eq17 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X0 X4) X5) = (M.op X0 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq8 X0 (M.op X0 x) X4 X5
       have i₂ := eq8 X0 x X1 X2
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
  have eq23 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 X2)) := by
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
  have eq24 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X0 X4)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 X0 X4 X1 (M.op (M.op X0 X1) x)
       have i₂ := eq8 (M.op X0 X1) x X2 X3
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) ≠ X3 ∨ (M.op X0 X2) = (k (M.op X0 X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq11 (M.op X0 X2) X3
       have i₂ := eq8 X0 X1 X2 X3
       grind)
    | exact superpose eq8 eq11
    | (have j0 := eq11 (M.op X0 X2) X3
       grind)
    | (have r₁ := eq11 (M.op X0 X2) (M.op X0 (M.op X0 X1))
       have r₂ := eq8 X0 X1 X2 (M.op X0 (M.op X0 X1))
       grind)
    | exact resolve eq11 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq33 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq12 (τ X1) X0
       grind)
    | exact superpose eq12 eq15
    | (have j1 := eq12 (τ X1) X0
       grind)
    | exact resolve eq15 eq12
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
  have eq114 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op X0 X2) ∨ (k X0 (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X0 (M.op X0 X2)
       have i₂ := eq23 X0 X2 X1
       grind)
    | (have i₁ := eq11 X0 (M.op X0 X2)
       have i₂ := eq23 X0 X1 X2
       grind)
    | exact superpose eq23 eq11
    | (have j0 := eq11 X0 (M.op X0 X2)
       grind)
    | (have r₁ := eq11 X0 (M.op X0 (M.op X0 X2))
       have r₂ := eq23 X0 (M.op X0 X2) X2
       grind)
    | (have r₁ := eq11 X0 (M.op X0 (M.op X0 X1))
       have r₂ := eq23 X0 X1 (M.op X0 X1)
       grind)
    | exact resolve eq11 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq40 X1 X0
       have i₂ := eq12 (σ X1) X0
       grind)
    | exact superpose eq12 eq40
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq40 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq266 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X0 X5) X6) = (M.op X0 (M.op (M.op (M.op (M.op X0 X1) X2) X3) X4)) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq17 X0 X1 (M.op (M.op X0 X1) x) X5 X6
       have i₂ := eq24 (M.op X0 X1) X2 X3 X4 x
       grind)
    | exact superpose eq24 eq17
    | exact resolve eq17 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq288 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (M.op (M.op X0 X2) X3) X4) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq17 (M.op (M.op X0 X2) X3) x x X4 X5
       have i₂ := eq24 X0 X2 X3 (M.op (M.op (M.op (M.op X0 X2) X3) x) x) X1
       grind)
    | exact superpose eq24 eq17
    | exact resolve eq17 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq24
  have eq577 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq26 X0 X1 X1 (M.op X0 (M.op X0 X2))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1085 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X1) (σ X0)
       have i₂ := eq32 X0 X1
       grind)
    | exact superpose eq32 eq11
    | (have j0 := eq11 (σ X1) (σ X0)
       have j1 := eq32 X0 X1
       grind)
    | (have r₁ := eq11 (σ X1) (σ X0)
       have r₂ := eq32 X0 X1
       grind)
    | exact resolve eq11 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1109 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq32 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1110 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1085 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1085
  have eq1112 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1110 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1110
    | (have j0 := eq1110 X0 X1
       grind)
    | exact resolve eq1110 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1110
  have eq3203 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X0 X1))) ≠ (σ (M.op X0 (M.op X0 X1))) ∨ (σ (M.op X0 (M.op X0 X1))) = (M.op (σ (M.op X0 (M.op X0 X1))) (σ (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1109 (M.op X0 (M.op X0 X1))
       have i₂ := eq577 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq577 eq1109
    | (have j0 := eq1109 (M.op X0 (M.op X0 X1))
       grind)
    | exact resolve eq1109 eq577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq577 eq1109
  have eq3208 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X0 X1))) = (M.op (σ (M.op X0 (M.op X0 X1))) (σ (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have j0 := eq3203 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3203
  have eq3216 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq33 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq33
    | exact resolve eq33 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq3259 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3216 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq3216
    | (have j0 := eq3216 X0 X1
       grind)
    | exact resolve eq3216 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3216
  have eq3469 : ∀ X0 X1 : G, (k X0 (M.op X0 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq114 X0 X1 (M.op X0 X1)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq3478 : ∀ X0 X1 X2 X3 X4 : G, (k X0 (M.op X0 (M.op (M.op (M.op (M.op X0 X1) X2) X3) X4))) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq3469 X0 (M.op X0 x)
       have i₂ := eq288 X0 x X1 X2 X3 X4
       grind)
    | exact superpose eq288 eq3469
    | exact resolve eq3469 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288 eq3469
  have eq6607 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1112 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1112
    | exact resolve eq1112 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6614 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1112 x y
       grind)
    | exact superpose eq1112 eq14
    | (have j1 := eq1112 x y
       grind)
    | exact resolve eq14 eq1112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6615 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X0 X1
       have i₂ := eq1112 X1 X0
       grind)
    | exact superpose eq1112 eq32
    | (have j0 := eq32 X0 X1
       have j1 := eq1112 X0 X1
       grind)
    | exact resolve eq32 eq1112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq1112
  have eq6674 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq6615 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6615
  have eq6678 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6607 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq6607
    | (have j0 := eq6607 X0 X1
       grind)
    | exact resolve eq6607 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6607
  have eq6680 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6678 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq6678
    | (have j0 := eq6678 X0 X1
       grind)
    | exact resolve eq6678 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq6678
  have eq12196 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6680 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6680
    | exact resolve eq6680 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6680
  have eq12622 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq12196 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23373 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq6614
       have i₂ := eq12196 x y
       grind)
    | exact superpose eq12196 eq6614
    | (have j1 := eq12196 x y
       grind)
    | exact resolve eq6614 eq12196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12196
  have eq23375 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq6614
       have i₂ := eq3259 y x
       grind)
    | exact superpose eq3259 eq6614
    | (have j1 := eq3259 y x
       grind)
    | (have r₁ := eq6614
       have r₂ := eq3259 y x
       grind)
    | exact resolve eq6614 eq3259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6614
  have eq23376 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y x) := by grind
  clear eq23375
  have eq23378 : (σ (M.op x y)) = (σ y) ∨ y = (k y x) := by grind
  clear eq23373
  have eq23987 : (M.op x y) = (τ (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq9 (M.op x y)
       have i₂ := eq23376
       grind)
    | exact superpose eq23376 eq9
    | exact resolve eq9 eq23376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23376
  have eq24086 : x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq23987
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq23987
    | exact resolve eq23987 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23987
  have eq24751 : ∀ X0 X1 : G, (M.op y (M.op y X0)) = (M.op x X1) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq8 y X0 x X1
       have i₂ := eq24086
       grind)
    | exact superpose eq24086 eq8
    | exact resolve eq8 eq24086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24820 : x ≠ x ∨ x = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12622 x y
       have i₂ := eq24086
       grind)
    | exact superpose eq24086 eq12622
    | (have j0 := eq12622 x y
       grind)
    | (have r₁ := eq12622 x y
       have r₂ := eq24086
       grind)
    | (have r₁ := eq12622 y x
       have r₂ := eq24086
       grind)
    | exact resolve eq12622 eq24086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24827 : x = (k x y) ∨ y = (M.op x y) := by grind
  clear eq24820
  have eq25064 : (σ x) = (σ (M.op y x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3259 x y
       have i₂ := eq24827
       grind)
    | exact superpose eq24827 eq3259
    | (have j0 := eq3259 x y
       grind)
    | exact resolve eq3259 eq24827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3259 eq24827
  have eq25070 : (σ x) = (σ (M.op y x)) ∨ y = (M.op x y) := by grind
  clear eq25064
  have eq29838 : ∀ X0 : G, (M.op y x) = (M.op x X0) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq24751 x X0
       have i₂ := eq24086
       grind)
    | exact superpose eq24086 eq24751
    | exact resolve eq24751 eq24086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29862 : ∀ X0 X2 : G, (M.op x X2) = (M.op x X0) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X2
    first
    | (have i₁ := eq24751 x X0
       have i₂ := eq24751 x X2
       grind)
    | exact superpose eq24751 eq24751
    | exact resolve eq24751 eq24751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24751
  have eq30151 : ∀ X0 X2 : G, (M.op x X2) = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0 X2
    first
    | (have j0 := eq29862 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29862
  have eq30153 : ∀ X0 : G, (M.op y x) = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq29838 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29838
  have eq30912 : ∀ X0 X1 X2 : G, (M.op x y) = (M.op x (M.op x X0)) ∨ (M.op x X1) = (M.op x X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 x X0 y
       have i₂ := eq30151 X2 X1
       grind)
    | exact superpose eq30151 eq23
    | (have j1 := eq30151 (M.op x X0) y
       grind)
    | exact resolve eq23 eq30151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq30979 : ∀ X0 X1 : G, y ≠ y ∨ y = (k y x) ∨ (M.op x X1) = (M.op x X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12622 y x
       have i₂ := eq30151 X0 X1
       grind)
    | exact superpose eq30151 eq12622
    | (have j0 := eq12622 y x
       have j1 := eq30151 X0 X1
       grind)
    | (have r₁ := eq12622 (M.op x X0) x
       have r₂ := eq30151 X0 (M.op x X0)
       grind)
    | (have r₁ := eq12622 (M.op x x) x
       have r₂ := eq30151 (M.op x x) x
       grind)
    | (have r₁ := eq12622 y x
       have r₂ := eq30151 X0 x
       grind)
    | exact resolve eq12622 eq30151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30151
  have eq30988 : ∀ X0 X1 : G, y = (k y x) ∨ (M.op x X1) = (M.op x X0) := by
    intro X0 X1
    first
    | (have j0 := eq30979 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30979
  have eq31799 : ∀ X0 : G, (σ x) = (σ (M.op x X0)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq25070
       have i₂ := eq30153 X0
       grind)
    | exact superpose eq30153 eq25070
    | exact resolve eq25070 eq30153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25070
  have eq31802 : ∀ X0 : G, x = (M.op x X0) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq24086
       have i₂ := eq30153 X0
       grind)
    | exact superpose eq30153 eq24086
    | exact resolve eq24086 eq30153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24086 eq30153
  have eq32050 : ∀ X0 : G, x = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq31802 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31802
  have eq32053 : ∀ X0 : G, (σ x) = (σ (M.op x X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq31799 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31799
  have eq32160 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X1) (σ X0)
       have i₂ := eq6674 X1 X0
       grind)
    | exact superpose eq6674 eq11
    | (have j0 := eq11 (σ X1) (σ X0)
       have j1 := eq6674 X1 X0
       grind)
    | exact resolve eq11 eq6674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6674
  have eq32265 : ∀ X0 X1 : G, (σ X1) = (σ (k X1 X0)) ∨ (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq32160 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq32160
    | (have j0 := eq32160 X0 X1
       grind)
    | exact resolve eq32160 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32160
  have eq32266 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq32265 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32265
  have eq32538 : ∀ X0 : G, y ≠ y ∨ y = (k y x) ∨ x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq12622 y x
       have i₂ := eq32050 X0
       grind)
    | exact superpose eq32050 eq12622
    | (have j0 := eq12622 y x
       have j1 := eq32050 X0
       grind)
    | (have r₁ := eq12622 x x
       have r₂ := eq32050 x
       grind)
    | (have r₁ := eq12622 y x
       have r₂ := eq32050 X0
       grind)
    | exact resolve eq12622 eq32050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12622 eq32050
  have eq32546 : ∀ X0 : G, y = (k y x) ∨ x = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq32538 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32538
  have eq36822 : ∀ X0 X1 : G, x = (M.op (M.op x X0) X1) ∨ y = (k y x) := by
    intro X0 X1
    first
    | (have i₁ := eq266 x x x x x X0 X1
       have i₂ := eq32546 (M.op (M.op (M.op (M.op x x) x) x) x)
       grind)
    | exact superpose eq32546 eq266
    | exact resolve eq266 eq32546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266 eq32546
  have eq42239 : ∀ X0 : G, (σ y) = (σ (M.op x X0)) ∨ y = (k y x) ∨ y = (k y x) := by
    intro X0
    first
    | (have i₁ := eq23378
       have i₂ := eq30988 X0 y
       grind)
    | (have i₁ := eq23378
       have i₂ := eq30988 y X0
       grind)
    | exact superpose eq30988 eq23378
    | exact resolve eq23378 eq30988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23378 eq30988
  have eq42420 : ∀ X0 : G, (σ y) = (σ (M.op x X0)) ∨ y = (k y x) := by
    intro X0
    first
    | (have j0 := eq42239 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42239
  have eq59983 : ∀ X0 : G, (τ (σ y)) = (M.op x X0) ∨ y = (k y x) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op x X0)
       have i₂ := eq42420 X0
       grind)
    | exact superpose eq42420 eq9
    | exact resolve eq9 eq42420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42420
  have eq60106 : ∀ X0 : G, y = (M.op x X0) ∨ y = (k y x) := by
    intro X0
    first
    | (have i₁ := eq59983 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq59983
    | exact resolve eq59983 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59983
  have eq66746 : ∀ X1 : G, x = (M.op y X1) ∨ y = (k y x) ∨ y = (k y x) := by
    intro X1
    first
    | (have i₁ := eq36822 x X1
       have i₂ := eq60106 x
       grind)
    | exact superpose eq60106 eq36822
    | exact resolve eq36822 eq60106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36822 eq60106
  have eq67164 : ∀ X1 : G, x = (M.op y X1) ∨ y = (k y x) := by
    intro X1
    first
    | (have j0 := eq66746 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66746
  have eq67883 : y = (k y x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq3478 y x x x x
       have i₂ := eq67164 (M.op (M.op (M.op (M.op y x) x) x) x)
       grind)
    | exact superpose eq67164 eq3478
    | exact resolve eq3478 eq67164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3478 eq67164
  have eq67911 : y = (k y x) := by grind
  clear eq67883
  have eq89189 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq32266 y x
       have i₂ := eq67911
       grind)
    | exact superpose eq67911 eq32266
    | (have j0 := eq32266 y x
       grind)
    | exact resolve eq32266 eq67911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32266 eq67911
  have eq89199 : (σ x) = (σ (k x y)) := by grind
  clear eq89189
  have eq91366 : (k x y) = (τ (σ x)) := by
    first
    | (have i₁ := eq9 (k x y)
       have i₂ := eq89199
       grind)
    | exact superpose eq89199 eq9
    | exact resolve eq9 eq89199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89199
  have eq91479 : x = (k x y) := by
    first
    | (have i₁ := eq91366
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq91366
    | exact resolve eq91366 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91366
  have eq432765 : ∀ X0 X1 : G, (M.op x y) ≠ (M.op x X1) ∨ (M.op x X1) = (M.op x (M.op x X0)) := by
    intro X0 X1
    first
    | (have j0 := eq30912 X0 X1 (M.op x X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30912
  have eq464769 : ∀ X0 : G, (M.op x y) = (M.op x (M.op x X0)) := by
    intro X0
    first
    | (have j0 := eq432765 X0 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432765
  have eq465538 : ∀ X1 X2 : G, (M.op x y) = (M.op (M.op x X1) X2) := by
    intro X1 X2
    first
    | (have i₁ := eq8 x x X1 X2
       have i₂ := eq464769 x
       grind)
    | exact superpose eq464769 eq8
    | exact resolve eq8 eq464769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq465558 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq3208 x x
       have i₂ := eq464769 x
       grind)
    | exact superpose eq464769 eq3208
    | exact resolve eq3208 eq464769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3208 eq464769
  have eq475679 : ∀ X0 X1 X2 : G, (M.op (M.op (σ (M.op x y)) X0) X1) = (M.op (σ (M.op x y)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 (σ (M.op x y)) X0 X1 (σ (M.op x y)) X2
       have i₂ := eq465558
       grind)
    | exact superpose eq465558 eq19
    | exact resolve eq19 eq465558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq482667 : ∀ X0 X3 : G, (M.op (σ (M.op x y)) X0) = (M.op (σ (M.op x y)) X3) := by
    intro X0 X3
    first
    | (have i₁ := eq475679 x x X3
       have i₂ := eq475679 x x X0
       grind)
    | exact superpose eq475679 eq475679
    | exact resolve eq475679 eq475679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475679
  have eq482862 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq465558
       have i₂ := eq482667 (σ (M.op x y)) X0
       grind)
    | (have i₁ := eq465558
       have i₂ := eq482667 X0 (σ (M.op x y))
       grind)
    | exact superpose eq482667 eq465558
    | exact resolve eq465558 eq482667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465558 eq482667
  have eq482937 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq482862 X0
       have i₂ := eq32053 y
       grind)
    | exact superpose eq32053 eq482862
    | exact resolve eq482862 eq32053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq483808 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq482937 (σ y)
       grind)
    | exact superpose eq482937 eq14
    | exact resolve eq14 eq482937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482937
  have eq484034 : (σ x) ≠ (σ x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq483808
       have i₂ := eq32053 y
       grind)
    | exact superpose eq32053 eq483808
    | (have r₁ := eq483808
       have r₂ := eq32053 y
       grind)
    | exact resolve eq483808 eq32053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32053 eq483808
  have eq484035 : (σ x) ≠ (σ x) ∨ y = (M.op x y) := by grind
  clear eq484034
  have eq484036 : y = (M.op x y) := by grind
  clear eq484035
  have eq484150 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq482862 X0
       have i₂ := eq484036
       grind)
    | exact superpose eq484036 eq482862
    | exact resolve eq482862 eq484036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482862
  have eq484343 : ∀ X0 : G, y = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq465538 y x
       have i₂ := eq484036
       grind)
    | exact superpose eq484036 eq465538
    | exact resolve eq465538 eq484036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465538
  have eq486200 : ∀ X0 : G, (τ (σ y)) = (k X0 (τ (σ y))) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq124 (σ y) X0
       have i₂ := eq484150 (σ X0)
       grind)
    | exact superpose eq484150 eq124
    | (have j0 := eq124 (σ y) X0
       grind)
    | exact resolve eq124 eq484150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq486219 : ∀ X0 : G, (σ y) = (M.op (σ X0) (σ y)) ∨ y = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq486200 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq486200
    | (have j0 := eq486200 X0
       grind)
    | exact resolve eq486200 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486200
  have eq511228 : (σ (M.op x y)) ≠ (σ y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq486219 x
       grind)
    | exact superpose eq486219 eq14
    | (have j1 := eq486219 x
       grind)
    | exact resolve eq14 eq486219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486219
  have eq511278 : (σ y) ≠ (σ y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq511228
       have i₂ := eq484036
       grind)
    | exact superpose eq484036 eq511228
    | exact resolve eq511228 eq484036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484036 eq511228
  have eq511279 : y = (k x y) := by grind
  clear eq511278
  have eq511290 : x = y := by
    first
    | (have i₁ := eq511279
       have i₂ := eq91479
       grind)
    | exact superpose eq91479 eq511279
    | exact resolve eq511279 eq91479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91479 eq511279
  have eq511293 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq511290
       grind)
    | exact superpose eq511290 eq14
    | exact resolve eq14 eq511290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq511888 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq484150 X0
       have i₂ := eq511290
       grind)
    | exact superpose eq511290 eq484150
    | exact resolve eq484150 eq511290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484150
  have eq511891 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq484343 X0
       have i₂ := eq511290
       grind)
    | exact superpose eq511290 eq484343
    | exact resolve eq484343 eq511290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484343 eq511290
  have eq512055 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq511293
       have i₂ := eq511891 x
       grind)
    | exact superpose eq511891 eq511293
    | exact resolve eq511293 eq511891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511293 eq511891
  have eq512076 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq512055
       have i₂ := eq511888 (σ x)
       grind)
    | exact superpose eq511888 eq512055
    | (have r₁ := eq512055
       have r₂ := eq511888 (σ x)
       grind)
    | exact resolve eq512055 eq511888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511888 eq512055
  have eq512077 : False := by grind
  exact eq512077

/-- `Equation4407`: `x ◇ (x ◇ y) = (y ◇ x) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation4407 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4407 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4407.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq59 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq72 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq59 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq442 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq72 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq446 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq442 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq442 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq442 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq442 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442
  have eq483 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq446 (σ X0) (σ X1)
       grind)
    | exact superpose eq446 eq13
    | exact resolve eq13 eq446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq490 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq483 X0 X1
       have i₂ := eq446 X0 X1
       grind)
    | exact superpose eq446 eq483
    | exact resolve eq483 eq446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446 eq483
  have eq1187 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq490 x y
       grind)
    | exact superpose eq490 eq14
    | (have r₁ := eq14
       have r₂ := eq490 x y
       grind)
    | exact resolve eq14 eq490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490
  have eq1210 : False := by grind
  exact eq1210
