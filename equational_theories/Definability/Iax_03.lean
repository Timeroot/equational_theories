import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation106`: `x = x ◇ ((y ◇ x) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxy_x_pxy_pyx_Equation106 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law106 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law106.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
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
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
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
  have eq17 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq18 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq20 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 (M.op X1 X0)
       have i₂ := eq16 X1 X0
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op X1 X0) X0 X2
       have i₂ := eq16 X1 X0
       grind)
    | exact superpose eq16 eq8
    | exact resolve eq8 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (M.op X0 X1)
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq11
    | (have r₁ := eq11 X1 (M.op X0 X1)
       have r₂ := eq16 X0 X1
       grind)
    | exact resolve eq11 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X1 X0) X0
       have i₂ := eq20 X0 X1
       grind)
    | exact superpose eq20 eq11
    | (have r₁ := eq11 (M.op X1 X0) X0
       have r₂ := eq20 X0 X1
       grind)
    | exact resolve eq11 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq32 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have j0 := eq31 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq33 : ∀ X0 X1 : G, (k X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq30 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq40 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq51 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (M.op X1 (τ X0))
       have i₂ := eq33 (τ X0) X1
       grind)
    | exact superpose eq33 eq17
    | exact resolve eq17 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq9
    | exact resolve eq9 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq58 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 (τ X0)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq51 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq51
    | exact resolve eq51 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq65 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq12 X1 (τ X0)
       grind)
    | exact superpose eq12 eq18
    | (have j1 := eq12 X1 (τ X0)
       grind)
    | exact resolve eq18 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq9
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq56 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq56
    | exact resolve eq56 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 X1 : G, (τ (M.op X0 (σ X1))) = (k (τ (M.op X0 (σ X1))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq56 (M.op X0 (σ X1)) X1
       have i₂ := eq32 X0 (σ X1)
       grind)
    | exact superpose eq32 eq56
    | exact resolve eq56 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq139 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X1))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (σ X1) (σ X0)
       have i₂ := eq40 X1 X0
       grind)
    | exact superpose eq40 eq16
    | (have j1 := eq40 (k X0 X1) X0
       grind)
    | exact resolve eq16 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (σ X0) (σ X1)
       have i₂ := eq40 X1 X0
       grind)
    | exact superpose eq40 eq16
    | (have j1 := eq40 X1 X0
       grind)
    | exact resolve eq16 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq169 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq71 X0 (M.op X1 (σ X0))
       have i₂ := eq33 (σ X0) X1
       grind)
    | exact superpose eq33 eq71
    | exact resolve eq71 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq71
  have eq184 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 (σ X0)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq169 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq169
    | exact resolve eq169 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq219 : ∀ X0 X1 : G, (k X0 (τ (σ (k X0 X1)))) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq184 X0 (σ X1)
       have i₂ := eq40 X1 X0
       grind)
    | exact superpose eq40 eq184
    | (have j1 := eq40 X1 X0
       grind)
    | exact resolve eq184 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq228 : ∀ X0 X1 : G, (k X0 (k X0 X1)) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq219 X0 X1
       have i₂ := eq9 (k X0 X1)
       grind)
    | exact superpose eq9 eq219
    | (have j0 := eq219 X0 X1
       grind)
    | exact resolve eq219 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq1121 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq65 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq65
    | exact resolve eq65 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq1158 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1121 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1121
    | (have j0 := eq1121 X0 X1
       grind)
    | exact resolve eq1121 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1121
  have eq1331 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ (k X0 X1)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq139 (τ X0) (τ X1)
       have i₂ := eq107 X1 X0
       grind)
    | exact superpose eq107 eq139
    | (have j0 := eq139 (τ X0) (τ (k X0 X1))
       grind)
    | exact resolve eq139 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq1380 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1331 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq1331
    | (have j0 := eq1331 X0 X1
       grind)
    | exact resolve eq1331 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1331
  have eq1386 : ∀ X0 X1 : G, (M.op X0 (k X0 X1)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1380 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1380
    | (have j0 := eq1380 X0 X1
       grind)
    | exact resolve eq1380 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1380
  have eq1387 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 (k X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1386 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1386
    | (have j0 := eq1386 X0 X1
       grind)
    | exact resolve eq1386 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1386
  have eq1388 : ∀ X0 X1 : G, (M.op X0 (k X0 X1)) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1387 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1387
    | (have j0 := eq1387 X0 X1
       grind)
    | exact resolve eq1387 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1387
  have eq1421 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (k X0 X1) X2)) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 (k X0 X1) X0 X2
       have i₂ := eq1388 X0 X1
       grind)
    | exact superpose eq1388 eq21
    | (have j1 := eq1388 X0 (M.op (k X0 X1) X2)
       grind)
    | exact resolve eq21 eq1388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1388
  have eq1474 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq148 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq148
    | exact resolve eq148 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1484 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq148 y x
       grind)
    | exact superpose eq148 eq14
    | (have j1 := eq148 y x
       grind)
    | exact resolve eq14 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1525 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq148 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq1531 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1474 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq1474
    | (have j0 := eq1474 X0 X1
       grind)
    | exact resolve eq1474 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1474
  have eq5176 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1525 (τ X1) (τ X0)
       have i₂ := eq107 X1 X0
       grind)
    | exact superpose eq107 eq1525
    | (have j0 := eq1525 (τ X1) (τ X0)
       grind)
    | exact resolve eq1525 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq5195 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5176 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq5176
    | (have j0 := eq5176 X0 X1
       grind)
    | exact resolve eq5176 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5176
  have eq5206 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5195 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq5195
    | (have j0 := eq5195 X0 X1
       grind)
    | exact resolve eq5195 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5195
  have eq5213 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5206 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5206
    | (have j0 := eq5206 X0 X1
       grind)
    | exact resolve eq5206 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5206
  have eq5214 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5213 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5213
    | (have j0 := eq5213 X0 X1
       grind)
    | exact resolve eq5213 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5213
  have eq5252 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1531 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1531
    | exact resolve eq1531 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5315 : ∀ X0 X1 : G, (σ X1) = (M.op (σ (M.op X0 (τ (σ X1)))) (σ X1)) ∨ (σ (M.op X0 (τ (σ X1)))) = (M.op (σ (M.op X0 (τ (σ X1)))) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq58 (σ X1) X0
       have i₂ := eq1531 (σ (M.op X0 (τ (σ X1)))) X1
       grind)
    | exact superpose eq1531 eq58
    | (have j1 := eq1531 (σ (M.op X0 (τ (σ X1)))) X1
       grind)
    | exact resolve eq58 eq1531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq1531
  have eq5355 : ∀ X0 X1 : G, (σ X1) = (M.op (σ (M.op X0 X1)) (σ X1)) ∨ (σ (M.op X0 (τ (σ X1)))) = (M.op (σ (M.op X0 (τ (σ X1)))) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5315 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq5315
    | (have j0 := eq5315 X0 X1
       grind)
    | exact resolve eq5315 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5315
  have eq5367 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ X1)) ∨ (σ X1) = (M.op (σ (M.op X0 X1)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5355 X0 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq5355
    | (have j0 := eq5355 X0 X1
       grind)
    | exact resolve eq5355 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5355
  have eq7867 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1484
       have i₂ := eq1158 x y
       grind)
    | exact superpose eq1158 eq1484
    | (have j1 := eq1158 (σ y) (σ x)
       grind)
    | (have r₁ := eq1484
       have r₂ := eq1158 x y
       grind)
    | exact resolve eq1484 eq1158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1158 eq1484
  have eq7868 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq7867
  have eq7881 : (τ (σ x)) = (k (τ (σ x)) y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq113 (σ x) y
       have i₂ := eq7868
       grind)
    | exact superpose eq7868 eq113
    | exact resolve eq113 eq7868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq7885 : y = (k y (τ (σ x))) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq184 y (σ x)
       have i₂ := eq7868
       grind)
    | exact superpose eq7868 eq184
    | exact resolve eq184 eq7868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184 eq7868
  have eq7943 : y = (k y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq7885
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq7885
    | exact resolve eq7885 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7885
  have eq7944 : x = (k x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq7881
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq7881
    | exact resolve eq7881 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7881
  have eq8145 : ∀ X0 : G, y = (M.op y (M.op y X0)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq1421 y x X0
       have i₂ := eq7943
       grind)
    | exact superpose eq7943 eq1421
    | (have j0 := eq1421 y (M.op y X0) x
       grind)
    | exact resolve eq1421 eq7943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1421
  have eq8151 : x ≠ y ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq5214 y x
       have i₂ := eq7943
       grind)
    | exact superpose eq7943 eq5214
    | (have j0 := eq5214 y x
       grind)
    | exact resolve eq5214 eq7943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5214 eq7943
  have eq8161 : ∀ X0 : G, y = (M.op y (M.op y X0)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq8145 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8145
  have eq8330 : x = (M.op y x) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq5252 x y
       have i₂ := eq7944
       grind)
    | exact superpose eq7944 eq5252
    | (have j0 := eq5252 x y
       grind)
    | exact resolve eq5252 eq7944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5252 eq7944
  have eq8335 : y = (M.op y x) ∨ x = (M.op y x) := by grind
  clear eq8330
  have eq8897 : x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16 y x
       have i₂ := eq8335
       grind)
    | exact superpose eq8335 eq16
    | exact resolve eq16 eq8335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8335
  have eq17139 : y = (M.op y x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8161 x
       have i₂ := eq8897
       grind)
    | exact superpose eq8897 eq8161
    | exact resolve eq8161 eq8897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8161 eq8897
  have eq17206 : y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq17139
       have r₂ := eq8151
       grind)
    | exact resolve eq17139 eq8151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8151 eq17139
  have eq17545 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16 y x
       have i₂ := eq17206
       grind)
    | exact superpose eq17206 eq16
    | exact resolve eq16 eq17206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq17206
  have eq17599 : x = (M.op x y) := by grind
  clear eq17545
  have eq17943 : x = (k x y) := by
    first
    | (have i₁ := eq32 x y
       have i₂ := eq17599
       grind)
    | exact superpose eq17599 eq32
    | exact resolve eq32 eq17599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq102968 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq228 x y
       have i₂ := eq17943
       grind)
    | exact superpose eq17943 eq228
    | (have j0 := eq228 x y
       grind)
    | exact resolve eq228 eq17943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228 eq17943
  have eq103506 : (σ (M.op x y)) ≠ (σ x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq102968
       grind)
    | exact superpose eq102968 eq14
    | exact resolve eq14 eq102968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102968
  have eq103699 : (σ x) ≠ (σ x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq103506
       have i₂ := eq17599
       grind)
    | exact superpose eq17599 eq103506
    | exact resolve eq103506 eq17599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103506
  have eq103700 : x = (k x x) := by grind
  clear eq103699
  have eq104054 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1525 x x
       have i₂ := eq103700
       grind)
    | exact superpose eq103700 eq1525
    | (have j0 := eq1525 x x
       grind)
    | exact resolve eq1525 eq103700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1525 eq103700
  have eq104085 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq104054
  have eq105897 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq21 (σ x) (σ x) x
       have i₂ := eq104085
       grind)
    | exact superpose eq104085 eq21
    | exact resolve eq21 eq104085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq104085
  have eq344139 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5367 x y
       have i₂ := eq17599
       grind)
    | exact superpose eq17599 eq5367
    | exact resolve eq5367 eq17599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5367
  have eq452870 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq105897 (σ y)
       have i₂ := eq344139
       grind)
    | exact superpose eq344139 eq105897
    | exact resolve eq105897 eq344139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105897 eq344139
  have eq452905 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq452870
  have eq452933 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq452905
       grind)
    | exact superpose eq452905 eq14
    | exact resolve eq14 eq452905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452905
  have eq453309 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq452933
       have i₂ := eq17599
       grind)
    | exact superpose eq17599 eq452933
    | exact resolve eq452933 eq17599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17599 eq452933
  have eq453310 : False := by grind
  exact eq453310

/-- `Equation1060`: `x = x ◇ ((y ◇ (z ◇ y)) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_x_pxx_pyx_Equation1060 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1060 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law1060.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X1)) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq20 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq22 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X0 (M.op X0 (M.op x X0))
       have i₂ := eq8 X0 X0 x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 X0) X1
       have i₂ := eq22 X0 (M.op X0 X0)
       grind)
    | exact superpose eq22 eq11
    | (have r₁ := eq11 (M.op X0 X0) X1
       have r₂ := eq22 X0 (M.op X0 X0)
       grind)
    | exact resolve eq11 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq54 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X2 X0) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j1 := eq12 X0 X2
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X1) X1
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 X2 : G, (k X0 X1) = X0 ∨ (M.op X2 X0) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq54 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq67 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq12 X1 (τ X0)
       grind)
    | exact superpose eq12 eq16
    | (have j1 := eq12 X1 X1
       grind)
    | exact resolve eq16 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op X0 X0)
       have i₂ := eq35 X0 (τ X1)
       grind)
    | exact superpose eq35 eq16
    | exact resolve eq16 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq100 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq59 (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq59 eq13
    | (have j1 := eq59 (σ X1) X2 X2
       grind)
    | exact resolve eq13 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq229 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq57 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq580 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq67 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq67
    | (have j0 := eq67 X0 X1
       grind)
    | exact resolve eq67 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq637 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq580 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq580
    | (have j0 := eq580 X0 X1
       grind)
    | exact resolve eq580 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580
  have eq1228 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq229 (τ X0)
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq229
    | (have j0 := eq229 (τ X0)
       grind)
    | exact resolve eq229 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq229
  have eq1242 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1228 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1228
    | (have j0 := eq1228 X0
       grind)
    | exact resolve eq1228 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1228
  have eq1251 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1242 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1242
    | (have j0 := eq1242 X0
       grind)
    | exact resolve eq1242 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1242
  have eq1815 : ∀ X0 X1 X2 : G, (σ X0) = (k (σ X0) X1) ∨ (σ (k X0 X2)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq68 X1 X1
       have i₂ := eq637 X0 X1
       grind)
    | exact superpose eq637 eq68
    | (have j1 := eq637 X2 X0
       grind)
    | exact resolve eq68 eq637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq637
  have eq1893 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (k (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq100 x y X0
       grind)
    | exact superpose eq100 eq14
    | (have j1 := eq100 X0 y X0
       grind)
    | exact resolve eq14 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq1952 : ∀ X0 : G, (σ y) = (k (σ y) X0) := by
    intro X0
    first
    | (have j0 := eq1893 X0
       have j1 := eq1815 y X0 x
       grind)
    | (have r₁ := eq1893 X0
       have r₂ := eq1815 y x x
       grind)
    | exact resolve eq1893 eq1815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1815 eq1893
  have eq1979 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1251 (σ y)
       have i₂ := eq1952 (σ y)
       grind)
    | exact superpose eq1952 eq1251
    | (have j0 := eq1251 (σ y)
       grind)
    | (have r₁ := eq1251 (σ y)
       have r₂ := eq1952 (σ y)
       grind)
    | exact resolve eq1251 eq1952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1991 : ∀ X0 : G, (τ (σ y)) = (k (τ (σ y)) X0) := by
    intro X0
    first
    | (have i₁ := eq20 (σ y) X0
       have i₂ := eq1952 (σ X0)
       grind)
    | exact superpose eq1952 eq20
    | exact resolve eq20 eq1952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1952
  have eq1994 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq1979
  have eq1995 : ∀ X0 : G, y = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq1991 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1991
    | exact resolve eq1991 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1991
  have eq2115 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1251 y
       have i₂ := eq1995 y
       grind)
    | exact superpose eq1995 eq1251
    | (have j0 := eq1251 y
       grind)
    | (have r₁ := eq1251 y
       have r₂ := eq1995 y
       grind)
    | exact resolve eq1251 eq1995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1251 eq1995
  have eq2130 : y = (M.op y y) := by grind
  clear eq2115
  have eq2265 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq22 y X0
       have i₂ := eq2130
       grind)
    | exact superpose eq2130 eq22
    | exact resolve eq22 eq2130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2130
  have eq3082 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq22 (σ y) X0
       have i₂ := eq1994
       grind)
    | exact superpose eq1994 eq22
    | exact resolve eq22 eq1994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1994
  have eq3349 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq3082 (σ x)
       grind)
    | exact superpose eq3082 eq14
    | exact resolve eq14 eq3082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3082
  have eq3357 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq3349
       have i₂ := eq2265 x
       grind)
    | exact superpose eq2265 eq3349
    | exact resolve eq3349 eq2265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2265 eq3349
  have eq3358 : False := by grind
  exact eq3358

/-- `Equation1060`: `x = x ◇ ((y ◇ (z ◇ y)) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_pxx_pxy_Equation1060 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1060 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law1060.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X1)) = X0 := by
    intro X0 X1 X2
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq20 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq22 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X0 (M.op X0 (M.op x X0))
       have i₂ := eq8 X0 X0 x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (M.op X0 X0)
       have i₂ := eq22 X0 (M.op X0 X0)
       grind)
    | exact superpose eq22 eq11
    | (have j0 := eq11 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq11 X0 (M.op X0 X0)
       have r₂ := eq22 X0 (M.op X0 X0)
       grind)
    | exact resolve eq11 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq54 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X0) = (k X2 X0) := by
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
  have eq57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq15
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq15 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq59 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq54 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq89 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq227 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq89 X0 (M.op X1 X1)
       have i₂ := eq35 X1 (σ X0)
       grind)
    | exact superpose eq35 eq89
    | exact resolve eq89 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq286 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq59 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq333 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ (σ (k X2 X0)) = (M.op (σ X2) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 (σ X0) X1
       have i₂ := eq57 X2 X0
       grind)
    | exact superpose eq57 eq22
    | (have j1 := eq57 X2 X0
       grind)
    | exact resolve eq22 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq548 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) ≠ (k X0 (M.op X1 X1)) ∨ (k X0 (M.op X1 X1)) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq286 X1 X1
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq286
    | exact resolve eq286 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq559 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq286 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286
  have eq562 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq548 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548
  have eq582 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq559 (σ X0)
       grind)
    | exact superpose eq559 eq13
    | exact resolve eq13 eq559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq594 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq582 X0
       have i₂ := eq559 X0
       grind)
    | exact superpose eq559 eq582
    | exact resolve eq582 eq559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582
  have eq710 : ∀ X0 X1 : G, (τ (k (σ X0) (M.op X1 X1))) = (k (τ (σ X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq20 (σ X0) X0
       have i₂ := eq562 (σ X0) X1
       grind)
    | exact superpose eq562 eq20
    | exact resolve eq20 eq562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq562
  have eq713 : ∀ X0 X1 : G, (k X0 X0) = (τ (k (σ X0) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq710 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq710
    | exact resolve eq710 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710
  have eq729 : ∀ X0 X1 : G, (k X0 X0) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq713 X0 X1
       have i₂ := eq89 X0 (M.op X1 X1)
       grind)
    | exact superpose eq89 eq713
    | exact resolve eq713 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq713
  have eq901 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq58 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq58
    | (have j0 := eq58 X0 X1
       grind)
    | exact resolve eq58 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq983 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq901 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq901
    | (have j0 := eq901 X0 X1
       grind)
    | exact resolve eq901 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901
  have eq1132 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X0) X1
       have i₂ := eq594 X0
       grind)
    | exact superpose eq594 eq22
    | exact resolve eq22 eq594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594
  have eq2458 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq333 y X0 x
       grind)
    | exact superpose eq333 eq14
    | (have j1 := eq333 y X0 x
       grind)
    | exact resolve eq14 eq333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333
  have eq68143 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op X0 (σ y)) = X0 ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq2458 X0
       have i₂ := eq983 x y
       grind)
    | exact superpose eq983 eq2458
    | (have j0 := eq2458 X0
       have j1 := eq983 X0 y
       grind)
    | (have r₁ := eq2458 X0
       have r₂ := eq983 x y
       grind)
    | exact resolve eq2458 eq983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq983 eq2458
  have eq68144 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq68143 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68143
  have eq68378 : ∀ X0 : G, (τ (σ y)) = (k y (τ (M.op X0 X0))) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq227 y X0
       have i₂ := eq68144 (σ y)
       grind)
    | exact superpose eq68144 eq227
    | exact resolve eq227 eq68144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227 eq68144
  have eq68408 : (τ (σ y)) = (k y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq68378 x
       have i₂ := eq729 y x
       grind)
    | exact superpose eq729 eq68378
    | exact resolve eq68378 eq729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729 eq68378
  have eq68468 : (τ (σ y)) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq68408
       have i₂ := eq559 y
       grind)
    | exact superpose eq559 eq68408
    | exact resolve eq68408 eq559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559 eq68408
  have eq68480 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq68468
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq68468
    | exact resolve eq68468 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68468
  have eq68481 : y = (M.op y y) := by grind
  clear eq68480
  have eq68690 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq22 y X0
       have i₂ := eq68481
       grind)
    | exact superpose eq68481 eq22
    | exact resolve eq22 eq68481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq68747 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1132 y X0
       have i₂ := eq68481
       grind)
    | exact superpose eq68481 eq1132
    | exact resolve eq1132 eq68481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1132 eq68481
  have eq73251 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq68747 (σ x)
       grind)
    | exact superpose eq68747 eq14
    | exact resolve eq14 eq68747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68747
  have eq73290 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq73251
       have i₂ := eq68690 x
       grind)
    | exact superpose eq68690 eq73251
    | exact resolve eq73251 eq68690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68690 eq73251
  have eq73291 : False := by grind
  exact eq73291

/-- `Equation1060`: `x = x ◇ ((y ◇ (z ◇ y)) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_pyy_pxy_Equation1060 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1060 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law1060.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X1)) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq22 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X0 (M.op X0 (M.op x X0))
       have i₂ := eq8 X0 X0 x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 (M.op X0 X0)
       have i₂ := eq22 X0 (M.op X0 X0)
       grind)
    | exact superpose eq22 eq11
    | (have r₁ := eq11 X0 (M.op X0 X0)
       have r₂ := eq22 X0 (M.op X0 X0)
       grind)
    | exact resolve eq11 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq54 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X0 ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq15
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq15 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 X2 : G, (k X1 X0) = X0 ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq54 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq65 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (M.op X0 X0)
       have i₂ := eq35 X0 (τ X1)
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq35
  have eq73 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq96 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (k X2 (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq59 (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq59 eq13
    | (have j1 := eq59 (σ X1) X2 X2
       grind)
    | exact resolve eq13 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq229 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq57 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq562 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq58 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq58
    | (have j0 := eq58 X0 X1
       grind)
    | exact resolve eq58 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq619 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq562 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq562
    | (have j0 := eq562 X0 X1
       grind)
    | exact resolve eq562 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq1228 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq229 (τ X0)
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq229
    | (have j0 := eq229 (τ X0)
       grind)
    | exact resolve eq229 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq229
  have eq1242 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1228 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1228
    | (have j0 := eq1228 X0
       grind)
    | exact resolve eq1228 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1228
  have eq1251 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1242 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1242
    | (have j0 := eq1242 X0
       grind)
    | exact resolve eq1242 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1242
  have eq1815 : ∀ X0 X1 X2 : G, (σ X0) = (k X1 (σ X0)) ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq65 X1 X1
       have i₂ := eq619 X0 X1
       grind)
    | exact superpose eq619 eq65
    | (have j1 := eq619 X2 X0
       grind)
    | exact resolve eq65 eq619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq619
  have eq1893 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq96 x y X0
       grind)
    | exact superpose eq96 eq14
    | (have j1 := eq96 X0 y X0
       grind)
    | exact resolve eq14 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq1952 : ∀ X0 : G, (σ y) = (k X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq1893 X0
       have j1 := eq1815 y X0 x
       grind)
    | (have r₁ := eq1893 X0
       have r₂ := eq1815 y x x
       grind)
    | exact resolve eq1893 eq1815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1815 eq1893
  have eq1976 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1251 (σ y)
       have i₂ := eq1952 (σ y)
       grind)
    | exact superpose eq1952 eq1251
    | (have j0 := eq1251 (σ y)
       grind)
    | (have r₁ := eq1251 (σ y)
       have r₂ := eq1952 (σ y)
       grind)
    | exact resolve eq1251 eq1952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1989 : ∀ X0 : G, (τ (σ y)) = (k X0 (τ (σ y))) := by
    intro X0
    first
    | (have i₁ := eq73 X0 (σ y)
       have i₂ := eq1952 (σ X0)
       grind)
    | exact superpose eq1952 eq73
    | exact resolve eq73 eq1952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq1952
  have eq1994 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq1976
  have eq1995 : ∀ X0 : G, y = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq1989 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1989
    | exact resolve eq1989 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1989
  have eq2115 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1251 y
       have i₂ := eq1995 y
       grind)
    | exact superpose eq1995 eq1251
    | (have j0 := eq1251 y
       grind)
    | (have r₁ := eq1251 y
       have r₂ := eq1995 y
       grind)
    | exact resolve eq1251 eq1995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1251 eq1995
  have eq2130 : y = (M.op y y) := by grind
  clear eq2115
  have eq2263 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq22 y X0
       have i₂ := eq2130
       grind)
    | exact superpose eq2130 eq22
    | exact resolve eq22 eq2130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2130
  have eq3089 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq22 (σ y) X0
       have i₂ := eq1994
       grind)
    | exact superpose eq1994 eq22
    | exact resolve eq22 eq1994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1994
  have eq3337 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq3089 (σ x)
       grind)
    | exact superpose eq3089 eq14
    | exact resolve eq14 eq3089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3089
  have eq3345 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq3337
       have i₂ := eq2263 x
       grind)
    | exact superpose eq2263 eq3337
    | exact resolve eq3337 eq2263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2263 eq3337
  have eq3346 : False := by grind
  exact eq3346

/-- `Equation1061`: `x = x ◇ ((y ◇ (z ◇ y)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation1061 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1061 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law1061.models_iff G M).mp hM
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
  have eq53 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq59 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq136 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq59 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq140 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq136 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq136 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq136 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq136 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq159 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq140 (σ X0) (σ X1)
       grind)
    | exact superpose eq140 eq13
    | exact resolve eq13 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq168 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq159 X0 X1
       have i₂ := eq140 X0 X1
       grind)
    | exact superpose eq140 eq159
    | exact resolve eq159 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140 eq159
  have eq1402 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq168 x y
       grind)
    | exact superpose eq168 eq14
    | (have r₁ := eq14
       have r₂ := eq168 x y
       grind)
    | exact resolve eq14 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq1427 : False := by grind
  exact eq1427

/-- `Equation1076`: `x = y ◇ ((x ◇ (x ◇ y)) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pyx_pxx_pyx_Equation1076 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1076 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law1076.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq46 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
    | (have r₁ := eq11 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq86 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq90 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq86 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq86 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq86 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq86 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq106 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq90 (σ X1) (σ X0)
       grind)
    | exact superpose eq90 eq13
    | exact resolve eq13 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq106 X0 X1
       have i₂ := eq90 X1 X0
       grind)
    | exact superpose eq90 eq106
    | exact resolve eq106 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq106
  have eq1720 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq113 x y
       grind)
    | exact superpose eq113 eq14
    | (have r₁ := eq14
       have r₂ := eq113 x y
       grind)
    | exact resolve eq14 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq1739 : False := by grind
  exact eq1739

/-- `Equation108`: `x = x ◇ ((y ◇ y) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_pxx_pxy_Equation108 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law108 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law108.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X1) X1)) = X0 := by
    intro X0 X1
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq19 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq20 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq21 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (M.op X1 X1) = (k X1 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (M.op (M.op X0 X0) X0)
       have i₂ := eq8 (M.op (M.op X0 X0) X0) X0
       grind)
    | exact superpose eq8 eq11
    | (have j0 := eq11 X1 (M.op (M.op X0 X0) X0)
       grind)
    | (have r₁ := eq11 X0 (M.op (M.op X1 X1) X1)
       have r₂ := eq8 (M.op (M.op X1 X1) X1) X1
       grind)
    | exact resolve eq11 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq21 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq9
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
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
  have eq31 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq19
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq19 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq32 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq28 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq39 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq9
    | exact resolve eq9 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq50 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op X1 X1) X1)) = X0 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 X0
       have i₂ := eq22 X1 X0
       grind)
    | exact superpose eq22 eq12
    | (have j0 := eq12 X2 X0
       grind)
    | exact resolve eq12 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq26
    | exact resolve eq26 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq132 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 X2) = (k X2 (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq32 (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq32 eq13
    | (have j1 := eq32 (σ X1) X2 X2
       grind)
    | exact resolve eq13 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq32 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq245 : ∀ X0 X1 : G, (k X0 (M.op (M.op X1 X1) X1)) ≠ (k X0 (M.op (M.op X1 X1) X1)) ∨ (k X0 (M.op (M.op X1 X1) X1)) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq138 X1 X1
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq138
    | exact resolve eq138 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq249 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq138 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq252 : ∀ X0 X1 : G, (k X0 (M.op (M.op X1 X1) X1)) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq245 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245
  have eq261 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq249 (σ X0)
       grind)
    | exact superpose eq249 eq13
    | exact resolve eq13 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq273 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq261 X0
       have i₂ := eq249 X0
       grind)
    | exact superpose eq249 eq261
    | exact resolve eq261 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261
  have eq381 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 X0)) (σ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 (σ X0)
       have i₂ := eq273 X0
       grind)
    | exact superpose eq273 eq8
    | exact resolve eq8 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq479 : ∀ X0 X1 : G, (τ (k (σ X0) (M.op (M.op X1 X1) X1))) = (k X0 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq39 X0 (σ X0)
       have i₂ := eq252 (σ X0) X1
       grind)
    | (have i₁ := eq39 X0 (M.op (M.op X1 X1) X1)
       have i₂ := eq252 (σ X0) X1
       grind)
    | exact superpose eq252 eq39
    | exact resolve eq39 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252
  have eq484 : ∀ X0 X1 : G, (k X0 X0) = (τ (k (σ X0) (M.op (M.op X1 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq479 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq479
    | exact resolve eq479 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479
  have eq508 : ∀ X0 X1 : G, (k X0 X0) = (k X0 (τ (M.op (M.op X1 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq484 X0 X1
       have i₂ := eq39 X0 (M.op (M.op X1 X1) X1)
       grind)
    | exact superpose eq39 eq484
    | exact resolve eq484 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484
  have eq521 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq31 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq31
    | (have j0 := eq31 X0 X1
       grind)
    | exact resolve eq31 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq582 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq521 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq521
    | (have j0 := eq521 X0 X1
       grind)
    | exact resolve eq521 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521
  have eq827 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op (M.op X0 X0) X0)) (σ (M.op (M.op X0 X0) X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq381 (M.op (M.op X0 X0) X0) X1
       have i₂ := eq8 (M.op (M.op X0 X0) X0) X0
       grind)
    | exact superpose eq8 eq381
    | exact resolve eq381 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381
  have eq897 : ∀ X0 X1 : G, (M.op X1 (σ (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq827 X0 X1
       have i₂ := eq273 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq273 eq827
    | exact resolve eq827 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827
  have eq906 : ∀ X0 X1 : G, (M.op X1 (σ (M.op (M.op X0 X0) X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq897 X0 X1
       have i₂ := eq8 (M.op (M.op X0 X0) X0) X0
       grind)
    | exact superpose eq8 eq897
    | exact resolve eq897 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq897
  have eq2078 : ∀ X0 X1 : G, (τ (k X0 X0)) = (k (τ X0) (τ (M.op (M.op X1 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq58 X0 X0
       have i₂ := eq508 (τ X0) X1
       grind)
    | (have i₁ := eq58 (M.op (M.op X1 X1) X1) X1
       have i₂ := eq508 (τ X1) X1
       grind)
    | exact superpose eq508 eq58
    | exact resolve eq58 eq508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508
  have eq2098 : ∀ X0 X1 : G, (τ (k X0 X0)) = (τ (k X0 (M.op (M.op X1 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2078 X0 X1
       have i₂ := eq58 (M.op (M.op X1 X1) X1) X0
       grind)
    | exact superpose eq58 eq2078
    | exact resolve eq2078 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq2078
  have eq2142 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (τ (k X0 (M.op (M.op X1 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2098 X0 X1
       have i₂ := eq249 X0
       grind)
    | exact superpose eq249 eq2098
    | exact resolve eq2098 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249 eq2098
  have eq9409 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq132 x y X0
       grind)
    | exact superpose eq132 eq14
    | (have j1 := eq132 X0 y X0
       grind)
    | exact resolve eq14 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq10654 : ∀ X0 X2 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X2
    first
    | (have i₁ := eq2142 X0 x
       have i₂ := eq50 X0 x X2
       grind)
    | exact superpose eq50 eq2142
    | (have j1 := eq50 X0 x X2
       grind)
    | exact resolve eq2142 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq2142
  have eq45954 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (σ (M.op X0 X0))) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10654 (σ X0) X1
       have i₂ := eq273 X0
       grind)
    | exact superpose eq273 eq10654
    | (have j0 := eq10654 (σ X0) X1
       grind)
    | exact resolve eq10654 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10654
  have eq46313 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq45954 X0 X1
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq45954
    | (have j0 := eq45954 X0 X1
       grind)
    | exact resolve eq45954 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45954
  have eq46388 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq46313 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq46313
    | (have j0 := eq46313 X0 X1
       grind)
    | exact resolve eq46313 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46313
  have eq85053 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op X0 X0) = (k X0 (σ y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq9409 X0
       have i₂ := eq582 x y
       grind)
    | exact superpose eq582 eq9409
    | (have j0 := eq9409 X0
       have j1 := eq582 X0 y
       grind)
    | (have r₁ := eq9409 X0
       have r₂ := eq582 x y
       grind)
    | exact resolve eq9409 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9409
  have eq85054 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq85053 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85053
  have eq85482 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq46388 y X0
       have i₂ := eq85054 X0
       grind)
    | exact superpose eq85054 eq46388
    | (have j0 := eq46388 y x
       grind)
    | exact resolve eq46388 eq85054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46388
  have eq85537 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ y))) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq39 X0 (σ y)
       have i₂ := eq85054 (σ X0)
       grind)
    | exact superpose eq85054 eq39
    | exact resolve eq39 eq85054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq85054
  have eq85548 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (σ y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq85482 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85482
  have eq85558 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 y) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq85537 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq85537
    | exact resolve eq85537 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85537
  have eq85741 : ∀ X0 : G, (τ (σ (M.op X0 X0))) = (k X0 y) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq85558 X0
       have i₂ := eq273 X0
       grind)
    | exact superpose eq273 eq85558
    | exact resolve eq85558 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85558
  have eq85792 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq85741 X0
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq85741
    | exact resolve eq85741 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85741
  have eq85807 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq85792 X0
       have j1 := eq11 X0 y
       grind)
    | (have r₁ := eq85792 X0
       have r₂ := eq11 X0 y
       grind)
    | exact resolve eq85792 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85792
  have eq87734 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) y) := by
    intro X0
    first
    | (have i₁ := eq273 X0
       have i₂ := eq85807 (σ X0)
       grind)
    | exact superpose eq85807 eq273
    | exact resolve eq273 eq85807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273
  have eq87825 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (M.op X0 y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq582 X0 y
       have i₂ := eq85807 X0
       grind)
    | exact superpose eq85807 eq582
    | (have j0 := eq582 X0 y
       grind)
    | exact resolve eq582 eq85807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582
  have eq195703 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq85548 (σ x)
       grind)
    | exact superpose eq85548 eq14
    | exact resolve eq14 eq85548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85548
  have eq195707 : (σ (M.op x y)) ≠ (k (σ x) y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq195703
       have i₂ := eq85807 (σ x)
       grind)
    | exact superpose eq85807 eq195703
    | exact resolve eq195703 eq85807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85807 eq195703
  have eq195756 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq195707
       have i₂ := eq87734 x
       grind)
    | exact superpose eq87734 eq195707
    | exact resolve eq195707 eq87734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87734 eq195707
  have eq195764 : y = (M.op y y) := by
    first
    | (have r₁ := eq195756
       have r₂ := eq87825 x
       grind)
    | exact resolve eq195756 eq87825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87825 eq195756
  have eq196762 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq8 X0 y
       have i₂ := eq195764
       grind)
    | exact superpose eq195764 eq8
    | exact resolve eq8 eq195764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196826 : ∀ X0 : G, (M.op X0 (σ (M.op y y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq906 y X0
       have i₂ := eq195764
       grind)
    | exact superpose eq195764 eq906
    | exact resolve eq906 eq195764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906
  have eq197035 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq196826 X0
       have i₂ := eq195764
       grind)
    | exact superpose eq195764 eq196826
    | exact resolve eq196826 eq195764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196826
  have eq197083 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq196762 X0
       have i₂ := eq195764
       grind)
    | exact superpose eq195764 eq196762
    | exact resolve eq196762 eq195764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195764 eq196762
  have eq200411 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq197035 (σ x)
       grind)
    | exact superpose eq197035 eq14
    | exact resolve eq14 eq197035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197035
  have eq201080 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq200411
       have i₂ := eq197083 x
       grind)
    | exact superpose eq197083 eq200411
    | exact resolve eq200411 eq197083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197083 eq200411
  have eq201081 : False := by grind
  exact eq201081

/-- `Equation109`: `x = x ◇ ((y ◇ y) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_x_pxx_pyx_Equation109 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law109 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law109.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X1) X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X0 (M.op (M.op x x) x)
       have i₂ := eq8 (M.op X0 X0) x x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq18 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq9
    | exact resolve eq9 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq28 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 X0) X1
       have i₂ := eq16 X0 (M.op X0 X0)
       grind)
    | exact superpose eq16 eq11
    | (have r₁ := eq11 (M.op X0 X0) X1
       have r₂ := eq16 X0 (M.op X0 X0)
       grind)
    | exact resolve eq11 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq28 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq41 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X1) X1
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq12 X1 (τ X0)
       grind)
    | exact superpose eq12 eq18
    | (have j1 := eq12 X1 X1
       grind)
    | exact resolve eq18 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k (τ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq26 (M.op X0 X0) X1
       have i₂ := eq29 X0 (σ X1)
       grind)
    | exact superpose eq29 eq26
    | exact resolve eq26 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq204 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ (M.op (σ X2) (σ X0)) = (σ (k X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (σ X0) X1
       have i₂ := eq41 X2 X0
       grind)
    | exact superpose eq41 eq16
    | (have j1 := eq41 X2 X0
       grind)
    | exact resolve eq16 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq209 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq41 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq667 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq46 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq46
    | (have j0 := eq46 X0 X1
       grind)
    | exact resolve eq46 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq723 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq667 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq667
    | (have j0 := eq667 X0 X1
       grind)
    | exact resolve eq667 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667
  have eq936 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X1 ∨ (σ (k X0 X2)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq723 X2 X0
       grind)
    | exact superpose eq723 eq16
    | (have j1 := eq723 X2 X0
       grind)
    | exact resolve eq16 eq723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723
  have eq1921 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq209 (M.op X0 X0)
       have i₂ := eq29 X0 (M.op X0 X0)
       grind)
    | exact superpose eq29 eq209
    | (have j0 := eq209 (M.op X0 X0)
       grind)
    | exact resolve eq209 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq1936 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq209 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq209
    | (have j0 := eq209 (τ X0)
       grind)
    | exact resolve eq209 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq209
  have eq1951 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq1921 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1921
  have eq1959 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1936 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1936
    | (have j0 := eq1936 X0
       grind)
    | exact resolve eq1936 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1936
  have eq1968 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1959 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1959
    | (have j0 := eq1959 X0
       grind)
    | exact resolve eq1959 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1959
  have eq2154 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 (σ (M.op X0 X0)) X1
       have i₂ := eq1951 X0
       grind)
    | exact superpose eq1951 eq16
    | exact resolve eq16 eq1951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1951
  have eq2312 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ (σ (k X0 X2)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2154 X0 X1
       have i₂ := eq936 X0 X0 X2
       grind)
    | exact superpose eq936 eq2154
    | (have j1 := eq936 (σ X0) X1 X2
       grind)
    | exact resolve eq2154 eq936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936 eq2154
  have eq2790 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq204 y X0 x
       grind)
    | exact superpose eq204 eq14
    | (have j1 := eq204 y X0 x
       grind)
    | exact resolve eq14 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq2828 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq2790 X0
       have j1 := eq2312 y X0 x
       grind)
    | (have r₁ := eq2790 X0
       have r₂ := eq2312 y x x
       grind)
    | exact resolve eq2790 eq2312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2312 eq2790
  have eq2845 : ∀ X0 : G, (τ (σ y)) = (k (τ (σ y)) X0) := by
    intro X0
    first
    | (have i₁ := eq76 (σ y) x
       have i₂ := eq2828 (σ y)
       grind)
    | exact superpose eq2828 eq76
    | exact resolve eq76 eq2828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq2870 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq2828 (σ x)
       grind)
    | exact superpose eq2828 eq14
    | exact resolve eq14 eq2828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2828
  have eq2879 : ∀ X0 : G, y = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq2845 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq2845
    | exact resolve eq2845 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2845
  have eq2990 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1968 y
       have i₂ := eq2879 y
       grind)
    | exact superpose eq2879 eq1968
    | (have j0 := eq1968 y
       grind)
    | (have r₁ := eq1968 y
       have r₂ := eq2879 y
       grind)
    | exact resolve eq1968 eq2879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1968 eq2879
  have eq3011 : y = (M.op y y) := by grind
  clear eq2990
  have eq3166 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 y X0
       have i₂ := eq3011
       grind)
    | exact superpose eq3011 eq16
    | exact resolve eq16 eq3011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq3011
  have eq3667 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq2870
       have i₂ := eq3166 x
       grind)
    | exact superpose eq3166 eq2870
    | exact resolve eq2870 eq3166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2870 eq3166
  have eq3668 : False := by grind
  exact eq3668
