import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation105`: `x = x ◇ ((y ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation105 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law105 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law105.models_iff G M).mp hM
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
  have eq29 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq29 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq84 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
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
  have eq1161 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
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
  have eq1180 : False := by grind
  exact eq1180

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

`x □ y = if m(Y,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_pyy_pxy_Equation109 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law109 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law109.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
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
  have eq28 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 (M.op X0 X0)
       have i₂ := eq16 X0 (M.op X0 X0)
       grind)
    | exact superpose eq16 eq11
    | (have r₁ := eq11 X0 (M.op X0 X0)
       have r₂ := eq16 X0 (M.op X0 X0)
       grind)
    | exact resolve eq11 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq28 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq41 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq42 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq17
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq17 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq51 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq104 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X1 (M.op X0 X0)
       have i₂ := eq29 X0 (σ X1)
       grind)
    | exact superpose eq29 eq51
    | exact resolve eq51 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq204 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ (σ (k X2 X0)) = (M.op (σ X2) (σ X0)) := by
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
  have eq649 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq42 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq42
    | (have j0 := eq42 X0 X1
       grind)
    | exact resolve eq42 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq705 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq649 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq649
    | (have j0 := eq649 X0 X1
       grind)
    | exact resolve eq649 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649
  have eq921 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X1 ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq705 X2 X0
       grind)
    | exact superpose eq705 eq16
    | (have j1 := eq705 X2 X0
       grind)
    | exact resolve eq16 eq705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705
  have eq1920 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
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
  have eq1952 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq1920 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1920
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
       have i₂ := eq1952 X0
       grind)
    | exact superpose eq1952 eq16
    | exact resolve eq16 eq1952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1952
  have eq2312 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2154 X0 X1
       have i₂ := eq921 X0 X0 X2
       grind)
    | exact superpose eq921 eq2154
    | (have j1 := eq921 (σ X0) X1 X2
       grind)
    | exact resolve eq2154 eq921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921 eq2154
  have eq2790 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op X0 (σ y)) = X0 := by
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
  have eq2845 : ∀ X0 : G, (τ (σ y)) = (k X0 (τ (σ y))) := by
    intro X0
    first
    | (have i₁ := eq104 (σ y) x
       have i₂ := eq2828 (σ y)
       grind)
    | exact superpose eq2828 eq104
    | exact resolve eq104 eq2828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
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
  have eq2879 : ∀ X0 : G, y = (k X0 y) := by
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
  have eq2988 : y ≠ y ∨ y = (M.op y y) := by
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
  have eq3009 : y = (M.op y y) := by grind
  clear eq2988
  have eq3162 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 y X0
       have i₂ := eq3009
       grind)
    | exact superpose eq3009 eq16
    | exact resolve eq16 eq3009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq3009
  have eq3663 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq2870
       have i₂ := eq3162 x
       grind)
    | exact superpose eq3162 eq2870
    | exact resolve eq2870 eq3162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2870 eq3162
  have eq3664 : False := by grind
  exact eq3664

/-- `Equation111`: `x = x ◇ ((y ◇ z) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_pxx_pxy_Equation111 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law111 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law111.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) X1)) = X0 := by
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
  have eq15 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X0 (M.op (M.op x x) x)
       have i₂ := eq8 X0 x x
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
  have eq33 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (M.op X0 X0)
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq11
    | (have j0 := eq11 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq11 X0 (M.op X0 X0)
       have r₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact resolve eq11 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq60 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
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
  have eq64 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq66 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq60 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq87 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq17
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq17 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq97 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  clear eq18
  have eq183 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq97 X0 (M.op X1 X1)
       have i₂ := eq36 X1 (σ X0)
       grind)
    | exact superpose eq36 eq97
    | exact resolve eq97 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq243 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq66 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq290 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ (σ (k X2 X0)) = (M.op (σ X2) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (σ X0) X1
       have i₂ := eq64 X2 X0
       grind)
    | exact superpose eq64 eq15
    | (have j1 := eq64 X2 X0
       grind)
    | exact resolve eq15 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq908 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) ≠ (k X0 (M.op X1 X1)) ∨ (k X0 (M.op X1 X1)) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq243 X1 X1
       have i₂ := eq36 X0 X1
       grind)
    | exact superpose eq36 eq243
    | exact resolve eq243 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq920 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq243 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq922 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq908 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq908
  have eq957 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq920 (σ X0)
       grind)
    | exact superpose eq920 eq13
    | exact resolve eq13 eq920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq964 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq957 X0
       have i₂ := eq920 X0
       grind)
    | exact superpose eq920 eq957
    | exact resolve eq957 eq920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq957
  have eq1110 : ∀ X0 X1 : G, (τ (k (σ X0) (M.op X1 X1))) = (k X0 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq97 X0 (σ X0)
       have i₂ := eq922 (σ X0) X1
       grind)
    | (have i₁ := eq97 X0 (M.op X1 X1)
       have i₂ := eq922 (σ X0) X1
       grind)
    | exact superpose eq922 eq97
    | exact resolve eq97 eq922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq922
  have eq1115 : ∀ X0 X1 : G, (k X0 X0) = (τ (k (σ X0) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1110 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1110
    | exact resolve eq1110 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1110
  have eq1131 : ∀ X0 X1 : G, (k X0 X0) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1115 X0 X1
       have i₂ := eq97 X0 (M.op X1 X1)
       grind)
    | exact superpose eq97 eq1115
    | exact resolve eq1115 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq1115
  have eq1136 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq87 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq87
    | (have j0 := eq87 X0 X1
       grind)
    | exact resolve eq87 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq1224 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1136 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq1136
    | (have j0 := eq1136 X0 X1
       grind)
    | exact resolve eq1136 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1136
  have eq1613 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 (σ X0) X1
       have i₂ := eq964 X0
       grind)
    | exact superpose eq964 eq15
    | exact resolve eq15 eq964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq964
  have eq6533 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq290 y X0 x
       grind)
    | exact superpose eq290 eq14
    | (have j1 := eq290 y X0 x
       grind)
    | exact resolve eq14 eq290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq89700 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op X0 (σ y)) = X0 ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq6533 X0
       have i₂ := eq1224 x y
       grind)
    | exact superpose eq1224 eq6533
    | (have j0 := eq6533 X0
       have j1 := eq1224 X0 y
       grind)
    | (have r₁ := eq6533 X0
       have r₂ := eq1224 x y
       grind)
    | exact resolve eq6533 eq1224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1224 eq6533
  have eq89701 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq89700 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89700
  have eq89993 : ∀ X0 : G, (τ (σ y)) = (k y (τ (M.op X0 X0))) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq183 y X0
       have i₂ := eq89701 (σ y)
       grind)
    | exact superpose eq89701 eq183
    | exact resolve eq183 eq89701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq89701
  have eq90037 : (τ (σ y)) = (k y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq89993 x
       have i₂ := eq1131 y x
       grind)
    | exact superpose eq1131 eq89993
    | exact resolve eq89993 eq1131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1131 eq89993
  have eq90102 : (τ (σ y)) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq90037
       have i₂ := eq920 y
       grind)
    | exact superpose eq920 eq90037
    | exact resolve eq90037 eq920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq920 eq90037
  have eq90113 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq90102
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq90102
    | exact resolve eq90102 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90102
  have eq90114 : y = (M.op y y) := by grind
  clear eq90113
  have eq90355 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq15 y X0
       have i₂ := eq90114
       grind)
    | exact superpose eq90114 eq15
    | exact resolve eq15 eq90114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq90422 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1613 y X0
       have i₂ := eq90114
       grind)
    | exact superpose eq90114 eq1613
    | exact resolve eq1613 eq90114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1613 eq90114
  have eq95377 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq90422 (σ x)
       grind)
    | exact superpose eq90422 eq14
    | exact resolve eq14 eq90422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90422
  have eq95430 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq95377
       have i₂ := eq90355 x
       grind)
    | exact superpose eq90355 eq95377
    | exact resolve eq95377 eq90355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90355 eq95377
  have eq95431 : False := by grind
  exact eq95431

/-- `Equation115`: `x = y ◇ ((x ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation115 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law115 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law115.models_iff G M).mp hM
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
  have eq30 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq33 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq30 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq112 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq116 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq112 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq112 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq112 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq112 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq132 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq116 (σ X0) (σ X1)
       grind)
    | exact superpose eq116 eq13
    | exact resolve eq13 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq132 X0 X1
       have i₂ := eq116 X0 X1
       grind)
    | exact superpose eq116 eq132
    | exact resolve eq132 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq132
  have eq1246 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq139 x y
       grind)
    | exact superpose eq139 eq14
    | (have r₁ := eq14
       have r₂ := eq139 x y
       grind)
    | exact resolve eq14 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq1267 : False := by grind
  exact eq1267

/-- `Equation124`: `x = y ◇ ((y ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation124 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law124 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law124.models_iff G M).mp hM
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
  have eq29 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq29 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq84 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
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
  have eq1463 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
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
  have eq1484 : False := by grind
  exact eq1484

/-- `Equation138`: `x = y ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation138 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law138 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law138.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
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
  have eq15 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X3 (M.op (M.op X1 X2) X0) X2
       have i₂ := eq8 X0 X2 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq20 (σ X0)
       grind)
    | exact superpose eq20 eq13
    | exact resolve eq13 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq22 X0
       have i₂ := eq20 X0
       grind)
    | exact superpose eq20 eq22
    | exact resolve eq22 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq22
  have eq31 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq34 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq35 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq31 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq37 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq34
    | (have j0 := eq34 X0 X1
       grind)
    | exact resolve eq34 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq90 : ∀ X0 X1 X4 : G, (M.op (M.op X1 X0) (M.op X0 X4)) = X4 := by
    intro X0 X1 X4
    first
    | (have i₁ := eq8 X4 (M.op X1 X0) (M.op (M.op x x) X1)
       have i₂ := eq15 X1 x x X0
       grind)
    | exact superpose eq15 eq8
    | exact resolve eq8 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq218 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq222 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq218 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq218 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq218 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq218 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq242 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq222 (σ X0) (σ X1)
       grind)
    | exact superpose eq222 eq13
    | exact resolve eq13 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq249 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq242 X0 X1
       have i₂ := eq222 X0 X1
       grind)
    | exact superpose eq222 eq242
    | exact resolve eq242 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242
  have eq529 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq37 x y
       grind)
    | exact superpose eq37 eq14
    | (have j1 := eq37 x y
       grind)
    | exact resolve eq14 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq556 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq529
       have i₂ := eq222 x y
       grind)
    | exact superpose eq222 eq529
    | exact resolve eq529 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222 eq529
  have eq557 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq556
  have eq605 : (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq557
       have i₂ := eq249 x y
       grind)
    | exact superpose eq249 eq557
    | exact resolve eq557 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249 eq557
  have eq715 : (M.op x y) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq9 (M.op x y)
       have i₂ := eq605
       grind)
    | exact superpose eq605 eq9
    | exact resolve eq9 eq605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605
  have eq734 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq715
       have i₂ := eq9 (M.op x x)
       grind)
    | exact superpose eq9 eq715
    | exact resolve eq715 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715
  have eq871 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq90 x X0 y
       have i₂ := eq734
       grind)
    | exact superpose eq734 eq90
    | exact resolve eq90 eq734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734
  have eq873 : x = y := by
    first
    | (have i₁ := eq871 x
       have i₂ := eq90 x x x
       grind)
    | (have i₁ := eq871 x
       have i₂ := eq90 x x (M.op (M.op x x) (M.op x x))
       grind)
    | exact superpose eq90 eq871
    | exact resolve eq871 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq871
  have eq915 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq873
       grind)
    | exact superpose eq873 eq14
    | exact resolve eq14 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873
  have eq916 : False := by grind
  exact eq916
