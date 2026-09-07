import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation452`: `x = x ◇ (y ◇ (z ◇ (y ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation452 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law452 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law452.models_iff G M).mp hM
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
  have eq52 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq58 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq96 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq58 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq100 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq96 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq96 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq96 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq96 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq116 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq100 (σ X0) (σ X1)
       grind)
    | exact superpose eq100 eq13
    | exact resolve eq13 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq116 X0 X1
       have i₂ := eq100 X0 X1
       grind)
    | exact superpose eq100 eq116
    | exact resolve eq116 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq116
  have eq1160 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq123 x y
       grind)
    | exact superpose eq123 eq14
    | (have r₁ := eq14
       have r₂ := eq123 x y
       grind)
    | exact resolve eq14 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq1183 : False := by grind
  exact eq1183

/-- `Equation455`: `x = x ◇ (y ◇ (z ◇ (z ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxy_x_pyy_pxy_Equation455 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law455 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law455.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X2 X1)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
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
  have eq23 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 (M.op X0 X0) X0
       have i₂ := eq8 (M.op X0 X0) X0 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 (M.op X1 (M.op X2 (M.op X2 X1)))) = (M.op (M.op X1 (M.op X2 (M.op X2 X1))) (M.op X1 (M.op X2 (M.op X2 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X0 (M.op X1 (M.op X2 (M.op X2 X1)))
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq11
    | (have j0 := eq11 X0 (M.op X1 (M.op X2 (M.op X2 X1)))
       grind)
    | (have r₁ := eq11 X0 (M.op X1 (M.op X2 (M.op X2 X1)))
       have r₂ := eq8 X0 X1 X2
       grind)
    | exact resolve eq11 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (M.op X1 X1)) = (M.op (M.op X1 X1) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 (M.op X1 X1)
       have i₂ := eq23 X1 X0
       grind)
    | exact superpose eq23 eq11
    | (have j0 := eq11 X0 (M.op X1 X1)
       grind)
    | (have r₁ := eq11 X1 (M.op X0 X0)
       have r₂ := eq23 X0 X1
       grind)
    | exact resolve eq11 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) = (M.op (M.op X1 X1) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq31 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq33 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 (M.op X2 (M.op X2 X1)))) = (M.op (M.op X1 (M.op X2 (M.op X2 X1))) (M.op X1 (M.op X2 (M.op X2 X1)))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq30 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq34 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X0 X1
       have i₂ := eq23 X1 (M.op X1 X1)
       grind)
    | exact superpose eq23 eq32
    | exact resolve eq32 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq35 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X2 X1))) = (k X0 (M.op X1 (M.op X2 (M.op X2 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33 X0 X1 X2
       have i₂ := eq8 (M.op X1 (M.op X2 (M.op X2 X1))) X1 X2
       grind)
    | exact superpose eq8 eq33
    | exact resolve eq33 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq41 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq50 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq76 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq20
    | exact resolve eq20 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq93 : ∀ X0 X1 X2 : G, (σ (M.op X0 (M.op X1 (M.op X1 X0)))) = (k X2 (σ (M.op X0 (M.op X1 (M.op X1 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (M.op X0 (M.op X1 (M.op X1 X0)))
       have i₂ := eq35 (τ X2) X0 X1
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq102 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq50 X1 (M.op X0 X0)
       have i₂ := eq34 (σ X1) X0
       grind)
    | exact superpose eq34 eq50
    | exact resolve eq50 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq119 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq41 x y
       grind)
    | exact superpose eq41 eq14
    | (have j1 := eq41 x y
       grind)
    | exact resolve eq14 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq41 X0 X1
       grind)
    | exact superpose eq41 eq11
    | (have j0 := eq11 (σ X0) (σ X1)
       have j1 := eq41 X0 X1
       grind)
    | (have r₁ := eq11 (σ X0) (σ X1)
       have r₂ := eq41 X0 X1
       grind)
    | exact resolve eq11 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : ∀ X0 X1 : G, (σ (k X0 X0)) = (k X1 (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 (σ X1)
       have i₂ := eq41 X1 X1
       grind)
    | exact superpose eq41 eq34
    | (have j1 := eq41 X0 X0
       grind)
    | exact resolve eq34 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq126 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq41 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq127 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq122 X0 X1
       have j1 := eq11 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq122 X0 X1
       have r₂ := eq11 (σ X0) (σ X1)
       grind)
    | exact resolve eq122 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq130 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq127 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq127
    | (have j0 := eq127 X0 X1
       grind)
    | exact resolve eq127 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq337 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq126 (τ X0) (τ X1)
       have i₂ := eq76 X1 X0
       grind)
    | exact superpose eq76 eq126
    | (have j0 := eq126 (τ X0) (τ X1)
       grind)
    | exact resolve eq126 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq344 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq337 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq337
    | (have j0 := eq337 X0 X1
       grind)
    | exact resolve eq337 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337
  have eq348 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq344 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq344
    | (have j0 := eq344 X0 X1
       grind)
    | exact resolve eq344 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344
  have eq351 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq348 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq348
    | (have j0 := eq348 X0 X1
       grind)
    | exact resolve eq348 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348
  have eq352 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq351 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq351
    | (have j0 := eq351 X0 X1
       grind)
    | exact resolve eq351 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351
  have eq523 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq119
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq119
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq119 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq524 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq523
  have eq530 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ x) (σ x)))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq8 X0 (σ y) (σ x)
       have i₂ := eq524
       grind)
    | exact superpose eq524 eq8
    | exact resolve eq8 eq524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524
  have eq532 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq530 X0
       have i₂ := eq23 (σ x) (σ y)
       grind)
    | exact superpose eq23 eq530
    | exact resolve eq530 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530
  have eq546 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq130 (τ X1) (τ X0)
       have i₂ := eq76 X0 X1
       grind)
    | exact superpose eq76 eq130
    | exact resolve eq130 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq130
  have eq553 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq546 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq546
    | (have j0 := eq546 X0 X1
       grind)
    | exact resolve eq546 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546
  have eq556 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq553 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq553
    | (have j0 := eq553 X0 X1
       grind)
    | exact resolve eq553 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553
  have eq559 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (k X0 X1))) ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq556 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq556
    | (have j0 := eq556 X0 X1
       grind)
    | exact resolve eq556 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556
  have eq560 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq559 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq559
    | (have j0 := eq559 X0 X1
       grind)
    | exact resolve eq559 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559
  have eq564 : ∀ X0 : G, (τ (σ y)) = (k X0 (τ (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq102 (σ y) x
       have i₂ := eq532 (σ y)
       grind)
    | exact superpose eq532 eq102
    | exact resolve eq102 eq532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq532
  have eq577 : ∀ X0 : G, y = (k X0 y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq564 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq564
    | exact resolve eq564 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564
  have eq634 : ∀ X0 : G, y ≠ X0 ∨ (M.op X0 y) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq352 X0 y
       have i₂ := eq577 X0
       grind)
    | exact superpose eq577 eq352
    | (have j0 := eq352 X0 y
       grind)
    | (have r₁ := eq352 y y
       have r₂ := eq577 y
       grind)
    | exact resolve eq352 eq577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352 eq577
  have eq1385 : y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have j0 := eq634 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634
  have eq1470 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq23 y X0
       have i₂ := eq1385
       grind)
    | exact superpose eq1385 eq23
    | exact resolve eq23 eq1385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1385
  have eq1550 : x ≠ x ∨ x = (M.op x y) := by
    first
    | (have j0 := eq1470 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1470
  have eq1551 : x = (M.op x y) := by grind
  clear eq1550
  have eq1628 : ∀ X0 : G, (σ (M.op y (M.op x x))) = (k X0 (σ (M.op y (M.op x x)))) := by
    intro X0
    first
    | (have i₁ := eq93 y x x
       have i₂ := eq1551
       grind)
    | exact superpose eq1551 eq93
    | exact resolve eq93 eq1551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq1629 : ∀ X0 : G, (M.op y (M.op x x)) = (k X0 (M.op y (M.op x x))) := by
    intro X0
    first
    | (have i₁ := eq35 X0 y x
       have i₂ := eq1551
       grind)
    | exact superpose eq1551 eq35
    | exact resolve eq35 eq1551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq1632 : ∀ X0 : G, (M.op X0 (M.op y (M.op x x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq8 X0 y x
       have i₂ := eq1551
       grind)
    | exact superpose eq1551 eq8
    | exact resolve eq8 eq1551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1551
  have eq1634 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq1632 X0
       have i₂ := eq23 x y
       grind)
    | exact superpose eq23 eq1632
    | exact resolve eq1632 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1632
  have eq1635 : ∀ X0 : G, y = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq1629 X0
       have i₂ := eq23 x y
       grind)
    | exact superpose eq23 eq1629
    | exact resolve eq1629 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1629
  have eq1636 : ∀ X0 : G, (σ y) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1628 X0
       have i₂ := eq23 x y
       grind)
    | exact superpose eq23 eq1628
    | exact resolve eq1628 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1628
  have eq1960 : ∀ X0 : G, (σ y) ≠ X0 ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq560 X0 (σ y)
       have i₂ := eq1636 X0
       grind)
    | exact superpose eq1636 eq560
    | (have r₁ := eq560 (σ y) (σ y)
       have r₂ := eq1636 (σ y)
       grind)
    | exact resolve eq560 eq1636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560 eq1636
  have eq2601 : ∀ X0 : G, (σ y) = (k X0 (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq124 y x
       have i₂ := eq1635 y
       grind)
    | exact superpose eq1635 eq124
    | (have j0 := eq124 y x
       grind)
    | exact resolve eq124 eq1635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq1635
  have eq2673 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq2601 x
       have r₂ := eq1960 (k x (σ y))
       grind)
    | (have r₁ := eq2601 x
       have r₂ := eq1960 (M.op (σ y) (σ y))
       grind)
    | exact resolve eq2601 eq1960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1960 eq2601
  have eq2689 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq23 (σ y) X0
       have i₂ := eq2673
       grind)
    | exact superpose eq2673 eq23
    | exact resolve eq23 eq2673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq2673
  have eq2787 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq2689 (σ x)
       grind)
    | exact superpose eq2689 eq14
    | exact resolve eq14 eq2689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2689
  have eq2789 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq2787
       have i₂ := eq1634 x
       grind)
    | exact superpose eq1634 eq2787
    | exact resolve eq2787 eq1634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1634 eq2787
  have eq2790 : False := by grind
  exact eq2790

/-- `Equation508`: `x = y ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pxx_pxy_Equation508 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law508 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law508.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
  have eq19 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X1 (M.op X0 X0)
       have i₂ := eq8 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X1 X1) X0 X1
       have i₂ := eq19 (M.op X1 X1) X0
       grind)
    | exact superpose eq19 eq8
    | exact resolve eq8 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X1 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X2 X1
       have i₂ := eq12 X2 X0
       grind)
    | (have i₁ := eq19 X0 X1
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq19
    | (have j1 := eq12 X2 X0
       grind)
    | exact resolve eq19 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq73 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    grind
  have eq88 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq97 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op X0 X0)
       have i₂ := eq73 X0 (τ X1)
       grind)
    | exact superpose eq73 eq16
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq88 X1 (M.op X0 X0)
       have i₂ := eq73 X0 (σ X1)
       grind)
    | exact superpose eq73 eq88
    | exact resolve eq88 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq164 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 X0
       have i₂ := eq24 (σ X0) X1
       grind)
    | (have i₁ := eq37 X0 X0
       have i₂ := eq24 X0 (σ X0)
       grind)
    | exact superpose eq24 eq37
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq179 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
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
  have eq361 : ∀ X0 X1 : G, (σ (σ (M.op X0 X0))) = (k X1 (σ (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (σ (M.op X0 X0))
       have i₂ := eq97 X0 (τ X1)
       grind)
    | exact superpose eq97 eq16
    | exact resolve eq16 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq420 : ∀ X0 X1 : G, (τ (τ (M.op X0 X0))) = (k X1 (τ (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq88 X1 (τ (M.op X0 X0))
       have i₂ := eq141 X0 (σ X1)
       grind)
    | exact superpose eq141 eq88
    | exact resolve eq88 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq141
  have eq1017 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (σ (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq164 X1 (σ (M.op X0 X0))
       have i₂ := eq97 X0 (σ (M.op X0 X0))
       grind)
    | exact superpose eq97 eq164
    | (have j0 := eq164 X1 (σ (M.op X0 X0))
       grind)
    | exact resolve eq164 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq1018 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (σ (σ (M.op X0 X0)))) ∨ (M.op X1 X1) = (σ (σ (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq164 X1 (σ (σ (M.op X0 X0)))
       have i₂ := eq361 X0 (σ (σ (M.op X0 X0)))
       grind)
    | exact superpose eq361 eq164
    | (have j0 := eq164 X1 (σ (σ (M.op X0 X0)))
       grind)
    | exact resolve eq164 eq361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361
  have eq1020 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (τ (M.op X0 X0)))) ∨ (M.op X1 X1) = (σ (τ (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq164 X1 (τ (τ (M.op X0 X0)))
       have i₂ := eq420 X0 (τ (τ (M.op X0 X0)))
       grind)
    | exact superpose eq420 eq164
    | (have j0 := eq164 X1 (τ (τ (M.op X0 X0)))
       grind)
    | exact resolve eq164 eq420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164 eq420
  have eq1076 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have j0 := eq1020 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1020
  have eq1078 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (σ (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have j0 := eq1018 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1018
  have eq1079 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq1017 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1017
  have eq1102 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1076 X0 X1
       have i₂ := eq10 (τ (M.op X0 X0))
       grind)
    | exact superpose eq10 eq1076
    | exact resolve eq1076 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1076
  have eq2374 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq179
       have i₂ := eq31 y X0 x
       grind)
    | exact superpose eq31 eq179
    | (have j1 := eq31 y X0 x
       grind)
    | exact resolve eq179 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq179
  have eq2382 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ x)) ∨ (M.op X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq2374 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2374
  have eq13563 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (σ y)) ∨ (M.op X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1102 (σ x) X0
       have i₂ := eq2382 X1
       grind)
    | exact superpose eq2382 eq1102
    | (have j1 := eq2382 X1
       grind)
    | exact resolve eq1102 eq2382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2382
  have eq13621 : ∀ X0 X1 : G, (M.op X0 X0) = y ∨ (M.op X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13563 X0 X1
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq13563
    | (have j0 := eq13563 X0 X1
       grind)
    | exact resolve eq13563 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13563
  have eq14214 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have j0 := eq13621 y y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13621
  have eq14215 : y = (M.op y y) := by grind
  clear eq14214
  have eq14431 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq19 y X0
       have i₂ := eq14215
       grind)
    | exact superpose eq14215 eq19
    | exact resolve eq19 eq14215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq14443 : ∀ X0 : G, (M.op X0 X0) = (σ (σ (σ y))) := by
    intro X0
    first
    | (have i₁ := eq1078 y X0
       have i₂ := eq14215
       grind)
    | exact superpose eq14215 eq1078
    | exact resolve eq1078 eq14215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1078
  have eq14444 : ∀ X0 : G, (M.op X0 X0) = (σ (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1079 y X0
       have i₂ := eq14215
       grind)
    | exact superpose eq14215 eq1079
    | exact resolve eq1079 eq14215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1079
  have eq14445 : ∀ X0 : G, (M.op X0 X0) = (τ y) := by
    intro X0
    first
    | (have i₁ := eq1102 y X0
       have i₂ := eq14215
       grind)
    | exact superpose eq14215 eq1102
    | exact resolve eq1102 eq14215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1102 eq14215
  have eq14480 : (σ (σ y)) = (τ y) := by
    first
    | (have i₁ := eq14444 x
       have i₂ := eq14445 x
       grind)
    | exact superpose eq14445 eq14444
    | exact resolve eq14444 eq14445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14444
  have eq14481 : (σ (σ (σ y))) = (τ y) := by
    first
    | (have i₁ := eq14443 x
       have i₂ := eq14445 x
       grind)
    | exact superpose eq14445 eq14443
    | exact resolve eq14443 eq14445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14443 eq14445
  have eq14485 : (τ y) = (σ (τ y)) := by
    first
    | (have i₁ := eq14481
       have i₂ := eq14480
       grind)
    | exact superpose eq14480 eq14481
    | exact resolve eq14481 eq14480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14480 eq14481
  have eq14486 : y = (τ y) := by
    first
    | (have i₁ := eq14485
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq14485
    | exact resolve eq14485 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14485
  have eq14783 : y = (σ y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq14486
       grind)
    | exact superpose eq14486 eq10
    | exact resolve eq10 eq14486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14486
  have eq15721 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq14783
       grind)
    | exact superpose eq14783 eq14
    | exact resolve eq14 eq14783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14783
  have eq15805 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq15721
       have i₂ := eq14431 (σ x)
       grind)
    | exact superpose eq14431 eq15721
    | exact resolve eq15721 eq14431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15721
  have eq15834 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq15805
       have i₂ := eq14431 x
       grind)
    | exact superpose eq14431 eq15805
    | exact resolve eq15805 eq14431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14431 eq15805
  have eq15835 : False := by grind
  exact eq15835

/-- `Equation543`: `x = y ◇ (z ◇ (x ◇ (y ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pxx_pxy_Equation543 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law543 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law543.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X0 (M.op X1 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
  have eq18 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X2 (M.op X0 (M.op X1 X2))) (M.op X3 X0))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X3 X1 (M.op X2 (M.op X0 (M.op X1 X2)))
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 (M.op X2 X1)) X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 X1 (M.op X0 (M.op X2 X1))
       have i₂ := eq8 X0 X2 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq28 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op X2 X0))) = X2 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 X1 X1
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq12 X0 (M.op X1 X2)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
       have i₂ := eq17 X1 X0
       grind)
    | exact superpose eq17 eq9
    | exact resolve eq9 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq46 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X1 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 (M.op X1 (M.op X0 X2)) X1
       have i₂ := eq19 X1 X2 X0
       grind)
    | exact superpose eq19 eq8
    | exact resolve eq8 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq117 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X2 X1))) = X2 ∨ (M.op X1 X1) = (k X1 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X1 X0 X1 X2
       have i₂ := eq28 X1 X1 X0
       grind)
    | exact superpose eq28 eq18
    | (have j1 := eq28 X1 X0 X2
       grind)
    | exact resolve eq18 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq182 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 x X0 X1 X1
       have i₂ := eq46 x X1 (M.op X0 X1)
       grind)
    | exact superpose eq46 eq18
    | exact resolve eq18 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq46
  have eq214 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
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
  clear eq30
  have eq279 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 X1
       have i₂ := eq182 X1 (M.op X0 (M.op X1 X1))
       grind)
    | exact superpose eq182 eq8
    | exact resolve eq8 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq341 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq182 X0 (M.op X1 X1)
       have i₂ := eq279 X0 X1
       grind)
    | exact superpose eq279 eq182
    | exact resolve eq182 eq279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq463 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    grind
  have eq705 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X1 (M.op X0 X0)
       have i₂ := eq463 X0 (σ X1)
       grind)
    | exact superpose eq463 eq38
    | exact resolve eq38 eq463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq706 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op X0 X0)
       have i₂ := eq463 X0 (τ X1)
       grind)
    | exact superpose eq463 eq16
    | exact resolve eq16 eq463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq13223 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X2 ∨ (M.op X0 X0) = (k X2 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq117 X0 X0 X0
       have i₂ := eq341 X0 X1
       grind)
    | (have i₁ := eq117 X0 X1 X1
       have i₂ := eq341 X0 X1
       grind)
    | exact superpose eq341 eq117
    | exact resolve eq117 eq341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq13556 : ∀ X0 X2 : G, (M.op X0 X0) = (k X2 X2) ∨ (M.op X0 X0) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq13223 X0 x X2
       have i₂ := eq182 x (M.op X0 X0)
       grind)
    | exact superpose eq182 eq13223
    | (have j0 := eq13223 X0 x X2
       grind)
    | exact resolve eq13223 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13223
  have eq14658 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X2 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq341 X1 X2
       have i₂ := eq13556 X2 X0
       grind)
    | exact superpose eq13556 eq341
    | (have j1 := eq13556 X1 X0
       grind)
    | exact resolve eq341 eq13556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14770 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) ∨ (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq706 X1 (σ (M.op X1 X1))
       have i₂ := eq13556 X0 (σ (M.op X1 X1))
       grind)
    | exact superpose eq13556 eq706
    | (have j1 := eq13556 X0 (σ (M.op X1 X1))
       grind)
    | exact resolve eq706 eq13556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706
  have eq14772 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) ∨ (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq705 X1 (τ (M.op X1 X1))
       have i₂ := eq13556 X0 (τ (M.op X1 X1))
       grind)
    | exact superpose eq13556 eq705
    | (have j1 := eq13556 X0 (τ (M.op X1 X1))
       grind)
    | exact resolve eq705 eq13556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705
  have eq14782 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq13556 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14785 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq14772 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14772
  have eq14786 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq14770 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14770
  have eq15298 : ∀ X0 X1 : G, (M.op X1 (τ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq182 X1 X1
       have i₂ := eq14785 X1 X0
       grind)
    | exact superpose eq14785 eq182
    | exact resolve eq182 eq14785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq15722 : ∀ X0 X2 : G, (σ (M.op X0 X0)) = (τ (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq14785 x X2
       have i₂ := eq14786 x X0
       grind)
    | exact superpose eq14786 eq14785
    | exact resolve eq14785 eq14786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14785 eq14786
  have eq16318 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq214
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq214
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq214 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq16319 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq16318
  have eq38175 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14782 X1 X0
       have i₂ := eq27 X0 X0
       grind)
    | exact superpose eq27 eq14782
    | (have j0 := eq14782 X1 X0
       have j1 := eq27 X0 X0
       grind)
    | (have r₁ := eq14782 X0 X0
       have r₂ := eq27 X0 X0
       grind)
    | exact resolve eq14782 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq38191 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq38175 X0 X1
       have j1 := eq14782 X1 X0
       grind)
    | (have r₁ := eq38175 X1 X1
       have r₂ := eq14782 X1 X1
       grind)
    | (have r₁ := eq38175 (M.op X0 X0) X1
       have r₂ := eq14782 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | (have r₁ := eq38175 (k (M.op X1 X1) (M.op X1 X1)) X1
       have r₂ := eq14782 X0 (M.op X1 X1)
       grind)
    | exact resolve eq38175 eq14782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14782 eq38175
  have eq38311 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X2 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq38191 X1 X2
       have i₂ := eq341 X1 X0
       grind)
    | (have i₁ := eq38191 X1 X2
       have i₂ := eq341 X0 X1
       grind)
    | exact superpose eq341 eq38191
    | (have j0 := eq38191 X1 X2
       grind)
    | (have r₁ := eq38191 (M.op X1 X1) X1
       have r₂ := eq341 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq38191 (M.op X0 X0) X1
       have r₂ := eq341 X0 (M.op X0 X0)
       grind)
    | exact resolve eq38191 eq341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341 eq38191
  have eq91292 : ∀ X0 X2 X3 : G, (k X2 X0) = X0 ∨ (k X0 X0) = (M.op X3 X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq463 X2 x
       have i₂ := eq14658 X0 x X2
       grind)
    | (have i₁ := eq463 X0 x
       have i₂ := eq14658 (M.op X0 X0) x X2
       grind)
    | exact superpose eq14658 eq463
    | (have j1 := eq14658 X0 X3 X2
       grind)
    | exact resolve eq463 eq14658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463 eq14658
  have eq95390 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq91292 X0 x X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91292
  have eq95397 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq95390 X0 X1
       have j1 := eq13556 X1 X0
       grind)
    | (have r₁ := eq95390 (k x x) X0
       have r₂ := eq13556 X0 x
       grind)
    | (have r₁ := eq95390 x X0
       have r₂ := eq13556 X0 x
       grind)
    | (have r₁ := eq95390 (M.op X0 X0) X1
       have r₂ := eq13556 X0 (M.op X1 X1)
       grind)
    | exact resolve eq95390 eq13556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13556 eq95390
  have eq96228 : ∀ X0 X2 : G, (σ (k X0 X0)) = (τ (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq15722 x X2
       have i₂ := eq95397 X0 x
       grind)
    | exact superpose eq95397 eq15722
    | exact resolve eq15722 eq95397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15722
  have eq96269 : ∀ X0 X2 X3 : G, (k X0 X0) ≠ X2 ∨ (M.op X3 X3) = X2 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq38311 x X2 X3
       have i₂ := eq95397 X0 x
       grind)
    | exact superpose eq95397 eq38311
    | (have j0 := eq38311 X0 X2 X3
       grind)
    | (have r₁ := eq38311 x (k X0 X0) X2
       have r₂ := eq95397 X0 x
       grind)
    | exact resolve eq38311 eq95397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38311
  have eq96384 : ∀ X0 X1 : G, (k X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15298 X1 (τ (M.op X1 X1))
       have i₂ := eq95397 X0 (τ (M.op X1 X1))
       grind)
    | exact superpose eq95397 eq15298
    | exact resolve eq15298 eq95397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15298 eq95397
  have eq110561 : ∀ X0 : G, (k X0 X0) = (τ (σ y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq96384 X0 (σ x)
       have i₂ := eq16319
       grind)
    | exact superpose eq16319 eq96384
    | exact resolve eq96384 eq16319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16319
  have eq110597 : ∀ X0 : G, y = (k X0 X0) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq110561 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq110561
    | exact resolve eq110561 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110561
  have eq110627 : y = (M.op x x) := by
    first
    | (have j1 := eq96269 x y x
       grind)
    | (have r₁ := eq110597 x
       have r₂ := eq96269 x y x
       grind)
    | exact resolve eq110597 eq96269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96269 eq110597
  have eq110642 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq279 X0 x
       have i₂ := eq110627
       grind)
    | exact superpose eq110627 eq279
    | exact resolve eq279 eq110627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279
  have eq110695 : ∀ X0 : G, (σ (k X0 X0)) = (τ y) := by
    intro X0
    first
    | (have i₁ := eq96228 X0 x
       have i₂ := eq110627
       grind)
    | exact superpose eq110627 eq96228
    | exact resolve eq96228 eq110627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96228
  have eq110697 : ∀ X0 : G, (k X0 X0) = (τ y) := by
    intro X0
    first
    | (have i₁ := eq96384 X0 x
       have i₂ := eq110627
       grind)
    | exact superpose eq110627 eq96384
    | exact resolve eq96384 eq110627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96384 eq110627
  have eq110828 : (τ y) = (σ (τ y)) := by
    first
    | (have i₁ := eq110695 x
       have i₂ := eq110697 x
       grind)
    | exact superpose eq110697 eq110695
    | exact resolve eq110695 eq110697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110695 eq110697
  have eq110880 : y = (τ y) := by
    first
    | (have i₁ := eq110828
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq110828
    | exact resolve eq110828 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110828
  have eq111068 : y = (σ y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq110880
       grind)
    | exact superpose eq110880 eq10
    | exact resolve eq10 eq110880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110880
  have eq111159 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq111068
       grind)
    | exact superpose eq111068 eq14
    | exact resolve eq14 eq111068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111068
  have eq111193 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq111159
       have i₂ := eq110642 (σ x)
       grind)
    | exact superpose eq110642 eq111159
    | exact resolve eq111159 eq110642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111159
  have eq111205 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq111193
       have i₂ := eq110642 x
       grind)
    | exact superpose eq110642 eq111193
    | exact resolve eq111193 eq110642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110642 eq111193
  have eq111206 : False := by grind
  exact eq111206

/-- `Equation618`: `x = x ◇ (x ◇ ((x ◇ y) ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation618 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law618 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law618.models_iff G M).mp hM
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
  have eq52 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X0 X1) = (k X0 X2) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X1 X1
       have i₂ := eq12 X1 X1
       grind)
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j1 := eq12 X0 X1
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
  have eq386 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq387 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq386 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386
  have eq394 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq387 (σ X0) (σ X1)
       grind)
    | exact superpose eq387 eq13
    | exact resolve eq13 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq409 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq394 X0 X1
       have i₂ := eq387 X0 X1
       grind)
    | exact superpose eq387 eq394
    | exact resolve eq394 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387 eq394
  have eq1404 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq409 x y
       grind)
    | exact superpose eq409 eq14
    | (have r₁ := eq14
       have r₂ := eq409 x y
       grind)
    | exact resolve eq14 eq409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409
  have eq1422 : False := by grind
  exact eq1422

/-- `Equation635`: `x = x ◇ (y ◇ ((x ◇ z) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pyx_Equation635 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law635 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law635.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X0 X2) X0))) = X0 := by
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
  have eq18 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 (M.op x (M.op (M.op X0 x) X0))
       have i₂ := eq8 X0 x x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq8 (M.op X0 X0) X0 x
       have i₂ := eq18 X0 (M.op (M.op X0 X0) x)
       grind)
    | exact superpose eq18 eq8
    | exact resolve eq8 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
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
  have eq32 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq22 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq22 X0
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq22
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq22 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  have eq42 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq43 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq38
    | exact resolve eq38 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq45 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
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
  have eq50 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq53 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
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
  clear eq27
  have eq61 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq42 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq42
    | exact resolve eq42 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq82 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (k (τ X1) X0) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq43 X1
       have i₂ := eq12 (τ X1) X0
       grind)
    | (have i₁ := eq43 X0
       have i₂ := eq12 X0 (M.op (τ X0) (τ X0))
       grind)
    | exact superpose eq12 eq43
    | (have j1 := eq12 (τ X1) X0
       grind)
    | exact resolve eq43 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq117 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  have eq119 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq50 X1 X0
       have i₂ := eq12 (σ X1) X0
       grind)
    | exact superpose eq12 eq50
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq50 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq131 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq117 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq117
    | exact resolve eq117 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq201 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X1)
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq22
    | (have j1 := eq31 X0 X1
       grind)
    | exact resolve eq22 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq262 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq131 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq131
    | (have j1 := eq31 X0 X1
       grind)
    | exact resolve eq131 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq131
  have eq283 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq262 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq262
    | (have j0 := eq262 X0 X1
       grind)
    | exact resolve eq262 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262
  have eq704 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq45 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq45
    | exact resolve eq45 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq736 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq10
    | (have j1 := eq45 X1 X0
       grind)
    | exact resolve eq10 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq787 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq704 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq704
    | (have j0 := eq704 X0 X1
       grind)
    | exact resolve eq704 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704
  have eq846 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq848 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1
       have i₂ := eq787 X0 X1
       grind)
    | (have i₁ := eq22 X0
       have i₂ := eq787 (M.op X0 X0) X1
       grind)
    | exact superpose eq787 eq22
    | (have j1 := eq787 X0 X1
       grind)
    | exact resolve eq22 eq787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1282 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (M.op X1 (σ (k X0 X0)))) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 (σ X0) X1
       have i₂ := eq53 X0 X0
       grind)
    | exact superpose eq53 eq18
    | (have j1 := eq53 X0 X0
       grind)
    | exact resolve eq18 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1283 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq22 (σ X0)
       have i₂ := eq53 X0 X0
       grind)
    | exact superpose eq53 eq22
    | (have j1 := eq53 X0 X0
       grind)
    | exact resolve eq22 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq53
  have eq2668 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq82 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq82
    | (have j0 := eq82 X1 (σ X0)
       grind)
    | exact resolve eq82 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq2743 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2668 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq2668
    | (have j0 := eq2668 X0 X1
       grind)
    | exact resolve eq2668 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2668
  have eq8837 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq283 x y
       grind)
    | exact superpose eq283 eq14
    | (have j1 := eq283 x y
       grind)
    | exact resolve eq14 eq283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283
  have eq8866 : y = (k y x) := by
    first
    | (have j1 := eq846 x y
       grind)
    | (have r₁ := eq8837
       have r₂ := eq846 x y
       grind)
    | exact resolve eq8837 eq846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq846 eq8837
  have eq9287 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq32 x y
       have i₂ := eq8866
       grind)
    | exact superpose eq8866 eq32
    | (have j0 := eq32 x y
       grind)
    | exact resolve eq32 eq8866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq9290 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq787 x y
       have i₂ := eq8866
       grind)
    | exact superpose eq8866 eq787
    | (have j0 := eq787 x y
       grind)
    | exact resolve eq787 eq8866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787
  have eq9291 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq848 x y
       have i₂ := eq8866
       grind)
    | exact superpose eq8866 eq848
    | (have j0 := eq848 x y
       grind)
    | exact resolve eq848 eq8866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848
  have eq10544 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq9287
  have eq14662 : ∀ X0 : G, (k (σ (τ X0)) X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq736 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736
  have eq14663 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14662 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq14662
    | (have j0 := eq14662 X0
       grind)
    | exact resolve eq14662 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14662
  have eq14749 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq14663 (σ X0)
       have i₂ := eq13 X0 X0
       grind)
    | exact superpose eq13 eq14663
    | (have j0 := eq14663 (σ X0)
       grind)
    | exact resolve eq14663 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14663
  have eq14761 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq14749 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq14749
    | (have j0 := eq14749 X0
       grind)
    | exact resolve eq14749 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14749
  have eq15815 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq14761 X0
       have i₂ := eq2743 X0 X0
       grind)
    | exact superpose eq2743 eq14761
    | (have j0 := eq14761 X0
       have j1 := eq2743 X0 X0
       grind)
    | (have r₁ := eq14761 x
       have r₂ := eq2743 x x
       grind)
    | exact resolve eq14761 eq2743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2743 eq14761
  have eq15832 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq15815 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15815
  have eq15980 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq201 x y
       grind)
    | exact superpose eq201 eq14
    | (have j1 := eq201 x y
       grind)
    | exact resolve eq14 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16017 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq201 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq16030 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15980
       have i₂ := eq8866
       grind)
    | exact superpose eq8866 eq15980
    | exact resolve eq15980 eq8866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15980
  have eq18669 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (M.op X1 (k (σ (τ X0)) X0))) ∨ (σ (τ X0)) = (k (σ (τ X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1282 (τ X0) X1
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq1282
    | exact resolve eq1282 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1282
  have eq18760 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (k X0 X0))) = X0 ∨ (σ (τ X0)) = (k (σ (τ X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq18669 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq18669
    | (have j0 := eq18669 X0 X1
       grind)
    | exact resolve eq18669 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18669
  have eq18771 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (k X0 X0))) = X0 ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18760 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq18760
    | (have j0 := eq18760 X0 X1
       grind)
    | exact resolve eq18760 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18760
  have eq18829 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq8 (k X0 X0) X0 x
       have i₂ := eq18771 X0 (M.op (k X0 X0) x)
       grind)
    | exact superpose eq18771 eq8
    | (have j1 := eq18771 X0 x
       grind)
    | exact resolve eq8 eq18771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18771
  have eq24232 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq16017 (τ X1) (τ X0)
       have i₂ := eq61 X1 X0
       grind)
    | exact superpose eq61 eq16017
    | (have j0 := eq16017 (τ X1) (τ X0)
       grind)
    | exact resolve eq16017 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq24238 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16017 x y
       have i₂ := eq8866
       grind)
    | exact superpose eq8866 eq16017
    | (have j0 := eq16017 x y
       grind)
    | exact resolve eq16017 eq8866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8866 eq16017
  have eq24292 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq24232 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq24232
    | (have j0 := eq24232 X0 X1
       grind)
    | exact resolve eq24232 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24232
  have eq24306 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq24292 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq24292
    | (have j0 := eq24292 X0 X1
       grind)
    | exact resolve eq24292 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24292
  have eq24313 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq24306 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq24306
    | (have j0 := eq24306 X0 X1
       grind)
    | exact resolve eq24306 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24306
  have eq24314 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq24313 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq24313
    | (have j0 := eq24313 X0 X1
       grind)
    | exact resolve eq24313 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24313
  have eq27926 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16030
       have i₂ := eq9291
       grind)
    | exact superpose eq9291 eq16030
    | (have r₁ := eq16030
       have r₂ := eq9291
       grind)
    | exact resolve eq16030 eq9291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27927 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16030
       have i₂ := eq9290
       grind)
    | exact superpose eq9290 eq16030
    | (have r₁ := eq16030
       have r₂ := eq9290
       grind)
    | exact resolve eq16030 eq9290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9290 eq16030
  have eq27931 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq27927
  have eq27932 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq27926
  have eq28460 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq27931
       grind)
    | exact superpose eq27931 eq14
    | exact resolve eq14 eq27931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27931
  have eq30516 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq27932
       grind)
    | exact superpose eq27932 eq14
    | exact resolve eq14 eq27932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30528 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq119 (σ x) y
       have i₂ := eq27932
       grind)
    | exact superpose eq27932 eq119
    | (have j0 := eq119 (σ x) y
       grind)
    | exact resolve eq119 eq27932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27932
  have eq30555 : x = (k y x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq30528
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq30528
    | exact resolve eq30528 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30528
  have eq30578 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq24314 y x
       grind)
    | (have r₁ := eq30555
       have r₂ := eq24314 y x
       grind)
    | exact resolve eq30555 eq24314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24314 eq30555
  have eq31265 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq30516
       have i₂ := eq9291
       grind)
    | exact superpose eq9291 eq30516
    | exact resolve eq30516 eq9291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9291 eq30516
  have eq31270 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by grind
  clear eq31265
  have eq31514 : (τ (σ x)) = (k y (τ (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq119 (σ y) y
       have i₂ := eq30578
       grind)
    | exact superpose eq30578 eq119
    | exact resolve eq119 eq30578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq30578
  have eq31566 : (τ (σ x)) = (k y (τ (σ y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq31514
       have r₂ := eq31270
       grind)
    | exact resolve eq31514 eq31270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31270 eq31514
  have eq31584 : (k y y) = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq31566
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq31566
    | exact resolve eq31566 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31566
  have eq31589 : x = (k y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq31584
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq31584
    | exact resolve eq31584 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31584
  have eq31791 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18829 y
       have i₂ := eq31589
       grind)
    | exact superpose eq31589 eq18829
    | exact resolve eq18829 eq31589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18829 eq31589
  have eq31814 : x = (M.op x y) ∨ x = y := by grind
  clear eq31791
  have eq31821 : x = (M.op x y) := by
    first
    | (have r₁ := eq31814
       have r₂ := eq10544
       grind)
    | exact resolve eq31814 eq10544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10544 eq31814
  have eq32041 : (σ x) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq28460
       have i₂ := eq31821
       grind)
    | exact superpose eq31821 eq28460
    | exact resolve eq28460 eq31821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28460
  have eq32059 : x = (M.op y y) := by grind
  clear eq32041
  have eq32299 : x = (k y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq15832 y
       have i₂ := eq32059
       grind)
    | exact superpose eq32059 eq15832
    | exact resolve eq15832 eq32059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15832 eq32059
  have eq35415 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1283 y
       have i₂ := eq32299
       grind)
    | exact superpose eq32299 eq1283
    | exact resolve eq1283 eq32299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1283 eq32299
  have eq35454 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq35415
  have eq35459 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq35454
       have r₂ := eq24238
       grind)
    | exact resolve eq35454 eq24238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24238 eq35454
  have eq36049 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq35459
       grind)
    | exact superpose eq35459 eq14
    | exact resolve eq14 eq35459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35459
  have eq36105 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq36049
       have i₂ := eq31821
       grind)
    | exact superpose eq31821 eq36049
    | exact resolve eq36049 eq31821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31821 eq36049
  have eq36106 : False := by grind
  exact eq36106

/-- `Equation645`: `x = x ◇ (y ◇ ((y ◇ z) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pyx_Equation645 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law645 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law645.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X2) X0))) = X0 := by
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
  have eq18 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X0 (M.op x (M.op (M.op x x) X0))
       have i₂ := eq8 X0 x x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (M.op X0 X0)
       have i₂ := eq18 X0 X0
       grind)
    | exact superpose eq18 eq18
    | exact resolve eq18 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq34 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq35 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq24 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq24 X0
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq24
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq24 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  have eq44 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq45 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq40
    | exact resolve eq40 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq47 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
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
  have eq52 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq55 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq30 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq30
    | exact resolve eq30 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq30 (τ X0) X1
       grind)
    | exact superpose eq30 eq17
    | (have j1 := eq30 (τ X0) X1
       grind)
    | exact resolve eq17 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq60 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq30 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq44 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq44
    | exact resolve eq44 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq90 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (k (τ X1) X0) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq45 X1
       have i₂ := eq12 (τ X1) X0
       grind)
    | (have i₁ := eq45 X0
       have i₂ := eq12 X0 (M.op (τ X0) (τ X0))
       grind)
    | exact superpose eq12 eq45
    | (have j1 := eq12 (τ X1) X0
       grind)
    | exact resolve eq45 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq126 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  have eq128 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq52 X1 X0
       have i₂ := eq12 (σ X1) X0
       grind)
    | exact superpose eq12 eq52
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq52 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq140 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq126 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq126
    | exact resolve eq126 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq210 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (σ X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq24
    | (have j1 := eq34 X0 X1
       grind)
    | exact resolve eq24 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq34 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq285 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq140 X1
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq140
    | (have j1 := eq34 X0 X1
       grind)
    | exact resolve eq140 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq140
  have eq304 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq285 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq285
    | (have j0 := eq285 X0 X1
       grind)
    | exact resolve eq285 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285
  have eq815 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq47 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq47
    | exact resolve eq47 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq846 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq47 X1 X0
       grind)
    | exact superpose eq47 eq10
    | (have j1 := eq47 X1 X0
       grind)
    | exact resolve eq10 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq905 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq815 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq815
    | (have j0 := eq815 X0 X1
       grind)
    | exact resolve eq815 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq815
  have eq930 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq57 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq57
    | exact resolve eq57 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq981 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq930 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq930
    | (have j0 := eq930 X0 X1
       grind)
    | exact resolve eq930 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq930
  have eq1036 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1
       have i₂ := eq905 X0 X1
       grind)
    | (have i₁ := eq24 X0
       have i₂ := eq905 (M.op X0 X0) X1
       grind)
    | exact superpose eq905 eq24
    | (have j1 := eq905 X0 X1
       grind)
    | exact resolve eq24 eq905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1364 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq24 (σ X0)
       have i₂ := eq55 X0 X0
       grind)
    | exact superpose eq55 eq24
    | (have j1 := eq55 X0 X0
       grind)
    | exact resolve eq24 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq55
  have eq2621 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq90 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq90
    | (have j0 := eq90 X1 (σ X0)
       grind)
    | exact resolve eq90 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq2692 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2621 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq2621
    | (have j0 := eq2621 X0 X1
       grind)
    | exact resolve eq2621 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2621
  have eq2953 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq218 X0
       have i₂ := eq2692 X0 X0
       grind)
    | exact superpose eq2692 eq218
    | (have j0 := eq218 X0
       have j1 := eq2692 X0 X0
       grind)
    | (have r₁ := eq218 x
       have r₂ := eq2692 x x
       grind)
    | exact resolve eq218 eq2692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2692
  have eq2985 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq2953 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2953
  have eq9280 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq304 x y
       grind)
    | exact superpose eq304 eq14
    | (have j1 := eq304 x y
       grind)
    | exact resolve eq14 eq304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304
  have eq9355 : y = (k y x) := by
    first
    | (have j1 := eq981 x y
       grind)
    | (have r₁ := eq9280
       have r₂ := eq981 x y
       grind)
    | exact resolve eq9280 eq981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq981 eq9280
  have eq10019 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq35 x y
       have i₂ := eq9355
       grind)
    | exact superpose eq9355 eq35
    | (have j0 := eq35 x y
       grind)
    | exact resolve eq35 eq9355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq10022 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq905 x y
       have i₂ := eq9355
       grind)
    | exact superpose eq9355 eq905
    | (have j0 := eq905 x y
       grind)
    | exact resolve eq905 eq9355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905
  have eq10023 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1036 x y
       have i₂ := eq9355
       grind)
    | exact superpose eq9355 eq1036
    | (have j0 := eq1036 x y
       grind)
    | exact resolve eq1036 eq9355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1036
  have eq11317 : y = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18 x y
       have i₂ := eq10019
       grind)
    | exact superpose eq10019 eq18
    | exact resolve eq18 eq10019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq11348 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq14039 : y = (M.op y y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11317
       have i₂ := eq10019
       grind)
    | exact superpose eq10019 eq11317
    | exact resolve eq11317 eq10019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10019 eq11317
  have eq14087 : y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq14039
       have r₂ := eq11348
       grind)
    | exact resolve eq14039 eq11348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11348 eq14039
  have eq14362 : y ≠ y ∨ y = (k y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq60 y y
       have i₂ := eq14087
       grind)
    | exact superpose eq14087 eq60
    | (have j0 := eq60 y y
       grind)
    | (have r₁ := eq60 y y
       have r₂ := eq14087
       grind)
    | exact resolve eq60 eq14087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq14087
  have eq14392 : y = (k y y) ∨ x = (M.op x y) := by grind
  clear eq14362
  have eq14648 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq218 y
       have i₂ := eq14392
       grind)
    | exact superpose eq14392 eq218
    | (have j0 := eq218 y
       grind)
    | exact resolve eq218 eq14392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218 eq14392
  have eq14670 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq14648
  have eq34229 : ∀ X0 : G, (k (σ (τ X0)) X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq846 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq846
  have eq34230 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq34229 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq34229
    | (have j0 := eq34229 X0
       grind)
    | exact resolve eq34229 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34229
  have eq34371 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq34230 X0
       have i₂ := eq30 X0 X0
       grind)
    | exact superpose eq30 eq34230
    | (have j0 := eq34230 X0
       have j1 := eq30 X0 X0
       grind)
    | (have r₁ := eq34230 X0
       have r₂ := eq30 X0 X0
       grind)
    | exact resolve eq34230 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq34400 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq34371 X0
       have j1 := eq34230 X0
       grind)
    | (have r₁ := eq34371 X0
       have r₂ := eq34230 X0
       grind)
    | exact resolve eq34371 eq34230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34230 eq34371
  have eq34758 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq34400 (σ X0)
       have i₂ := eq2985 X0
       grind)
    | exact superpose eq2985 eq34400
    | (have j0 := eq34400 (σ X0)
       have j1 := eq2985 X0
       grind)
    | (have r₁ := eq34400 (σ X0)
       have r₂ := eq2985 X0
       grind)
    | exact resolve eq34400 eq2985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2985 eq34400
  have eq34770 : ∀ X0 : G, (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq34758 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34758
  have eq34783 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq34770 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq34770
    | (have j0 := eq34770 X0
       grind)
    | exact resolve eq34770 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34770
  have eq40813 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq210 x y
       grind)
    | exact superpose eq210 eq14
    | (have j1 := eq210 x y
       grind)
    | exact resolve eq14 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40949 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq210 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq40980 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40813
       have i₂ := eq9355
       grind)
    | exact superpose eq9355 eq40813
    | exact resolve eq40813 eq9355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40813
  have eq42561 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq40949 (τ X1) (τ X0)
       have i₂ := eq63 X1 X0
       grind)
    | exact superpose eq63 eq40949
    | (have j0 := eq40949 (τ X1) (τ X0)
       grind)
    | exact resolve eq40949 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq42569 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40949 x y
       have i₂ := eq9355
       grind)
    | exact superpose eq9355 eq40949
    | (have j0 := eq40949 x y
       grind)
    | exact resolve eq40949 eq9355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9355 eq40949
  have eq42625 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq42561 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq42561
    | (have j0 := eq42561 X0 X1
       grind)
    | exact resolve eq42561 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42561
  have eq42639 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq42625 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq42625
    | (have j0 := eq42625 X0 X1
       grind)
    | exact resolve eq42625 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42625
  have eq42643 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq42639 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq42639
    | (have j0 := eq42639 X0 X1
       grind)
    | exact resolve eq42639 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42639
  have eq42644 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq42643 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq42643
    | (have j0 := eq42643 X0 X1
       grind)
    | exact resolve eq42643 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42643
  have eq44680 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq40980
       have i₂ := eq10023
       grind)
    | exact superpose eq10023 eq40980
    | (have r₁ := eq40980
       have r₂ := eq10023
       grind)
    | exact resolve eq40980 eq10023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44681 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40980
       have i₂ := eq10022
       grind)
    | exact superpose eq10022 eq40980
    | (have r₁ := eq40980
       have r₂ := eq10022
       grind)
    | exact resolve eq40980 eq10022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10022 eq40980
  have eq44683 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq44681
  have eq44684 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq44680
  have eq44740 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq44683
       grind)
    | exact superpose eq44683 eq14
    | exact resolve eq14 eq44683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44683
  have eq45038 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq44684
       grind)
    | exact superpose eq44684 eq14
    | exact resolve eq14 eq44684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45050 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq128 (σ x) y
       have i₂ := eq44684
       grind)
    | exact superpose eq44684 eq128
    | (have j0 := eq128 (σ x) y
       grind)
    | exact resolve eq128 eq44684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq44684
  have eq45095 : x = (k y x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq45050
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq45050
    | exact resolve eq45050 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45050
  have eq45113 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq42644 y x
       grind)
    | (have r₁ := eq45095
       have r₂ := eq42644 y x
       grind)
    | exact resolve eq45095 eq42644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42644 eq45095
  have eq45281 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq45038
       have i₂ := eq10023
       grind)
    | exact superpose eq10023 eq45038
    | exact resolve eq45038 eq10023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10023 eq45038
  have eq45285 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by grind
  clear eq45281
  have eq45533 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14670
       have i₂ := eq45113
       grind)
    | exact superpose eq45113 eq14670
    | exact resolve eq14670 eq45113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14670 eq45113
  have eq45617 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq45533
  have eq45642 : x = (M.op x y) := by
    first
    | (have r₁ := eq45617
       have r₂ := eq45285
       grind)
    | exact resolve eq45617 eq45285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45285 eq45617
  have eq45767 : (σ x) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq44740
       have i₂ := eq45642
       grind)
    | exact superpose eq45642 eq44740
    | exact resolve eq44740 eq45642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44740
  have eq45838 : x = (M.op y y) := by grind
  clear eq45767
  have eq45913 : x = (k y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq34783 y
       have i₂ := eq45838
       grind)
    | exact superpose eq45838 eq34783
    | exact resolve eq34783 eq45838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34783 eq45838
  have eq47080 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1364 y
       have i₂ := eq45913
       grind)
    | exact superpose eq45913 eq1364
    | exact resolve eq1364 eq45913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1364 eq45913
  have eq47122 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq47080
  have eq47126 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq47122
       have r₂ := eq42569
       grind)
    | exact resolve eq47122 eq42569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42569 eq47122
  have eq47206 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq47126
       grind)
    | exact superpose eq47126 eq14
    | exact resolve eq14 eq47126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47126
  have eq47295 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq47206
       have i₂ := eq45642
       grind)
    | exact superpose eq45642 eq47206
    | exact resolve eq47206 eq45642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45642 eq47206
  have eq47296 : False := by grind
  exact eq47296

/-- `Equation646`: `x = x ◇ (y ◇ ((y ◇ z) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pyx_pxx_pyx_Equation646 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law646 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law646.models_iff G M).mp hM
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
  have eq59 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq65 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq59 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq116 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq65 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq120 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq116 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq116 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq116 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq116 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq144 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq120 (σ X1) (σ X0)
       grind)
    | exact superpose eq120 eq13
    | exact resolve eq13 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq149 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq144 X0 X1
       have i₂ := eq120 X1 X0
       grind)
    | exact superpose eq120 eq144
    | exact resolve eq144 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq144
  have eq1499 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq149 x y
       grind)
    | exact superpose eq149 eq14
    | (have r₁ := eq14
       have r₂ := eq149 x y
       grind)
    | exact resolve eq14 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq1519 : False := by grind
  exact eq1519
