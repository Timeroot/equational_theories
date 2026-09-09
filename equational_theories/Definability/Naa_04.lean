import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3201`: `x = (((y ◇ z) ◇ y) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(Y,X) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pxx_pxy_pyx_pxx_pxy_Equation3201 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3201 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3201.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
  have eq30 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 X0 x
       grind)
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 x X0
       grind)
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15
    | (have j0 := eq15 X0 y
       grind)
    | exact resolve eq15 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y)
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10
    | (have j0 := eq10 x
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 y
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq58 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq30 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq30
    | (have j0 := eq30 y
       grind)
    | exact resolve eq30 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq63 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq31 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq31
    | (have j0 := eq31 y
       grind)
    | exact resolve eq31 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq91 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq48 X1 X0
       grind)
    | exact superpose eq48 eq10
    | exact resolve eq10 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq130 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq91 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq91
    | exact resolve eq91 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq215 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq228 : (M.op x y) ≠ (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq232 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq234 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k x y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq63 eq232
    | exact resolve eq232 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq232
  have eq249 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq130 X0 X0
       have i₂ := eq215 X0
       grind)
    | exact superpose eq215 eq130
    | exact resolve eq130 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq250 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq215 (σ X0)
       grind)
    | exact superpose eq215 eq15
    | exact resolve eq15 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq251 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq250 X0
       have i₂ := eq215 X0
       grind)
    | exact superpose eq215 eq250
    | exact resolve eq250 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq252 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq249 X0
       have i₂ := eq215 (τ X0)
       grind)
    | exact superpose eq215 eq249
    | exact resolve eq249 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215 eq249
  have eq970 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq1001 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0
       have i₂ := eq14 (σ X0) sF3
       grind)
    | exact superpose eq14 eq35
    | (have j1 := eq14 (σ X0) (σ y)
       grind)
    | exact resolve eq35 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq4453 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq970 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq970
    | (have j0 := eq970 X0 X1
       have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq970 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq970
  have eq120969 : (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq4453 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4453
    | (have j0 := eq4453 x y
       grind)
    | exact resolve eq4453 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4453
  have eq121021 : (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) := by
    first
    | exact superpose eq20 eq120969
    | exact resolve eq120969 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120969
  have eq121022 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq121021
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq121021
    | exact resolve eq121021 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121021
  have eq121023 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq121022
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq121022
    | exact resolve eq121022 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121022
  have eq121024 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) := by
    first
    | exact superpose eq26 eq121023
    | exact resolve eq121023 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121023
  have eq121025 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have r₁ := eq121024
       have r₂ := eq27
       grind)
    | exact resolve eq121024 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121024
  have eq121026 : (M.op (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq121025
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq121025
    | exact resolve eq121025 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121025
  have eq121027 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq121026
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq121026
    | exact resolve eq121026 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121026
  have eq121028 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) := by
    first
    | exact superpose eq26 eq121027
    | exact resolve eq121027 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121027
  have eq121029 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq121028
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq121028
    | exact resolve eq121028 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121028
  have eq121030 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq121029
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq121029
    | exact resolve eq121029 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121029
  have eq121051 : (τ (M.op (σ x) (σ x))) = (M.op (τ (σ y)) (τ (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) := by
    first
    | exact superpose eq121030 eq252
    | exact resolve eq252 eq121030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121030
  have eq121083 : (M.op y y) = (τ (M.op (σ x) (σ x))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) := by
    first
    | exact superpose eq39 eq121051
    | exact resolve eq121051 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121051
  have eq121105 : (M.op y y) = (M.op (τ (σ x)) (τ (σ x))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq121083
       have i₂ := eq252 sF2
       grind)
    | exact superpose eq252 eq121083
    | exact resolve eq121083 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121083
  have eq121106 : (M.op x x) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) := by
    first
    | exact superpose eq38 eq121105
    | exact resolve eq121105 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121105
  have eq121107 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq121106
  have eq121108 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq121107 eq234
    | (have r₁ := eq234
       have r₂ := eq121107
       grind)
    | exact resolve eq234 eq121107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234
  have eq121129 : (M.op (τ (σ x)) (τ (σ x))) = (τ (M.op (σ x) (σ y))) ∨ (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq121107 eq252
    | exact resolve eq252 eq121107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121107
  have eq121154 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq121108
  have eq121162 : (M.op x x) = (τ (M.op (σ x) (σ y))) ∨ (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq38 eq121129
    | exact resolve eq121129 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq121129
  have eq129962 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq121154
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq121154
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq121154 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121154
  have eq130031 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq129962
  have eq130048 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq130031
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq130031
    | exact resolve eq130031 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130031
  have eq130055 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq130048
    | exact resolve eq130048 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130048
  have eq130059 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq130055
       have r₂ := eq27
       grind)
    | exact resolve eq130055 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130055
  have eq130061 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq130059
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq130059
    | exact resolve eq130059 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130059
  have eq130062 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq130061
  have eq130086 : (M.op (τ (σ y)) (τ (σ y))) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) := by
    first
    | exact superpose eq130062 eq252
    | exact resolve eq252 eq130062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130062
  have eq130122 : (M.op y y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) := by
    first
    | exact superpose eq39 eq130086
    | exact resolve eq130086 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130086
  have eq130126 : (M.op x x) = (M.op y y) ∨ (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) := by
    first
    | exact superpose eq130122 eq121162
    | exact resolve eq121162 eq130122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121162 eq130122
  have eq130370 : (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq130126
  have eq130411 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (k y X0) = (M.op X0 y) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq12 y X0
       have i₂ := eq130370
       grind)
    | exact superpose eq130370 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq130370
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq130370
       grind)
    | exact resolve eq12 eq130370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130414 : (σ (M.op x x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq251 y
       have i₂ := eq130370
       grind)
    | exact superpose eq130370 eq251
    | exact resolve eq251 eq130370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130370
  have eq130448 : (σ (M.op x x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq130414
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq130414
    | exact resolve eq130414 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130414
  have eq130454 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq130448
       have i₂ := eq251 x
       grind)
    | exact superpose eq251 eq130448
    | exact resolve eq130448 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130448
  have eq130460 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq130454
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq130454
    | exact resolve eq130454 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130454
  have eq130483 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ x) (σ x)) ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq130460 eq12
    | (have j0 := eq12 X0 (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq130460
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq130460
       grind)
    | exact resolve eq12 eq130460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130460
  have eq143717 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have j0 := eq130411 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130411
  have eq143729 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq143717
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq143717
    | exact resolve eq143717 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143717
  have eq173408 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have j0 := eq130483 (σ x)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130483
  have eq173418 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq58 eq173408
    | exact resolve eq173408 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173408
  have eq173423 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq173418
    | exact resolve eq173418 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173418
  have eq173424 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq173423
       have i₂ := eq143729
       grind)
    | exact superpose eq143729 eq173423
    | exact resolve eq173423 eq143729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143729 eq173423
  have eq173527 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq173424
  have eq173536 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq173527
    | exact resolve eq173527 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173527
  have eq173540 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq173536
       have r₂ := eq27
       grind)
    | exact resolve eq173536 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173536
  have eq173543 : (M.op x y) ≠ (M.op x y) ∨ (M.op x x) = (M.op y y) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq228
       have i₂ := eq173540
       grind)
    | exact superpose eq173540 eq228
    | (have r₁ := eq228
       have r₂ := eq173540
       grind)
    | exact resolve eq228 eq173540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq176146 : (M.op x x) = (M.op y y) ∨ (k x y) = (M.op x x) := by grind
  clear eq173543
  have eq176236 : (M.op x y) = (M.op y y) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq176146
       have i₂ := eq173540
       grind)
    | exact superpose eq173540 eq176146
    | exact resolve eq176146 eq173540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176146
  have eq176243 : (M.op x y) = (k x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq176236
       have i₂ := eq173540
       grind)
    | exact superpose eq173540 eq176236
    | exact resolve eq176236 eq173540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176236
  have eq176257 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq251 x
       have i₂ := eq173540
       grind)
    | exact superpose eq173540 eq251
    | exact resolve eq251 eq173540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184734 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq176257
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq176257
    | exact resolve eq176257 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176257
  have eq186254 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq20 eq184734
    | exact resolve eq184734 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184734
  have eq187752 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq1001 x
       have i₂ := eq176243
       grind)
    | exact superpose eq176243 eq1001
    | (have j0 := eq1001 x
       grind)
    | exact resolve eq1001 eq176243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1001 eq176243
  have eq187772 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq187752
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq187752
    | exact resolve eq187752 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187752
  have eq187781 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq187772
    | exact resolve eq187772 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187772
  have eq187790 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq20 eq187781
    | exact resolve eq187781 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187781
  have eq187799 : (M.op (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq187790
       have r₂ := eq27
       grind)
    | exact resolve eq187790 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187790
  have eq187809 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq187799
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq187799
    | exact resolve eq187799 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187799
  have eq187819 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq186254 eq187809
    | exact resolve eq187809 eq186254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187809
  have eq187828 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq187819
    | exact resolve eq187819 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187819
  have eq187836 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq187828
       have r₂ := eq27
       grind)
    | exact resolve eq187828 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187828
  have eq187844 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq187836
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq187836
    | exact resolve eq187836 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq187836
  have eq187851 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq186254 eq187844
    | exact resolve eq187844 eq186254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187844
  have eq188073 : (τ (σ (M.op x y))) = (M.op (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq187851 eq252
    | exact resolve eq252 eq187851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252 eq187851
  have eq188097 : (τ (σ (M.op x y))) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq39 eq188073
    | exact resolve eq188073 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq188073
  have eq188112 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq37 eq188097
    | exact resolve eq188097 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq188097
  have eq188113 : (M.op x y) = (M.op y y) := by grind
  clear eq188112
  have eq188455 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x y) ∨ (k y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq12 y X0
       have i₂ := eq188113
       grind)
    | exact superpose eq188113 eq12
    | (have j0 := eq12 y X0
       grind)
    | exact resolve eq12 eq188113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188458 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq251 y
       have i₂ := eq188113
       grind)
    | exact superpose eq188113 eq251
    | exact resolve eq251 eq188113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251 eq188113
  have eq188486 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq188458
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq188458
    | exact resolve eq188458 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq188458
  have eq188555 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq20 eq188486
    | exact resolve eq188486 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188486
  have eq189043 : ∀ X0 : G, (M.op X0 X0) ≠ (σ (M.op x y)) ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq188555 eq12
    | (have j0 := eq12 (σ y) X0
       grind)
    | exact resolve eq12 eq188555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188555
  have eq189548 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq188455 x
       have i₂ := eq173540
       grind)
    | exact superpose eq173540 eq188455
    | (have j0 := eq188455 x
       grind)
    | (have r₁ := eq188455 x
       have r₂ := eq173540
       grind)
    | exact resolve eq188455 eq173540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173540 eq188455
  have eq189553 : (M.op x y) = (k y x) := by grind
  clear eq189548
  have eq189555 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq189553
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq189553
    | exact resolve eq189553 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq189553
  have eq189563 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq58
       have i₂ := eq189555
       grind)
    | exact superpose eq189555 eq58
    | exact resolve eq58 eq189555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq189555
  have eq189564 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq20 eq189563
    | exact resolve eq189563 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq189563
  have eq190531 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq186254 eq189043
    | (have j0 := eq189043 (σ x)
       grind)
    | (have r₁ := eq189043 (σ x)
       have r₂ := eq186254
       grind)
    | exact resolve eq189043 eq186254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186254 eq189043
  have eq190534 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq190531
  have eq190536 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq189564 eq190534
    | exact resolve eq190534 eq189564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189564 eq190534
  have eq190548 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq190536
    | exact resolve eq190536 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq190536
  have eq190549 : False := by grind
  exact eq190549

/-- `Equation3292`: `x ◇ x = y ◇ (z ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(Y,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyy_y_pxy_pyy_pxy_Equation3292 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3292 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3292.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X2 (M.op X1 X0))) := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq13 X0 X0
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
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
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
  have eq73 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 y)
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq15
    | exact resolve eq15 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq73 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq73
    | exact resolve eq73 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq176 : ∀ X0 : G, (M.op y y) = (M.op x (M.op X0 (M.op x y))) := by
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
  have eq177 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) (σ x) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : (M.op x y) = (k x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq28 x y
       grind)
    | exact superpose eq28 eq18
    | (have j1 := eq28 x y
       grind)
    | exact resolve eq18 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq28 sF2 sF3
       grind)
    | exact superpose eq28 eq26
    | (have j1 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq26 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq196 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op X0 (M.op y y)) := by
    intro X0
    first
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq201 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ y) (σ y))) := by
    intro X0
    first
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq440 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq186
       grind)
    | exact superpose eq186 eq41
    | exact resolve eq41 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq441 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq440
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq440
    | exact resolve eq440 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq440
  have eq443 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq441
    | exact resolve eq441 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441
  have eq532 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq443 eq187
    | exact resolve eq187 eq443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187 eq443
  have eq539 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq532
       have r₂ := eq27
       grind)
    | exact resolve eq532 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532
  have eq626 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 X2))) ≠ (M.op X0 (M.op X1 (M.op X0 X2))) ∨ (M.op X0 (M.op X1 (M.op X0 X2))) = (k X2 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq13
    | (have r₁ := eq13 (M.op X2 (M.op X0 X0)) X0
       have r₂ := eq16 X0 X0 X2
       grind)
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq643 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq539 eq13
    | exact resolve eq13 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539
  have eq658 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq661 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq643
  have eq666 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 X2))) = (k X2 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq626 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626
  have eq677 : (σ y) = (k (σ y) (σ y)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq661
       have i₂ := eq658 y
       grind)
    | exact superpose eq658 eq661
    | exact resolve eq661 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661
  have eq977 : (τ (σ y)) = (k (τ (σ y)) y) ∨ y = (k y y) := by
    first
    | exact superpose eq677 eq153
    | exact resolve eq153 eq677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq677
  have eq980 : y = (k y y) ∨ y = (k y y) := by
    first
    | exact superpose eq32 eq977
    | exact resolve eq977 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq977
  have eq981 : y = (k y y) := by grind
  clear eq980
  have eq987 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq981
       grind)
    | exact superpose eq981 eq41
    | exact resolve eq41 eq981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq991 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq987
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq987
    | exact resolve eq987 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq987
  have eq1341 : (M.op (M.op x y) (M.op x y)) = (k (M.op y y) (M.op y y)) := by
    first
    | (have i₁ := eq196 (M.op y y)
       have i₂ := eq658 (M.op y y)
       grind)
    | exact superpose eq658 eq196
    | exact resolve eq196 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1342 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq201 (M.op sF3 sF3)
       have i₂ := eq658 (M.op sF3 sF3)
       grind)
    | exact superpose eq658 eq201
    | exact resolve eq201 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq1358 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op X0 (k y y)) := by
    intro X0
    first
    | (have i₁ := eq196 X0
       have i₂ := eq658 y
       grind)
    | exact superpose eq658 eq196
    | exact resolve eq196 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq1374 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq1358 X0
       have i₂ := eq981
       grind)
    | exact superpose eq981 eq1358
    | exact resolve eq1358 eq981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1358
  have eq1386 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (k (σ y) (σ y)) (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq1342
       have i₂ := eq658 sF3
       grind)
    | exact superpose eq658 eq1342
    | exact resolve eq1342 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1342
  have eq1387 : (M.op (M.op x y) (M.op x y)) = (k (k y y) (k y y)) := by
    first
    | (have i₁ := eq1341
       have i₂ := eq658 y
       grind)
    | exact superpose eq658 eq1341
    | exact resolve eq1341 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1341
  have eq1402 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq1374 X0
       have i₂ := eq658 sF0
       grind)
    | exact superpose eq658 eq1374
    | exact resolve eq1374 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1374
  have eq1410 : (k (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq991 eq1386
    | exact resolve eq1386 eq991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1386
  have eq1411 : (k y y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1387
       have i₂ := eq981
       grind)
    | exact superpose eq981 eq1387
    | exact resolve eq1387 eq981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1387
  have eq1419 : (k (σ y) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1410
       have i₂ := eq658 sF4
       grind)
    | exact superpose eq658 eq1410
    | exact resolve eq1410 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1410
  have eq1420 : (k y y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1411
       have i₂ := eq658 sF0
       grind)
    | exact superpose eq658 eq1411
    | exact resolve eq1411 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1411
  have eq1424 : (σ y) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq991 eq1419
    | exact resolve eq1419 eq991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1419
  have eq1425 : y = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1420
       have i₂ := eq981
       grind)
    | exact superpose eq981 eq1420
    | exact resolve eq1420 eq981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq981 eq1420
  have eq1476 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq177 eq666
    | exact resolve eq666 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq666
  have eq1506 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (σ y) (σ y))) := by
    intro X0
    first
    | exact superpose eq1424 eq1476
    | exact resolve eq1476 eq1424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1424 eq1476
  have eq1548 : ∀ X0 : G, (σ y) = (M.op X0 (k (σ y) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq1506 X0
       have i₂ := eq658 sF3
       grind)
    | exact superpose eq658 eq1506
    | exact resolve eq1506 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658 eq1506
  have eq1581 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq991 eq1548
    | exact resolve eq1548 eq991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq991 eq1548
  have eq1634 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1581 eq26
    | (have j1 := eq1581 (σ x)
       grind)
    | exact resolve eq26 eq1581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1581
  have eq1648 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq1634 eq27
    | exact resolve eq27 eq1634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1634
  have eq1669 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1425 eq42
    | exact resolve eq42 eq1425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1425
  have eq1672 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq1669
    | exact resolve eq1669 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1669
  have eq1675 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1672
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1672
    | exact resolve eq1672 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1672
  have eq1930 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1402 x
       grind)
    | exact superpose eq1402 eq18
    | (have j1 := eq1402 x
       grind)
    | exact resolve eq18 eq1402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1402
  have eq1960 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1930 eq42
    | exact resolve eq42 eq1930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq1930
  have eq1964 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq1960
    | exact resolve eq1960 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1960
  have eq1967 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1675 eq1964
    | exact resolve eq1964 eq1675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1675 eq1964
  have eq1969 : False := by grind
  exact eq1969

/-- `Equation3459`: `x ◇ x = x ◇ ((x ◇ y) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,X) else if m(Y,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_x_pyx_pyx_pxy_Equation3459 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3459 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3459.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
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
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq10
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq24
    | exact resolve eq24 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 X2 : G, (k (τ X2) (k X0 (τ X1))) = (τ (k X2 (k (σ X0) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X2 (k X0 (τ X1))
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq24
    | exact resolve eq24 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq285 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) (σ X1)) = X0 ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X0 X1
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq24
    | (have j1 := eq14 X0 (σ X1)
       grind)
    | exact resolve eq24 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq286 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) (τ X1)) = X0 ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq20
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq20 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq289 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq359 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    grind
  have eq360 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq359 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359
  have eq367 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq20 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq360 (τ X0)
       grind)
    | exact superpose eq360 eq20
    | exact resolve eq20 eq360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq888 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq289 x y
       grind)
    | exact superpose eq289 eq16
    | (have j1 := eq289 x y
       grind)
    | exact resolve eq16 eq289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq893 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (M.op (σ (k X0 X1)) (σ X1))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) (σ X1)
       have i₂ := eq289 X0 X1
       grind)
    | exact superpose eq289 eq9
    | (have j1 := eq289 X0 X1
       grind)
    | exact resolve eq9 eq289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq898 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq900 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq289 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq901 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq900 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900
  have eq903 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq898 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq898
  have eq910 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ (k X0 X0)) (σ X0)) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq903 X0
       have i₂ := eq15 X0 (k X0 X0)
       grind)
    | exact superpose eq15 eq903
    | (have j0 := eq903 X0
       grind)
    | exact resolve eq903 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903
  have eq2590 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ (k (τ X0) (k (τ X0) (τ X0)))) = (M.op (σ (k (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq910 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq910
    | exact resolve eq910 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq910
  have eq2627 : ∀ X0 : G, (σ (k (τ X0) (k (τ X0) (τ X0)))) = (M.op (k (σ (τ X0)) X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2590 X0
       have i₂ := eq20 X0 (τ X0)
       grind)
    | exact superpose eq20 eq2590
    | (have j0 := eq2590 X0
       grind)
    | exact resolve eq2590 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2590
  have eq2630 : ∀ X0 : G, (σ (k (τ X0) (k (τ X0) (τ X0)))) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2627 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2627
    | (have j0 := eq2627 X0
       grind)
    | exact resolve eq2627 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2627
  have eq2631 : ∀ X0 : G, (M.op (k X0 X0) X0) = (k X0 (σ (k (τ X0) (τ X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2630 X0
       have i₂ := eq19 X0 (k (τ X0) (τ X0))
       grind)
    | exact superpose eq19 eq2630
    | (have j0 := eq2630 X0
       grind)
    | exact resolve eq2630 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2630
  have eq2632 : ∀ X0 : G, (M.op (k X0 X0) X0) = (k X0 (k (σ (τ X0)) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2631 X0
       have i₂ := eq20 X0 (τ X0)
       grind)
    | exact superpose eq20 eq2631
    | (have j0 := eq2631 X0
       grind)
    | exact resolve eq2631 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2631
  have eq2633 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 (k X0 X0)) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq2632 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2632
    | (have j0 := eq2632 X0
       grind)
    | exact resolve eq2632 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2632
  have eq2638 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 ∨ (k X0 (k X0 X0)) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0
       have i₂ := eq2633 X0
       grind)
    | exact superpose eq2633 eq9
    | (have j1 := eq2633 X0
       grind)
    | exact resolve eq9 eq2633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2673 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) ∨ (k (τ X0) (k (τ X0) (τ X0))) = (M.op (k (τ X0) (τ X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq367 X0
       have i₂ := eq2638 (τ X0)
       grind)
    | exact superpose eq2638 eq367
    | (have j1 := eq2638 (τ X0)
       grind)
    | exact resolve eq367 eq2638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367 eq2638
  have eq2676 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 ∨ (k (τ X0) (k (τ X0) (τ X0))) = (M.op (k (τ X0) (τ X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq2673 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2673
    | (have j0 := eq2673 X0
       grind)
    | exact resolve eq2673 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2673
  have eq2678 : ∀ X0 : G, (k (τ X0) (τ (k X0 X0))) = (M.op (τ (k X0 X0)) (τ X0)) ∨ (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2676 X0
       have i₂ := eq33 X0 X0
       grind)
    | exact superpose eq33 eq2676
    | (have j0 := eq2676 X0
       grind)
    | exact resolve eq2676 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2676
  have eq2680 : ∀ X0 : G, (M.op (τ (k X0 X0)) (τ X0)) = (τ (k X0 (k X0 X0))) ∨ (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2678 X0
       have i₂ := eq33 (k X0 X0) X0
       grind)
    | exact superpose eq33 eq2678
    | (have j0 := eq2678 X0
       grind)
    | exact resolve eq2678 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2678
  have eq4024 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq286 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq286
    | exact resolve eq286 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286
  have eq4072 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4024 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq4024
    | (have j0 := eq4024 X0 X1
       grind)
    | exact resolve eq4024 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4024
  have eq4507 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X1 X0)) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq285 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq285
    | exact resolve eq285 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285
  have eq4591 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4507 X0 X1
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq4507
    | (have j0 := eq4507 X0 X1
       grind)
    | exact resolve eq4507 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4507
  have eq6745 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq888
       have i₂ := eq4072 y x
       grind)
    | exact superpose eq4072 eq888
    | (have j1 := eq4072 (σ y) (σ x)
       grind)
    | (have r₁ := eq888
       have r₂ := eq4072 y x
       grind)
    | exact resolve eq888 eq4072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq888 eq4072
  have eq6746 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq6745
  have eq10991 : ∀ X0 : G, (τ (k (σ X0) (k (σ X0) (σ X0)))) = (M.op (τ (k (σ X0) (σ X0))) X0) ∨ (σ X0) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq2680 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2680
    | exact resolve eq2680 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2680
  have eq11023 : ∀ X0 : G, (τ (k (σ X0) (k (σ X0) (σ X0)))) = (M.op (k (τ (σ X0)) X0) X0) ∨ (σ X0) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10991 X0
       have i₂ := eq24 (σ X0) X0
       grind)
    | exact superpose eq24 eq10991
    | (have j0 := eq10991 X0
       grind)
    | exact resolve eq10991 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq10991
  have eq11049 : ∀ X0 : G, (M.op (k X0 X0) X0) = (τ (k (σ X0) (k (σ X0) (σ X0)))) ∨ (σ X0) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq11023 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11023
    | (have j0 := eq11023 X0
       grind)
    | exact resolve eq11023 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11023
  have eq11069 : ∀ X0 : G, (M.op (k X0 X0) X0) = (k (τ (σ X0)) (k X0 (τ (σ X0)))) ∨ (σ X0) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq11049 X0
       have i₂ := eq35 X0 (σ X0) (σ X0)
       grind)
    | exact superpose eq35 eq11049
    | (have j0 := eq11049 X0
       grind)
    | exact resolve eq11049 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq11049
  have eq11087 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op (k X0 X0) X0) ∨ (σ X0) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq11069 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11069
    | (have j0 := eq11069 X0
       grind)
    | exact resolve eq11069 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11069
  have eq11105 : ∀ X0 : G, (σ X0) = (σ (k (M.op X0 X0) X0)) ∨ (k X0 (k X0 X0)) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq11087 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq11087
    | (have j0 := eq11087 X0
       grind)
    | exact resolve eq11087 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11087
  have eq11123 : ∀ X0 : G, (σ X0) = (σ (M.op X0 (M.op X0 X0))) ∨ (k X0 (k X0 X0)) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq11105 X0
       have i₂ := eq360 X0
       grind)
    | exact superpose eq360 eq11105
    | (have j0 := eq11105 X0
       grind)
    | exact resolve eq11105 eq360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11105
  have eq11152 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k X0 (k X0 X0)) = (M.op (k X0 X0) X0) ∨ (k X0 (k X0 X0)) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq11123 X0
       have i₂ := eq2633 X0
       grind)
    | exact superpose eq2633 eq11123
    | (have j0 := eq11123 X0
       have j1 := eq2633 X0
       grind)
    | exact resolve eq11123 eq2633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2633
  have eq11207 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k X0 (k X0 X0)) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq11152 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11152
  have eq11262 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (k (M.op X0 X0) X1)) ∨ (k X0 (k X0 X0)) = (M.op (k X0 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (M.op X0 X0) X1
       have i₂ := eq11207 X0
       grind)
    | exact superpose eq11207 eq15
    | (have j1 := eq11207 X0
       grind)
    | exact resolve eq15 eq11207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11207
  have eq11341 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (k (M.op X0 X0) X1)) ∨ (k X0 (k X0 X0)) = (M.op (k X0 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11262 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq11262
    | (have j0 := eq11262 X0 X1
       grind)
    | exact resolve eq11262 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11262
  have eq12049 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (σ (k X0 X0)) ∨ (k X0 (k X0 X0)) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq11341 X0 X0
       have i₂ := eq360 X0
       grind)
    | exact superpose eq360 eq11341
    | (have j0 := eq11341 X0 x
       grind)
    | exact resolve eq11341 eq360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11341
  have eq13031 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (k X0 (k X0 X0)) = (M.op (k X0 X0) X0) ∨ (k X0 (k X0 X0)) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq11123 X0
       have i₂ := eq12049 X0
       grind)
    | exact superpose eq12049 eq11123
    | (have j0 := eq11123 X0
       have j1 := eq12049 X0
       grind)
    | exact resolve eq11123 eq12049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11123 eq12049
  have eq13078 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op (k X0 X0) X0) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq13031 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13031
  have eq13179 : ∀ X0 : G, (k X0 (σ (k (τ X0) (τ X0)))) = (σ (M.op (k (τ X0) (τ X0)) (τ X0))) ∨ (σ (τ X0)) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (k (τ X0) (τ X0))
       have i₂ := eq13078 (τ X0)
       grind)
    | exact superpose eq13078 eq19
    | (have j1 := eq13078 (τ X0)
       grind)
    | exact resolve eq19 eq13078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq13078
  have eq13230 : ∀ X0 : G, (k X0 (σ (τ (k X0 X0)))) = (σ (M.op (τ (k X0 X0)) (τ X0))) ∨ (σ (τ X0)) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq13179 X0
       have i₂ := eq33 X0 X0
       grind)
    | exact superpose eq33 eq13179
    | (have j0 := eq13179 X0
       grind)
    | exact resolve eq13179 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13179
  have eq13288 : ∀ X0 : G, (k X0 (k X0 X0)) = (σ (M.op (τ (k X0 X0)) (τ X0))) ∨ (σ (τ X0)) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq13230 X0
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq13230
    | (have j0 := eq13230 X0
       grind)
    | exact resolve eq13230 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13230
  have eq13339 : ∀ X0 : G, (σ (τ X0)) = (k (σ (τ X0)) X0) ∨ (k X0 (k X0 X0)) = (σ (M.op (τ (k X0 X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq13288 X0
       have i₂ := eq20 X0 (τ X0)
       grind)
    | exact superpose eq20 eq13288
    | (have j0 := eq13288 X0
       grind)
    | exact resolve eq13288 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13288
  have eq13388 : ∀ X0 : G, (k X0 (k X0 X0)) = (σ (M.op (τ (k X0 X0)) (τ X0))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq13339 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq13339
    | (have j0 := eq13339 X0
       grind)
    | exact resolve eq13339 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13339
  have eq13553 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq13388 x
       have i₂ := eq14 x x
       grind)
    | exact superpose eq14 eq13388
    | (have j1 := eq14 X0 X0
       grind)
    | exact resolve eq13388 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13388
  have eq13648 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13553 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13553
  have eq13675 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (M.op X0 X0) X0) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) := by
    intro X0
    grind
  clear eq13648
  have eq14018 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (M.op (σ (k X0 X0)) (σ X0)) = (σ (M.op (τ (σ (k X0 X0))) (τ (σ X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13675 (σ x)
       have i₂ := eq289 x x
       grind)
    | exact superpose eq289 eq13675
    | (have j0 := eq13675 (σ X0)
       have j1 := eq289 X0 X0
       grind)
    | exact resolve eq13675 eq289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13675
  have eq14060 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (M.op (σ (k X0 X0)) (σ X0)) = (σ (M.op (τ (σ (k X0 X0))) (τ (σ X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq14018 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14018
  have eq14076 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (M.op (τ (σ (k X0 X0))) (τ (σ X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq14060 X0
       have j1 := eq901 X0
       grind)
    | (have r₁ := eq14060 X0
       have r₂ := eq901 X0
       grind)
    | exact resolve eq14060 eq901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14060
  have eq14087 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (M.op (τ (σ (k X0 X0))) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq14076 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq14076
    | (have j0 := eq14076 X0
       grind)
    | exact resolve eq14076 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14076
  have eq14088 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (M.op (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq14087 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq14087
    | (have j0 := eq14087 X0
       grind)
    | exact resolve eq14087 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14087
  have eq25175 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ (M.op (k X0 X0) X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq893 X0 X0
       have i₂ := eq14088 X0
       grind)
    | exact superpose eq14088 eq893
    | (have j0 := eq893 X0 X0
       have j1 := eq14088 X0
       grind)
    | exact resolve eq893 eq14088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq893 eq14088
  have eq25184 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ (M.op (k X0 X0) X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq25175 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25175
  have eq47820 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (σ (M.op (k (τ X0) (τ X0)) (τ X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq25184 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25184
    | exact resolve eq25184 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47904 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (σ (M.op (τ (k X0 X0)) (τ X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq47820 X0
       have i₂ := eq33 X0 X0
       grind)
    | exact superpose eq33 eq47820
    | (have j0 := eq47820 X0
       grind)
    | exact resolve eq47820 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq47820
  have eq47944 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (σ (M.op (τ (M.op X0 X0)) (τ X0)))) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq47904 X0
       have i₂ := eq4591 X0 X0
       grind)
    | exact superpose eq4591 eq47904
    | (have j0 := eq47904 X0
       have j1 := eq4591 X0 X0
       grind)
    | exact resolve eq47904 eq4591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4591 eq47904
  have eq48024 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (σ (M.op (τ (M.op X0 X0)) (τ X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq47944 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47944
  have eq48103 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ (M.op (τ (σ (k X0 X0))) (τ (σ X0))))) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq48024 (σ x)
       have i₂ := eq289 x x
       grind)
    | exact superpose eq289 eq48024
    | (have j0 := eq48024 (σ X0)
       have j1 := eq289 X0 X0
       grind)
    | exact resolve eq48024 eq289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289 eq48024
  have eq48169 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ (M.op (τ (σ (k X0 X0))) (τ (σ X0))))) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq48103 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48103
  have eq48182 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ (M.op (τ (σ (k X0 X0))) (τ (σ X0))))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq48169 X0
       have j1 := eq901 X0
       grind)
    | (have r₁ := eq48169 X0
       have r₂ := eq901 X0
       grind)
    | exact resolve eq48169 eq901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901 eq48169
  have eq48188 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ (M.op (τ (σ (k X0 X0))) X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq48182 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq48182
    | (have j0 := eq48182 X0
       grind)
    | exact resolve eq48182 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48182
  have eq48192 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ (M.op (k X0 X0) X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq48188 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq48188
    | (have j0 := eq48188 X0
       grind)
    | exact resolve eq48188 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48188
  have eq48285 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq25184 X0
       have i₂ := eq48192 X0
       grind)
    | exact superpose eq48192 eq25184
    | (have j0 := eq25184 X0
       have j1 := eq48192 X0
       grind)
    | exact resolve eq25184 eq48192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25184 eq48192
  have eq48295 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq48285 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48285
  have eq48399 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq360 (σ X0)
       have i₂ := eq48295 X0
       grind)
    | exact superpose eq48295 eq360
    | (have j1 := eq48295 X0
       grind)
    | exact resolve eq360 eq48295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48295
  have eq48462 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq48399 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq48399
    | (have j0 := eq48399 X0
       grind)
    | exact resolve eq48399 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48399
  have eq48463 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq48462 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48462
  have eq48526 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq48463 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq48463
    | exact resolve eq48463 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48624 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ X0) (σ (k X0 X0))) := by
    intro X0
    grind
  have eq48629 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq360 (σ X0)
       have i₂ := eq48463 X0
       grind)
    | exact superpose eq48463 eq360
    | exact resolve eq360 eq48463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48824 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq48629 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq48629
    | exact resolve eq48629 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48629
  have eq48826 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq48624 X0
       have i₂ := eq15 X0 (k X0 X0)
       grind)
    | exact superpose eq15 eq48624
    | exact resolve eq48624 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48624
  have eq48898 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq48526 X0
       have i₂ := eq20 X0 (τ X0)
       grind)
    | exact superpose eq20 eq48526
    | exact resolve eq48526 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq48526
  have eq49041 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq48898 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq48898
    | exact resolve eq48898 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48898
  have eq50618 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq48824 X0
       have i₂ := eq49041 X0
       grind)
    | exact superpose eq49041 eq48824
    | exact resolve eq48824 eq49041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48824
  have eq50700 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq50618 X0
       have i₂ := eq360 X0
       grind)
    | exact superpose eq360 eq50618
    | exact resolve eq50618 eq360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360 eq50618
  have eq51071 : ∀ X0 : G, (σ (k X0 (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq48826 X0
       have i₂ := eq49041 X0
       grind)
    | exact superpose eq49041 eq48826
    | exact resolve eq48826 eq49041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48826
  have eq51269 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  clear eq51071
  have eq589687 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq50700 x
       have i₂ := eq6746
       grind)
    | exact superpose eq6746 eq50700
    | exact resolve eq50700 eq6746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6746
  have eq589791 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq589687
       have r₂ := eq16
       grind)
    | exact resolve eq589687 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589687
  have eq590151 : (σ y) = (σ (k x x)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq589791
       have i₂ := eq48463 x
       grind)
    | exact superpose eq48463 eq589791
    | exact resolve eq589791 eq48463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589791
  have eq590446 : (σ y) = (σ (M.op x x)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq590151
       have i₂ := eq49041 x
       grind)
    | exact superpose eq49041 eq590151
    | exact resolve eq590151 eq49041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590151
  have eq590728 : (σ x) = (σ (k y y)) ∨ (σ y) = (σ (M.op x x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq590446
       have i₂ := eq48463 y
       grind)
    | exact superpose eq48463 eq590446
    | exact resolve eq590446 eq48463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48463 eq590446
  have eq590953 : x = (M.op y y) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq590728
       have i₂ := eq49041 y
       grind)
    | exact superpose eq49041 eq590728
    | exact resolve eq590728 eq49041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49041 eq590728
  have eq591497 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq51269 y
       have i₂ := eq590953
       grind)
    | exact superpose eq590953 eq51269
    | exact resolve eq51269 eq590953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590953
  have eq591549 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq591497
       have r₂ := eq16
       grind)
    | exact resolve eq591497 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591497
  have eq591916 : (M.op x x) = (τ (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq591549
       grind)
    | exact superpose eq591549 eq10
    | exact resolve eq10 eq591549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591549
  have eq592406 : y = (M.op x x) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq591916
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq591916
    | exact resolve eq591916 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591916
  have eq593153 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq50700 x
       have i₂ := eq592406
       grind)
    | exact superpose eq592406 eq50700
    | exact resolve eq50700 eq592406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50700 eq592406
  have eq593210 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq593153
       have r₂ := eq16
       grind)
    | exact resolve eq593153 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593153
  have eq593550 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq593210
       grind)
    | exact superpose eq593210 eq10
    | exact resolve eq10 eq593210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593210
  have eq594041 : x = (M.op y y) := by
    first
    | (have i₁ := eq593550
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq593550
    | exact resolve eq593550 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593550
  have eq594887 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq51269 y
       have i₂ := eq594041
       grind)
    | exact superpose eq594041 eq51269
    | exact resolve eq51269 eq594041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51269 eq594041
  have eq594939 : False := by grind
  exact eq594939

/-- `Equation3461`: `x ◇ x = x ◇ ((y ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pxy_x_pxy_x_pxy_Equation3461 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3461 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3461.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq54 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq54 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq54
    | (have j0 := eq54 (σ X0) (σ X1)
       grind)
    | exact resolve eq54 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq54 X0 (τ X1)
       grind)
    | exact superpose eq54 eq18
    | (have j1 := eq54 X0 (τ X1)
       grind)
    | exact resolve eq18 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq109 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq65 x y
       grind)
    | exact superpose eq65 eq16
    | (have j1 := eq65 x y
       grind)
    | exact resolve eq16 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq65 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq294 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq71 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq71
    | exact resolve eq71 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq302 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op (τ X1) X0) = X0 ∨ (k X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (τ X1)
       have i₂ := eq71 X0 X1
       grind)
    | exact superpose eq71 eq13
    | (have j0 := eq13 X0 (τ X1)
       have j1 := eq71 X0 X1
       grind)
    | (have r₁ := eq13 X0 (τ X1)
       have r₂ := eq71 X0 X1
       grind)
    | exact resolve eq13 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq303 : ∀ X0 X1 : G, (M.op (τ X1) X0) ≠ X0 ∨ (k X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (τ X1)
       have i₂ := eq71 X0 X1
       grind)
    | exact superpose eq71 eq12
    | (have j1 := eq71 X0 X1
       grind)
    | exact resolve eq12 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq310 : ∀ X0 X1 : G, (M.op (τ X1) X0) = X0 ∨ (k X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq302 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302
  have eq324 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq294 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq294
    | (have j0 := eq294 X0 X1
       grind)
    | exact resolve eq294 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294
  have eq419 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq109
       have i₂ := eq54 x y
       grind)
    | exact superpose eq54 eq109
    | (have j1 := eq54 (σ x) (σ y)
       grind)
    | exact resolve eq109 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq420 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq419
  have eq422 : x ≠ x ∨ x = (M.op y x) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq420
       grind)
    | exact superpose eq420 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq420
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq420
       grind)
    | exact resolve eq13 eq420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420
  have eq424 : x = (k x y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq422
  have eq2330 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq114 x y
       have i₂ := eq424
       grind)
    | exact superpose eq424 eq114
    | (have j0 := eq114 x y
       grind)
    | exact resolve eq114 eq424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq424
  have eq2333 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq2330
  have eq2334 : x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2333
  have eq2410 : x ≠ (M.op x y) ∨ (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq2334
       grind)
    | exact superpose eq2334 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq2334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2334
  have eq2419 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq54 x y
       grind)
    | (have r₁ := eq2410
       have r₂ := eq54 x y
       grind)
    | exact resolve eq2410 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq2410
  have eq2552 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq109
       have i₂ := eq2419
       grind)
    | exact superpose eq2419 eq109
    | exact resolve eq109 eq2419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq2419
  have eq2558 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2552
  have eq2559 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2558
  have eq2675 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2559
       grind)
    | exact superpose eq2559 eq16
    | exact resolve eq16 eq2559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2710 : (σ x) ≠ (σ x) ∨ (σ (M.op x y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq2675
       have i₂ := eq324 y x
       grind)
    | exact superpose eq324 eq2675
    | (have j1 := eq324 y x
       grind)
    | exact resolve eq2675 eq324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324
  have eq2711 : (σ (M.op x y)) = (σ (k x y)) := by grind
  clear eq2710
  have eq2768 : (k x y) = (τ (σ (M.op x y))) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq2711
       grind)
    | exact superpose eq2711 eq10
    | exact resolve eq10 eq2711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2711
  have eq2824 : (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq2768
       have i₂ := eq10 (M.op x y)
       grind)
    | exact superpose eq10 eq2768
    | exact resolve eq2768 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2768
  have eq3132 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq310 X0 X1
       have j1 := eq303 X0 X1
       grind)
    | (have r₁ := eq310 X0 X1
       have r₂ := eq303 X0 X1
       grind)
    | exact resolve eq310 eq303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303 eq310
  have eq3168 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (τ X1))) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (τ X1)
       have i₂ := eq3132 (τ X0) X1
       grind)
    | exact superpose eq3132 eq17
    | (have j1 := eq3132 (τ X0) X1
       grind)
    | exact resolve eq17 eq3132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq3132
  have eq3192 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3168 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq3168
    | (have j0 := eq3168 X0 X1
       grind)
    | exact resolve eq3168 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3168
  have eq3212 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3192 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3192
    | (have j0 := eq3192 X0 X1
       grind)
    | exact resolve eq3192 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3192
  have eq3221 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3212 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3212
    | (have j0 := eq3212 X0 X1
       grind)
    | exact resolve eq3212 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3212
  have eq3493 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X1))
       have i₂ := eq3221 X0 X1
       grind)
    | exact superpose eq3221 eq10
    | (have j1 := eq3221 X0 X1
       grind)
    | exact resolve eq10 eq3221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3221
  have eq3571 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (M.op (τ X1) X0) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3493 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3493
    | (have j0 := eq3493 X1 (σ X0)
       grind)
    | exact resolve eq3493 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3493
  have eq3643 : ∀ X0 X1 : G, (k (τ X1) X0) = (M.op (τ X1) X0) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3571 X0 X1
       have i₂ := eq22 X1 X0
       grind)
    | exact superpose eq22 eq3571
    | (have j0 := eq3571 X0 X1
       grind)
    | exact resolve eq3571 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq3571
  have eq3776 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3643 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3643
    | (have j0 := eq3643 X1 (σ X0)
       grind)
    | exact resolve eq3643 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3643
  have eq3840 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3776 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3776
    | (have j0 := eq3776 X0 X1
       grind)
    | exact resolve eq3776 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3776
  have eq3962 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq3840 X0 X1
       grind)
    | exact superpose eq3840 eq10
    | (have j1 := eq3840 X0 X1
       grind)
    | exact resolve eq10 eq3840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3840
  have eq4024 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3962 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3962
    | (have j0 := eq3962 X0 X1
       grind)
    | exact resolve eq3962 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3962
  have eq4118 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq4024 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4024
  have eq4155 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq4118 (σ x) (σ y)
       have i₂ := eq2559
       grind)
    | exact superpose eq2559 eq4118
    | (have j0 := eq4118 (σ x) (σ y)
       grind)
    | (have r₁ := eq4118 (σ x) (σ y)
       have r₂ := eq2559
       grind)
    | exact resolve eq4118 eq2559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2559 eq4118
  have eq4173 : (σ x) = (k (σ x) (σ y)) := by grind
  clear eq4155
  have eq4187 : (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq4173
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq4173
    | exact resolve eq4173 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4173
  have eq4197 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq4187
       have i₂ := eq2824
       grind)
    | exact superpose eq2824 eq4187
    | exact resolve eq4187 eq2824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2824 eq4187
  have eq4200 : False := by grind
  exact eq4200

/-- `Equation3475`: `x ◇ x = y ◇ ((x ◇ y) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(Y,Y) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pyx_pyx_pxy_Equation3475 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3475 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3475.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X1 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq12 eq13
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
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
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
  have eq60 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 x)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq15
    | exact resolve eq15 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 y)
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq15
    | exact resolve eq15 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq60 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq60
    | exact resolve eq60 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq153 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq73 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq73
    | exact resolve eq73 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq1017 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq28
    | (have j0 := eq28 X1 X0
       have j1 := eq11 X0 X0
       grind)
    | (have r₁ := eq28 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq28 X0 X0
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1018 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq11 X0 X0
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq13 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1019 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X1) X1)) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1023 : (M.op x y) = (k x y) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq18
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1026 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11 sF2 sF3
       grind)
    | exact superpose eq11 eq26
    | (have j1 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1033 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X1) X1)) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1019 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1019
  have eq1034 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1018 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1018
  have eq1035 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1017 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1017
  have eq1037 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1034 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq1034 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq1034 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1034
  have eq1038 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1035 X0 X1
       have j1 := eq28 X1 X0
       grind)
    | (have r₁ := eq1035 X1 X1
       have r₂ := eq28 X0 X1
       grind)
    | exact resolve eq1035 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1035
  have eq2806 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq1023
       grind)
    | exact superpose eq1023 eq41
    | exact resolve eq41 eq1023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1023
  have eq2807 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2806
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2806
    | exact resolve eq2806 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2806
  have eq2809 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq2807
    | exact resolve eq2807 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2807
  have eq10607 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 x
       have i₂ := eq1033 X0 x
       grind)
    | exact superpose eq1033 eq16
    | (have j1 := eq1033 X0 x
       grind)
    | exact resolve eq16 eq1033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1033
  have eq10649 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq10607 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq10607 X0
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq10607 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10607
  have eq17086 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq2809 eq1026
    | exact resolve eq1026 eq2809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1026 eq2809
  have eq17097 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq17086
       have r₂ := eq27
       grind)
    | exact resolve eq17086 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17086
  have eq17103 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq17097
       have i₂ := eq10649 sF3
       grind)
    | exact superpose eq10649 eq17097
    | exact resolve eq17097 eq10649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17097
  have eq17107 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq17103
       have i₂ := eq10649 sF2
       grind)
    | exact superpose eq10649 eq17103
    | exact resolve eq17103 eq10649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17103
  have eq17109 : y = (k y y) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq17107
       have i₂ := eq10649 y
       grind)
    | exact superpose eq10649 eq17107
    | exact resolve eq17107 eq10649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17107
  have eq17111 : (σ y) = (k (σ y) (σ y)) ∨ y = (k y y) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq17109
       have i₂ := eq10649 x
       grind)
    | exact superpose eq10649 eq17109
    | exact resolve eq17109 eq10649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10649 eq17109
  have eq17432 : (τ (σ y)) = (k (τ (σ y)) y) ∨ y = (k y y) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | exact superpose eq17111 eq153
    | exact resolve eq153 eq17111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq17111
  have eq17445 : y = (k y y) ∨ y = (k y y) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | exact superpose eq32 eq17432
    | exact resolve eq17432 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq17432
  have eq17446 : (σ x) = (k (σ x) (σ x)) ∨ y = (k y y) ∨ x = (k x x) := by grind
  clear eq17445
  have eq17459 : (τ (σ x)) = (k (τ (σ x)) x) ∨ y = (k y y) ∨ x = (k x x) := by
    first
    | exact superpose eq17446 eq142
    | exact resolve eq142 eq17446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq17446
  have eq17472 : x = (k x x) ∨ y = (k y y) ∨ x = (k x x) := by
    first
    | exact superpose eq30 eq17459
    | exact resolve eq17459 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq17459
  have eq17473 : y = (k y y) ∨ x = (k x x) := by grind
  clear eq17472
  have eq17485 : (σ y) = (k (σ y) (σ y)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq17473
       grind)
    | exact superpose eq17473 eq41
    | exact resolve eq41 eq17473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq17487 : ∀ X0 : G, y ≠ y ∨ (k y X0) = (M.op X0 y) ∨ x = (k x x) := by
    intro X0
    first
    | (have i₁ := eq1037 y X0
       have i₂ := eq17473
       grind)
    | exact superpose eq17473 eq1037
    | (have j0 := eq1037 y X0
       grind)
    | (have r₁ := eq1037 y x
       have r₂ := eq17473
       grind)
    | (have r₁ := eq1037 x x
       have r₂ := eq17473
       grind)
    | exact resolve eq1037 eq17473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17473
  have eq17493 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ x = (k x x) := by
    intro X0
    first
    | (have j0 := eq17487 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17487
  have eq17498 : (σ y) = (k (σ y) (σ y)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq17485
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq17485
    | exact resolve eq17485 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17485
  have eq17513 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ x = (k x x) := by
    intro X0
    first
    | exact superpose eq17498 eq1037
    | (have j0 := eq1037 (σ y) X0
       grind)
    | (have r₁ := eq1037 (σ y) x
       have r₂ := eq17498
       grind)
    | (have r₁ := eq1037 x x
       have r₂ := eq17498
       grind)
    | exact resolve eq1037 eq17498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1037 eq17498
  have eq17519 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ x = (k x x) := by
    intro X0
    first
    | (have j0 := eq17513 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17513
  have eq17737 : (M.op x y) = (k y x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq17493 x
       grind)
    | exact superpose eq17493 eq18
    | (have j1 := eq17493 x
       grind)
    | exact resolve eq18 eq17493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17493
  have eq17830 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq17737
       grind)
    | exact superpose eq17737 eq40
    | exact resolve eq40 eq17737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17737
  have eq17831 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq17830
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq17830
    | exact resolve eq17830 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17830
  have eq17835 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k x x) := by
    first
    | exact superpose eq20 eq17831
    | exact resolve eq17831 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17831
  have eq18488 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (k x x) := by
    first
    | exact superpose eq17519 eq26
    | (have j1 := eq17519 (σ x)
       grind)
    | exact resolve eq26 eq17519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17519
  have eq18494 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
    first
    | exact superpose eq17835 eq18488
    | exact resolve eq18488 eq17835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17835 eq18488
  have eq18537 : x = (k x x) := by
    first
    | (have r₁ := eq18494
       have r₂ := eq27
       grind)
    | exact resolve eq18494 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18494
  have eq18568 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq18537
       grind)
    | exact superpose eq18537 eq40
    | exact resolve eq40 eq18537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18571 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq1038 x X0
       have i₂ := eq18537
       grind)
    | exact superpose eq18537 eq1038
    | (have j0 := eq1038 x X0
       grind)
    | (have r₁ := eq1038 x x
       have r₂ := eq18537
       grind)
    | exact resolve eq1038 eq18537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18537
  have eq18577 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq18571 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18571
  have eq18584 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq18568
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18568
    | exact resolve eq18568 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq18568
  have eq18602 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq18584 eq1038
    | (have j0 := eq1038 (σ x) X0
       grind)
    | (have r₁ := eq1038 (σ x) x
       have r₂ := eq18584
       grind)
    | exact resolve eq1038 eq18584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1038 eq18584
  have eq18608 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq18602 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18602
  have eq18638 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq18577 y
       grind)
    | exact superpose eq18577 eq18
    | (have j1 := eq18577 y
       grind)
    | exact resolve eq18 eq18577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq18577
  have eq18786 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq18638
       grind)
    | exact superpose eq18638 eq40
    | exact resolve eq40 eq18638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq18638
  have eq18789 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq18786
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq18786
    | exact resolve eq18786 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq18786
  have eq18794 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq20 eq18789
    | exact resolve eq18789 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq18789
  have eq18968 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq18608 eq26
    | (have j1 := eq18608 (σ y)
       grind)
    | exact resolve eq26 eq18608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq18608
  have eq19040 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18794 eq18968
    | exact resolve eq18968 eq18794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18794 eq18968
  have eq19079 : False := by grind
  exact eq19079

/-- `Equation3479`: `x ◇ x = y ◇ ((x ◇ z) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxy_pyx_pxy_pyx_pxy_Equation3479 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3479 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3479.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X0 X2) X2)) := by
    intro X0 X1 X2
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
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
  have eq23 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2 (M.op (M.op X0 x) x)
       have i₂ := eq9 X0 (M.op X1 (M.op (M.op X0 x) x)) x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq23 x X0 x
       have i₂ := eq23 x X1 x
       grind)
    | (have i₁ := eq23 X0 X1 (M.op X0 X0)
       have i₂ := eq23 X0 (M.op X0 X0) x
       grind)
    | exact superpose eq23 eq23
    | exact resolve eq23 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq68 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq34 X0 X1
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq34 X1 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq34 X0 X0
       grind)
    | exact resolve eq12 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq79 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq68 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq89 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq79 (σ X0)
       grind)
    | exact superpose eq79 eq15
    | exact resolve eq15 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq89 X0
       have i₂ := eq79 X0
       grind)
    | exact superpose eq79 eq89
    | exact resolve eq89 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq112 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X1
       have i₂ := eq82 X0 (σ X1)
       grind)
    | exact superpose eq82 eq15
    | exact resolve eq15 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq115 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq112 X0 X1
       have i₂ := eq79 X1
       grind)
    | exact superpose eq79 eq112
    | exact resolve eq112 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq112
  have eq163 : ∀ X0 X1 X2 : G, (M.op X1 X2) ≠ (σ (M.op X0 X0)) ∨ (M.op X1 X2) = (k X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X2
       have i₂ := eq115 X2 X0
       grind)
    | exact superpose eq115 eq12
    | (have j0 := eq12 X1 X2
       grind)
    | exact resolve eq12 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq181 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
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
  have eq182 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq181 X0 X1
       have i₂ := eq90 X1
       grind)
    | exact superpose eq90 eq181
    | (have j0 := eq181 X0 X1
       grind)
    | exact resolve eq181 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq181
  have eq2785 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq182 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq182 X0 X1
       grind)
    | exact superpose eq182 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq182 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq182 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq182 X0 X1
       grind)
    | exact resolve eq13 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq2797 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2785 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2785
  have eq2804 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2797 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq2797 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq2797 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | exact resolve eq2797 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2797
  have eq2822 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2804 X0 X1
       have j1 := eq163 X0 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq2804 X0 X0
       have r₂ := eq163 X0 (σ X0) (σ X0)
       grind)
    | exact resolve eq2804 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163 eq2804
  have eq2835 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2822 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2822
    | (have j0 := eq2822 X0 X1
       grind)
    | exact resolve eq2822 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2822
  have eq2836 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2835 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2835
  have eq2851 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2836 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2836
    | exact resolve eq2836 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2884 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2836 x y
       grind)
    | exact superpose eq2836 eq16
    | exact resolve eq16 eq2836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2836
  have eq3177 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq2851 X0 (τ X1)
       grind)
    | exact superpose eq2851 eq18
    | exact resolve eq18 eq2851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2851
  have eq3190 : ∀ X0 X1 : G, (M.op X0 X1) = (k (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3177 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq3177
    | exact resolve eq3177 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3177
  have eq3211 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3190 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3190
    | exact resolve eq3190 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3190
  have eq3256 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq2884
       have i₂ := eq3211 x y
       grind)
    | exact superpose eq3211 eq2884
    | exact resolve eq2884 eq3211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2884 eq3211
  have eq3257 : False := by grind
  exact eq3257

/-- `Equation3600`: `x ◇ y = z ◇ ((y ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation3600 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3600 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3600.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
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
  have eq29 : x = (τ (σ x)) := by
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
  have eq41 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq20
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
  clear eq35
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
  have eq174 : y ≠ (M.op x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X2 (M.op (M.op X1 X0) X1) X3
       have i₂ := eq16 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq179 X0 X1 x X3
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq179
    | exact resolve eq179 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq192 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq181 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq181
    | (have j0 := eq181 x y X0
       grind)
    | exact resolve eq181 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq181
    | (have j0 := eq181 (σ x) (σ y) X0
       grind)
    | exact resolve eq181 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq211 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (k X0 (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq192 eq13
    | (have j0 := eq13 X0 (M.op x y)
       grind)
    | (have r₁ := eq13 X0 (M.op x y)
       have r₂ := eq192 X0
       grind)
    | exact resolve eq13 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq213 : ∀ X0 : G, (k X0 (M.op x y)) = X0 := by
    intro X0
    first
    | (have j0 := eq211 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq217 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k X0 (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq193 eq13
    | (have j0 := eq13 X0 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq13 X0 (M.op (σ x) (σ y))
       have r₂ := eq193 X0
       grind)
    | exact resolve eq13 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq219 : ∀ X0 : G, (k X0 (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | (have j0 := eq217 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq221 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq213 eq41
    | exact resolve eq41 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq213
  have eq281 : ∀ X0 : G, (k X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq221 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq221
    | exact resolve eq221 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq402 : x ≠ (M.op x y) ∨ y = (M.op x y) ∨ y = (k x y) := by
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
  have eq404 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq411 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
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
  clear eq18
  have eq413 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq416 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq11 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq11 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq13 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq453 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq416 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq416 X0 X0
       have r₂ := eq13 X0 X0
       grind)
    | (have r₁ := eq416 X1 X1
       have r₂ := eq13 X1 X1
       grind)
    | (have r₁ := eq416 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq416 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416
  have eq472 : (τ (σ x)) = (k x (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq219 eq90
    | exact resolve eq90 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq483 : x = (k x (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq29 eq472
    | exact resolve eq472 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq472
  have eq1563 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq411
       grind)
    | exact superpose eq411 eq40
    | exact resolve eq40 eq411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1564 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1563
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1563
    | exact resolve eq1563 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1563
  have eq1566 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq1564
    | exact resolve eq1564 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1564
  have eq3342 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1566 eq413
    | exact resolve eq413 eq1566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3355 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq3342
       have r₂ := eq27
       grind)
    | exact resolve eq3342 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3342
  have eq3369 : x = (k x (τ (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3355 eq483
    | exact resolve eq483 eq3355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483 eq3355
  have eq3427 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq3369
    | exact resolve eq3369 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3369
  have eq3428 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq3427
       have r₂ := eq174
       grind)
    | exact resolve eq3427 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq3427
  have eq3430 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq411
       have i₂ := eq3428
       grind)
    | exact superpose eq3428 eq411
    | exact resolve eq411 eq3428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3432 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq3428
       grind)
    | exact superpose eq3428 eq40
    | exact resolve eq40 eq3428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq3428
  have eq3436 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq3430
  have eq3442 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3432
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3432
    | exact resolve eq3432 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3432
  have eq3448 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3436 eq27
    | exact resolve eq27 eq3436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3454 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3436 eq219
    | exact resolve eq219 eq3436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq3458 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3436 eq404
    | (have r₁ := eq404
       have r₂ := eq3436
       grind)
    | exact resolve eq404 eq3436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3436
  have eq3496 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq3458
  have eq3523 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3442 eq413
    | exact resolve eq413 eq3442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3442
  have eq3530 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq3523
  have eq3545 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3530 eq27
    | exact resolve eq27 eq3530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3530
  have eq4580 : (τ (σ y)) = (k x (τ (σ y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3496 eq90
    | exact resolve eq90 eq3496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq3496
  have eq4605 : y = (k x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq4580
    | exact resolve eq4580 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq4580
  have eq4610 : y = (k x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq4605
       have r₂ := eq402
       grind)
    | exact resolve eq4605 eq402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4605
  have eq4617 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq411
       have i₂ := eq4610
       grind)
    | exact superpose eq4610 eq411
    | exact resolve eq411 eq4610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411 eq4610
  have eq4627 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq4617
  have eq4665 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4627 eq1566
    | exact resolve eq1566 eq4627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1566 eq4627
  have eq4690 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq4665
  have eq4692 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3454 eq4690
    | exact resolve eq4690 eq3454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3454 eq4690
  have eq4704 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq4692
       have r₂ := eq3448
       grind)
    | exact resolve eq4692 eq3448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3448 eq4692
  have eq4713 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq4704
       grind)
    | exact superpose eq4704 eq24
    | exact resolve eq24 eq4704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4704
  have eq4736 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq4713
    | exact resolve eq4713 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4713
  have eq4754 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4736 eq281
    | exact resolve eq281 eq4736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4788 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4736 eq3545
    | (have r₁ := eq3545
       have r₂ := eq4736
       grind)
    | exact resolve eq3545 eq4736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3545
  have eq4789 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq4788
  have eq4790 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq4789
  have eq4817 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4790 eq27
    | exact resolve eq27 eq4790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4827 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4790 eq404
    | (have r₁ := eq404
       have r₂ := eq4790
       grind)
    | exact resolve eq404 eq4790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404 eq4790
  have eq4865 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq4827
  have eq4888 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4754 eq4865
    | exact resolve eq4865 eq4754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4754 eq4865
  have eq4889 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq4888
  have eq4892 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4736 eq4817
    | exact resolve eq4817 eq4736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4736 eq4817
  have eq4893 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by grind
  clear eq4892
  have eq4894 : x = (M.op x y) := by
    first
    | (have r₁ := eq4893
       have r₂ := eq4889
       grind)
    | exact resolve eq4893 eq4889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4889 eq4893
  have eq4896 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq4894
       grind)
    | exact superpose eq4894 eq22
    | exact resolve eq22 eq4894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq4904 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ y = (k (M.op x y) y) := by
    first
    | (have i₁ := eq402
       have i₂ := eq4894
       grind)
    | exact superpose eq4894 eq402
    | (have r₁ := eq402
       have r₂ := eq4894
       grind)
    | exact resolve eq402 eq4894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402 eq4894
  have eq4919 : y = (k (M.op x y) y) ∨ y = (M.op x y) := by grind
  clear eq4904
  have eq4927 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq4896 eq20
    | exact resolve eq20 eq4896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq4993 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq4927 eq281
    | exact resolve eq281 eq4927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq5642 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4919 eq37
    | exact resolve eq37 eq4919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq4919
  have eq5654 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq5642
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq5642
    | exact resolve eq5642 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5642
  have eq5656 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4927 eq5654
    | exact resolve eq5654 eq4927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5654
  have eq5670 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5656 eq413
    | exact resolve eq413 eq5656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5677 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5656 eq453
    | (have j0 := eq453 (σ x) (σ y)
       grind)
    | (have r₁ := eq453 (σ x) (σ y)
       have r₂ := eq5656
       grind)
    | exact resolve eq453 eq5656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453 eq5656
  have eq5681 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq5677
  have eq5683 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq5670
  have eq5691 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq5681
    | exact resolve eq5681 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq5681
  have eq6749 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq5683
  have eq6752 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq6749
       have r₂ := eq5691
       grind)
    | exact resolve eq6749 eq5691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5691 eq6749
  have eq6805 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6752 eq27
    | exact resolve eq27 eq6752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6752
  have eq6879 : y = (M.op x y) := by
    first
    | (have r₁ := eq6805
       have r₂ := eq4927
       grind)
    | exact resolve eq6805 eq4927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6805
  have eq6902 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq6879
       grind)
    | exact superpose eq6879 eq24
    | exact resolve eq24 eq6879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq6879
  have eq6927 : (σ x) = (σ y) := by
    first
    | exact superpose eq4896 eq6902
    | exact resolve eq6902 eq4896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4896 eq6902
  have eq6946 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6927 eq413
    | exact resolve eq413 eq6927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413 eq6927
  have eq6976 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq6946
  have eq6977 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4993 eq6976
    | exact resolve eq6976 eq4993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4993 eq6976
  have eq6978 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq6977
  have eq7016 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq6978 eq27
    | exact resolve eq27 eq6978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq6978
  have eq7089 : False := by grind
  exact eq7089

/-- `Equation3600`: `x ◇ y = z ◇ ((y ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(X,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_x_pyx_pxy_Equation3600 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3600 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3600.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X1 X0) X1) X3
       have i₂ := eq9 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X2 ∨ (M.op (M.op X1 X0) X1) = (k (M.op (M.op X1 X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op (M.op X1 X0) X1) X2
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 (M.op (M.op X1 X0) X1) X2
       grind)
    | (have r₁ := eq12 (M.op (M.op X1 X0) X1) (M.op X0 X1)
       have r₂ := eq9 X0 X1 (M.op X0 X1)
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq62 X0 X1 x X3
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq68 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 x
       have i₂ := eq64 (M.op X0 X1) X0 x
       grind)
    | exact superpose eq64 eq9
    | exact resolve eq9 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X2 ∨ (M.op X0 X1) = (k (M.op X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X0 X1) X2
       have i₂ := eq64 X0 X1 X2
       grind)
    | exact superpose eq64 eq12
    | (have j0 := eq12 (M.op X0 X1) X2
       grind)
    | (have r₁ := eq12 (M.op X0 X1) (M.op X0 X1)
       have r₂ := eq64 X0 X1 (M.op X0 X1)
       grind)
    | exact resolve eq12 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 : G, (k X1 (M.op X1 X0)) = X1 ∨ (M.op X0 X1) ≠ (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X1 X0)
       have i₂ := eq68 X1 X0
       grind)
    | exact superpose eq68 eq12
    | (have j0 := eq12 X1 (M.op X1 X0)
       grind)
    | (have r₁ := eq12 X1 (M.op X1 X1)
       have r₂ := eq68 X1 X1
       grind)
    | exact resolve eq12 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq70 X0 X1 (M.op X0 X1)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) X1))) ∨ (M.op (σ X0) X1) ≠ (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (M.op (σ X0) X1)
       have i₂ := eq80 X1 (σ X0)
       grind)
    | exact superpose eq80 eq28
    | (have j1 := eq80 (σ X0) X1
       grind)
    | exact resolve eq28 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 X1 : G, (M.op (σ X0) X1) ≠ (M.op X1 (σ X0)) ∨ (k X0 (τ (M.op (σ X0) X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq96 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq96
    | (have j0 := eq96 X0 X1
       grind)
    | exact resolve eq96 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq429 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 (M.op X1 X0)) = X1 ∨ (M.op X1 (M.op X1 X0)) = (k (M.op X1 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X1 X0) X1
       have i₂ := eq68 X1 X0
       grind)
    | exact superpose eq68 eq13
    | (have j0 := eq13 (M.op X1 X0) X1
       grind)
    | (have r₁ := eq13 (M.op X1 X1) X1
       have r₂ := eq68 X1 X1
       grind)
    | exact resolve eq13 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq432 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 (M.op X1 X0)) = (k (M.op X1 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq429 X0 X1
       have i₂ := eq64 X1 X0 X1
       grind)
    | exact superpose eq64 eq429
    | (have j0 := eq429 X0 X1
       grind)
    | exact resolve eq429 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429
  have eq436 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X1 X0) X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) ≠ (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq432 X0 X1
       have i₂ := eq64 X1 X0 X1
       grind)
    | exact superpose eq64 eq432
    | (have j0 := eq432 X0 X1
       grind)
    | exact resolve eq432 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432
  have eq439 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k (M.op X1 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq436 X0 X1
       have j1 := eq70 X0 X1 (M.op X1 X0)
       grind)
    | (have r₁ := eq436 X1 X0
       have r₂ := eq70 X0 X1 (k (M.op X0 X1) X0)
       grind)
    | (have r₁ := eq436 X1 x
       have r₂ := eq70 x X1 x
       grind)
    | (have r₁ := eq436 X0 (M.op X0 X1)
       have r₂ := eq70 X0 X1 (M.op (M.op X0 X1) X0)
       grind)
    | exact resolve eq436 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq436
  have eq453 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq439 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq478 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq22 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq453 (σ X0)
       grind)
    | exact superpose eq453 eq22
    | exact resolve eq22 eq453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq578 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq579 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq582 : ∀ X0 X1 X2 : G, (M.op X2 X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 X1 X0 x
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq64
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq64 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq598 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14 (σ y) (σ x)
       grind)
    | exact superpose eq14 eq16
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq601 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq602 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq601 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601
  have eq603 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq579 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579
  have eq604 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq603 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603
  have eq605 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq578 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578
  have eq606 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq598
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq598
    | exact resolve eq598 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598
  have eq652 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq602 (σ X0)
       grind)
    | exact superpose eq602 eq15
    | (have j1 := eq602 (σ X0)
       grind)
    | exact resolve eq15 eq602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602
  have eq680 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k (M.op X1 X0) X1) ∨ (M.op X0 X1) = (k (M.op X1 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq605 X0 (M.op X0 X1)
       have i₂ := eq68 X0 X1
       grind)
    | exact superpose eq68 eq605
    | (have j0 := eq605 X1 (M.op X1 X0)
       grind)
    | exact resolve eq605 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq687 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq605 X1 X0
       grind)
    | exact superpose eq605 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq605 X1 X0
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq605 X0 X1
       grind)
    | exact resolve eq13 eq605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq690 : ∀ X0 X1 X2 : G, (M.op X2 X0) = X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 X1 X0 x
       have i₂ := eq605 X0 X1
       grind)
    | exact superpose eq605 eq64
    | (have j1 := eq605 X1 X0
       grind)
    | exact resolve eq64 eq605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq700 : ∀ X0 : G, (k X0 X0) = X0 ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq453 X0
       have i₂ := eq605 X0 X0
       grind)
    | exact superpose eq605 eq453
    | (have j1 := eq605 X0 X0
       grind)
    | exact resolve eq453 eq605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453 eq605
  have eq709 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq700 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700
  have eq710 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq687 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687
  have eq725 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq710 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq710 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq710 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710
  have eq730 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X1 X0) X1) ∨ (M.op X0 X1) = (k (M.op X1 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq680 X0 X1
       have j1 := eq439 X0 X1
       grind)
    | (have r₁ := eq680 X0 X1
       have r₂ := eq439 X0 X1
       grind)
    | (have r₁ := eq680 X1 X0
       have r₂ := eq439 X0 X1
       grind)
    | exact resolve eq680 eq439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439 eq680
  have eq753 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq709 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq709
    | exact resolve eq709 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709
  have eq807 : ∀ X0 X1 X2 : G, X0 ≠ X2 ∨ (M.op (M.op X1 X0) X1) = (k (M.op (M.op X1 X0) X1) X2) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq63 X0 X1 X2
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq63
    | (have j0 := eq63 X0 X1 X2
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq63 X1 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq63 X0 X1 (M.op (M.op X0 X1) X0)
       have r₂ := eq14 X0 (M.op X0 X1)
       grind)
    | (have r₁ := eq63 X0 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq63 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq818 : ∀ X0 X1 X2 : G, X0 ≠ X2 ∨ (M.op X0 X1) = (k (M.op X0 X1) X2) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq807 X1 X0 X2
       have i₂ := eq68 X0 X1
       grind)
    | exact superpose eq68 eq807
    | (have j0 := eq807 X0 X1 X2
       grind)
    | (have r₁ := eq807 (M.op X1 X0) X1 (M.op (M.op X0 X1) X0)
       have r₂ := eq68 X0 X1
       grind)
    | (have r₁ := eq807 (M.op (M.op X0 X1) X0) X1 (M.op X1 X0)
       have r₂ := eq68 X0 X1
       grind)
    | exact resolve eq807 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq807
  have eq856 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq582 X1 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582
  have eq2591 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X2 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 X1 X0 x
       have i₂ := eq604 X0 X1
       grind)
    | exact superpose eq604 eq64
    | (have j1 := eq604 X1 X0
       grind)
    | exact resolve eq64 eq604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604
  have eq9401 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq652 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652
  have eq9409 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq9401 X0
       have j1 := eq753 X0
       grind)
    | (have r₁ := eq9401 X0
       have r₂ := eq753 X0
       grind)
    | exact resolve eq9401 eq753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq753 eq9401
  have eq9449 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq9409 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq9409
    | exact resolve eq9409 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9491 : ∀ X0 : G, (τ (σ (k X0 X0))) = (k (τ (σ (k X0 X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq478 X0
       have i₂ := eq9409 X0
       grind)
    | exact superpose eq9409 eq478
    | exact resolve eq478 eq9409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9530 : ∀ X0 X1 : G, (σ (k X0 X0)) = (M.op X1 (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq64 (σ X0) (σ X0) x
       have i₂ := eq9409 X0
       grind)
    | exact superpose eq9409 eq64
    | exact resolve eq64 eq9409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9533 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ (k X0 X0))) ∨ (σ (k X0 X0)) ≠ (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq80 (σ X0) (σ X0)
       have i₂ := eq9409 X0
       grind)
    | exact superpose eq9409 eq80
    | exact resolve eq80 eq9409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq9409
  have eq9551 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ (k X0 X0))) := by
    intro X0
    first
    | (have j0 := eq9533 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9533
  have eq9562 : ∀ X0 : G, (σ X0) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq9551 X0
       have i₂ := eq15 X0 (k X0 X0)
       grind)
    | exact superpose eq15 eq9551
    | exact resolve eq9551 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9551
  have eq9593 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq9491 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq9491
    | exact resolve eq9491 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9491
  have eq9622 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq9449 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq9449
    | exact resolve eq9449 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9449
  have eq9646 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq9622 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq9622
    | exact resolve eq9622 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9622
  have eq9752 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq9646 (τ X0)
       grind)
    | exact superpose eq9646 eq31
    | exact resolve eq31 eq9646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9760 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq9752 X0
       have i₂ := eq9646 X0
       grind)
    | exact superpose eq9646 eq9752
    | exact resolve eq9752 eq9646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9752
  have eq9827 : ∀ X0 : G, (σ X0) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq9562 X0
       have i₂ := eq9646 X0
       grind)
    | exact superpose eq9646 eq9562
    | exact resolve eq9562 eq9646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9838 : ∀ X0 : G, (τ (σ X0)) = (k X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 (k X0 X0))
       have i₂ := eq9562 X0
       grind)
    | exact superpose eq9562 eq10
    | exact resolve eq10 eq9562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9839 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (k (k X0 (k X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 (k X0 X0)) X1
       have i₂ := eq9562 X0
       grind)
    | exact superpose eq9562 eq15
    | exact resolve eq15 eq9562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9840 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (k X1 (k X0 (k X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (k X0 (k X0 X0))
       have i₂ := eq9562 X0
       grind)
    | exact superpose eq9562 eq15
    | exact resolve eq15 eq9562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9850 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (k (k X0 (k X0 X0)) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 (k X0 (k X0 X0)) X1
       have i₂ := eq9562 X0
       grind)
    | exact superpose eq9562 eq28
    | exact resolve eq28 eq9562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9562
  have eq9888 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (k (k X0 (M.op X0 X0)) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9850 X0 X1
       have i₂ := eq9646 X0
       grind)
    | exact superpose eq9646 eq9850
    | exact resolve eq9850 eq9646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9850
  have eq9898 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (k X1 (k X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9840 X0 X1
       have i₂ := eq9646 X0
       grind)
    | exact superpose eq9646 eq9840
    | exact resolve eq9840 eq9646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9840
  have eq9899 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (k (k X0 (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9839 X0 X1
       have i₂ := eq9646 X0
       grind)
    | exact superpose eq9646 eq9839
    | exact resolve eq9839 eq9646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9839
  have eq9900 : ∀ X0 : G, (τ (σ X0)) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq9838 X0
       have i₂ := eq9646 X0
       grind)
    | exact superpose eq9646 eq9838
    | exact resolve eq9838 eq9646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9838
  have eq9925 : ∀ X0 X1 : G, (k X0 (τ X1)) = (k (k X0 (M.op X0 X0)) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9888 X0 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq9888
    | exact resolve eq9888 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9888
  have eq9935 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (k X1 (k X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9898 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq9898
    | exact resolve eq9898 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9898
  have eq9936 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (k (k X0 (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9899 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq9899
    | exact resolve eq9899 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9899
  have eq9937 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9900 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9900
    | exact resolve eq9900 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9900
  have eq10594 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq64 (τ X0) (τ X0) x
       have i₂ := eq9760 X0
       grind)
    | exact superpose eq9760 eq64
    | exact resolve eq64 eq9760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9760
  have eq10776 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (M.op X2 (σ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9530 (M.op X0 X1) X1
       have i₂ := eq89 X0 X1
       grind)
    | exact superpose eq89 eq9530
    | exact resolve eq9530 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq9530
  have eq11155 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = X2 ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) X2) ∨ (M.op (σ (M.op X0 X1)) X2) = (k (σ (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (σ (M.op X0 X1)) X2
       have i₂ := eq10776 X0 X1 X2
       grind)
    | exact superpose eq10776 eq14
    | (have j0 := eq14 (σ (M.op X0 X1)) X2
       grind)
    | exact resolve eq14 eq10776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11208 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) X2) ∨ (M.op (σ (M.op X0 X1)) X2) = (k (σ (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq11155 X0 X1 X2
       have j1 := eq856 (σ (M.op X0 X1)) X2
       grind)
    | (have r₁ := eq11155 X0 X1 X1
       have r₂ := eq856 (σ (M.op X0 X1)) X1
       grind)
    | (have r₁ := eq11155 X0 X1 X0
       have r₂ := eq856 X0 (σ (M.op X0 X1))
       grind)
    | (have r₁ := eq11155 X0 X1 X2
       have r₂ := eq856 (σ (M.op X0 X1)) (M.op (σ (M.op X0 X1)) X2)
       grind)
    | exact resolve eq11155 eq856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11155
  have eq11266 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) = (M.op X2 (τ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10594 (M.op X0 X1) X1
       have i₂ := eq64 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq64 eq10594
    | exact resolve eq10594 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10594
  have eq11482 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) = X2 ∨ (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) X2) ∨ (M.op (τ (M.op X0 X1)) X2) = (k (τ (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (τ (M.op X0 X1)) X2
       have i₂ := eq11266 X0 X1 X2
       grind)
    | exact superpose eq11266 eq14
    | (have j0 := eq14 (τ (M.op X0 X1)) X2
       grind)
    | exact resolve eq14 eq11266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11530 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) X2) ∨ (M.op (τ (M.op X0 X1)) X2) = (k (τ (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq11482 X0 X1 X2
       have j1 := eq856 (τ (M.op X0 X1)) X2
       grind)
    | (have r₁ := eq11482 X0 X1 X1
       have r₂ := eq856 (τ (M.op X0 X1)) X1
       grind)
    | (have r₁ := eq11482 X0 X1 X0
       have r₂ := eq856 X0 (τ (M.op X0 X1))
       grind)
    | (have r₁ := eq11482 X0 X1 X2
       have r₂ := eq856 (τ (M.op X0 X1)) (M.op (τ (M.op X0 X1)) X2)
       grind)
    | exact resolve eq11482 eq856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856 eq11482
  have eq22319 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X0 X1) X0) ∨ (M.op X0 X1) ≠ (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq730 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730
  have eq22416 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 X1)) X2) = (k (σ (M.op X0 X1)) X2) ∨ (σ (M.op X0 X1)) ≠ (M.op (σ (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22319 X2 (σ (M.op X0 X1))
       have i₂ := eq10776 X0 X1 X2
       grind)
    | exact superpose eq10776 eq22319
    | exact resolve eq22319 eq10776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22431 : ∀ X0 X1 X2 : G, (M.op (τ (M.op X0 X1)) X2) = (k (τ (M.op X0 X1)) X2) ∨ (τ (M.op X0 X1)) ≠ (M.op (τ (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22319 X2 (τ (M.op X0 X1))
       have i₂ := eq11266 X0 X1 X2
       grind)
    | exact superpose eq11266 eq22319
    | exact resolve eq22319 eq11266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22319
  have eq22479 : ∀ X0 X1 X2 : G, (M.op (τ (M.op X0 X1)) X2) = (k (τ (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq22431 X0 X1 X2
       have j1 := eq11530 X0 X1 X2
       grind)
    | (have r₁ := eq22431 X0 X1 X2
       have r₂ := eq11530 X0 X1 X2
       grind)
    | exact resolve eq22431 eq11530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11530 eq22431
  have eq22494 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 X1)) X2) = (k (σ (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq22416 X0 X1 X2
       have j1 := eq11208 X0 X1 X2
       grind)
    | (have r₁ := eq22416 X0 X1 X2
       have r₂ := eq11208 X0 X1 X2
       grind)
    | exact resolve eq22416 eq11208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11208 eq22416
  have eq22621 : ∀ X0 X1 X3 : G, (k (σ (τ (M.op X0 X1))) X3) = (M.op (σ (τ (M.op X0 X1))) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq22494 x (τ (M.op X0 X1)) x
       have i₂ := eq11266 X0 X1 x
       grind)
    | exact superpose eq11266 eq22494
    | exact resolve eq22494 eq11266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22680 : ∀ X0 X1 X2 : G, (k (M.op X0 X1) (τ X2)) = (τ (M.op (σ (M.op X0 X1)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 (M.op X0 X1) X2
       have i₂ := eq22494 X0 X1 X2
       grind)
    | exact superpose eq22494 eq28
    | exact resolve eq28 eq22494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22896 : ∀ X0 X1 X3 : G, (k (M.op X0 X1) X3) = (M.op (M.op X0 X1) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq22621 X0 X1 X3
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq22621
    | exact resolve eq22621 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22621
  have eq23225 : ∀ X0 X1 X2 : G, (k (σ (M.op X0 X1)) X2) = (σ (M.op (M.op X0 X1) (τ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X2 (M.op X0 X1)
       have i₂ := eq22896 X0 X1 (τ X2)
       grind)
    | exact superpose eq22896 eq18
    | exact resolve eq18 eq22896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23260 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 X1)) X2) = (σ (M.op (M.op X0 X1) (τ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23225 X0 X1 X2
       have i₂ := eq22494 X0 X1 X2
       grind)
    | exact superpose eq22494 eq23225
    | exact resolve eq23225 eq22494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22494 eq23225
  have eq24627 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq725 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24628 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq725 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq725
  have eq24629 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq24627 X0 X1
       have j1 := eq690 X0 X1 x
       grind)
    | (have r₁ := eq24627 X0 x
       have r₂ := eq690 X0 X1 x
       grind)
    | exact resolve eq24627 eq690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690 eq24627
  have eq24660 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq24629 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq24629
    | exact resolve eq24629 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24843 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq24629 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24629
  have eq24909 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq24843 X0 X1
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq24843
    | (have j0 := eq24843 X0 X1
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq24843 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq24843 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq24843 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24843
  have eq24976 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq24909 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24909
  have eq25012 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq24976 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq24976 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq24976 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24976
  have eq27640 : ∀ X0 X1 : G, (σ (M.op X0 (τ X1))) = (M.op (σ (M.op (τ X1) X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq23260 (τ X1) X0 X1
       have i₂ := eq68 (τ X1) X0
       grind)
    | exact superpose eq68 eq23260
    | exact resolve eq23260 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23260
  have eq38646 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq24660 X0 X1
       grind)
    | exact superpose eq24660 eq10
    | (have j1 := eq24660 X0 X1
       grind)
    | exact resolve eq10 eq24660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24660
  have eq38730 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq38646 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq38646
    | (have j0 := eq38646 X0 X1
       grind)
    | exact resolve eq38646 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38646
  have eq38821 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq38730 X1 X0
       have i₂ := eq25012 X0 X1
       grind)
    | exact superpose eq25012 eq38730
    | (have j0 := eq38730 X1 X0
       have j1 := eq25012 X1 X0
       grind)
    | exact resolve eq38730 eq25012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38875 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X1 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq25012 X1 X0
       have i₂ := eq38730 X0 X1
       grind)
    | exact superpose eq38730 eq25012
    | (have j0 := eq25012 X1 X0
       have j1 := eq38730 X1 X0
       grind)
    | exact resolve eq25012 eq38730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25012 eq38730
  have eq38941 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq38875 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq38875 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq38875 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38875
  have eq38949 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq38821 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq38821 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq38821 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38821
  have eq39185 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (σ (k (τ X1) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X1 X0
       have i₂ := eq38941 (τ X1) (τ X0)
       grind)
    | exact superpose eq38941 eq31
    | (have j1 := eq38941 (τ X1) (τ X0)
       grind)
    | exact resolve eq31 eq38941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39194 : ∀ X0 X1 : G, (k X0 (τ X1)) = (k X0 (M.op X0 X0)) ∨ (σ (k (τ X1) (k X0 (M.op X0 X0)))) = (M.op (σ (τ X1)) (σ (k X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9925 X0 X1
       have i₂ := eq38941 (τ X1) (k X0 (M.op X0 X0))
       grind)
    | exact superpose eq38941 eq9925
    | (have j1 := eq38941 (τ X1) (k X0 (M.op X0 X0))
       grind)
    | exact resolve eq9925 eq38941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9925 eq38941
  have eq39197 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (σ (k (τ X1) (k X0 (M.op X0 X0)))) = (M.op (σ (τ X1)) (σ (k X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq39194 X0 X1
       have i₂ := eq9937 X0
       grind)
    | exact superpose eq9937 eq39194
    | (have j0 := eq39194 X0 X1
       grind)
    | exact resolve eq39194 eq9937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39194
  have eq39206 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = (σ (k (τ X1) (τ X0))) ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq39185 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq39185
    | (have j0 := eq39185 X0 X1
       grind)
    | exact resolve eq39185 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39185
  have eq39239 : ∀ X0 X1 : G, (σ (k (τ X1) (k X0 (M.op X0 X0)))) = (M.op (σ (τ X1)) (σ X0)) ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq39197 X0 X1
       have i₂ := eq9827 X0
       grind)
    | exact superpose eq9827 eq39197
    | (have j0 := eq39197 X0 X1
       grind)
    | exact resolve eq39197 eq9827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9827 eq39197
  have eq39244 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = (k (σ (τ X1)) X0) ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq39206 X0 X1
       have i₂ := eq18 X0 (τ X1)
       grind)
    | exact superpose eq18 eq39206
    | (have j0 := eq39206 X0 X1
       grind)
    | exact resolve eq39206 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq39206
  have eq39253 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (σ (k (τ X1) (k X0 (M.op X0 X0)))) ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq39239 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq39239
    | (have j0 := eq39239 X0 X1
       grind)
    | exact resolve eq39239 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39239
  have eq39258 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq39244 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq39244
    | (have j0 := eq39244 X0 X1
       grind)
    | exact resolve eq39244 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39244
  have eq39265 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (σ (k (τ X1) X0)) ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq39253 X0 X1
       have i₂ := eq9935 X0 (τ X1)
       grind)
    | exact superpose eq9935 eq39253
    | (have j0 := eq39253 X0 X1
       grind)
    | exact resolve eq39253 eq9935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39253
  have eq39269 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq39265 X0 X1
       have i₂ := eq17 X1 X0
       grind)
    | exact superpose eq17 eq39265
    | (have j0 := eq39265 X0 X1
       grind)
    | exact resolve eq39265 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq39265
  have eq39314 : ∀ X0 X1 X2 : G, (k (τ X1) (τ X0)) = (τ (k X1 (k X0 X2))) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31 (k X0 X2) X1
       have i₂ := eq39258 X0 X2
       grind)
    | exact superpose eq39258 eq31
    | (have j1 := eq39258 X0 X2
       grind)
    | exact resolve eq31 eq39258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39258
  have eq39360 : ∀ X0 X1 X2 : G, (τ (k X1 X0)) = (τ (k X1 (k X0 X2))) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq39314 X0 X1 X2
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq39314
    | (have j0 := eq39314 X0 X1 X2
       grind)
    | exact resolve eq39314 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq39314
  have eq39651 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (M.op (σ (k X1 (M.op X1 X1))) (σ X0)) = (σ (M.op (k X1 (M.op X1 X1)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9935 X1 X0
       have i₂ := eq38949 (k X1 (M.op X1 X1)) X0
       grind)
    | exact superpose eq38949 eq9935
    | (have j1 := eq38949 (k X1 (M.op X1 X1)) X0
       grind)
    | exact resolve eq9935 eq38949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9935
  have eq39697 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (σ (M.op X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq39651 X0 X0
       have i₂ := eq9937 X0
       grind)
    | exact superpose eq9937 eq39651
    | (have j0 := eq39651 X0 X1
       grind)
    | exact resolve eq39651 eq9937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39651
  have eq40248 : ∀ X0 X1 : G, (k X0 (τ (σ X1))) = (τ (M.op (σ X0) (σ X1))) ∨ (k X1 (τ (σ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (σ X1)
       have i₂ := eq39269 X1 (σ X0)
       grind)
    | exact superpose eq39269 eq28
    | (have j1 := eq39269 X1 (σ X0)
       grind)
    | exact resolve eq28 eq39269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq39269
  have eq40283 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X1 (τ (σ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq40248 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq40248
    | (have j0 := eq40248 X0 X1
       grind)
    | exact resolve eq40248 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40248
  have eq40347 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq40283 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq40283
    | (have j0 := eq40283 X0 X1
       grind)
    | exact resolve eq40283 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40283
  have eq40595 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X2 (k X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11266 (σ X0) (σ X1) X2
       have i₂ := eq40347 X0 X1
       grind)
    | exact superpose eq40347 eq11266
    | (have j1 := eq40347 X0 X1
       grind)
    | exact resolve eq11266 eq40347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40347
  have eq108582 : ∀ X0 X1 : G, (σ (M.op X0 (τ (σ X1)))) ≠ (M.op (σ X1) (σ (M.op (τ (σ X1)) X0))) ∨ (k X1 (τ (M.op (σ X1) (σ (M.op (τ (σ X1)) X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq99 X1 (σ (M.op (τ (σ X1)) X0))
       have i₂ := eq27640 X0 (σ X1)
       grind)
    | exact superpose eq27640 eq99
    | (have j0 := eq99 X1 (σ (M.op (τ (σ X1)) X0))
       grind)
    | exact resolve eq99 eq27640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq27640
  have eq108645 : ∀ X0 X1 : G, (σ (M.op X0 (τ (σ X1)))) ≠ (σ (M.op (τ (σ X1)) X0)) ∨ (k X1 (τ (M.op (σ X1) (σ (M.op (τ (σ X1)) X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq108582 X0 X1
       have i₂ := eq10776 (τ (σ X1)) X0 (σ X1)
       grind)
    | exact superpose eq10776 eq108582
    | (have j0 := eq108582 X0 X1
       grind)
    | (have r₁ := eq108582 (τ (σ X1)) X1
       have r₂ := eq10776 (τ (σ X1)) (τ (σ X1)) (σ X1)
       grind)
    | exact resolve eq108582 eq10776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108582
  have eq108780 : ∀ X0 X1 : G, (σ (M.op X0 X1)) ≠ (σ (M.op X1 X0)) ∨ (k X1 (τ (M.op (σ X1) (σ (M.op (τ (σ X1)) X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq108645 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq108645
    | (have j0 := eq108645 X0 X1
       grind)
    | exact resolve eq108645 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108645
  have eq108896 : ∀ X0 X1 : G, (k X1 (τ (σ (M.op (τ (σ X1)) X0)))) = X1 ∨ (σ (M.op X0 X1)) ≠ (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq108780 X0 X1
       have i₂ := eq10776 (τ (σ X1)) X0 (σ X1)
       grind)
    | exact superpose eq10776 eq108780
    | (have j0 := eq108780 X0 X1
       grind)
    | exact resolve eq108780 eq10776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108780
  have eq108976 : ∀ X0 X1 : G, (k X1 (M.op (τ (σ X1)) X0)) = X1 ∨ (σ (M.op X0 X1)) ≠ (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq108896 X0 X1
       have i₂ := eq10 (M.op (τ (σ X1)) X0)
       grind)
    | exact superpose eq10 eq108896
    | (have j0 := eq108896 X0 X1
       grind)
    | exact resolve eq108896 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108896
  have eq109008 : ∀ X0 X1 : G, (σ (M.op X0 X1)) ≠ (σ (M.op X1 X0)) ∨ (k X1 (M.op X1 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq108976 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq108976
    | (have j0 := eq108976 X0 X1
       grind)
    | exact resolve eq108976 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108976
  have eq162024 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (k X0 (k X1 X2)) ∨ (M.op X2 X1) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 (k X0 (k X1 X2))
       have i₂ := eq39360 X1 X0 X2
       grind)
    | exact superpose eq39360 eq11
    | (have j1 := eq39360 X1 X1 X2
       grind)
    | exact resolve eq11 eq39360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39360
  have eq162132 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (k X2 X1) ∨ (k X0 X1) = (k X0 (k X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq162024 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq162024
    | (have j0 := eq162024 X0 X1 X2
       grind)
    | exact resolve eq162024 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162024
  have eq196993 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq818 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq818
  have eq196994 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq196993 X0 X1
       have i₂ := eq22896 X0 X1 X0
       grind)
    | exact superpose eq22896 eq196993
    | (have j0 := eq196993 X0 X1
       grind)
    | exact resolve eq196993 eq22896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196993
  have eq196995 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq196994 X0 X1
       have i₂ := eq68 X0 X1
       grind)
    | exact superpose eq68 eq196994
    | (have j0 := eq196994 X0 X1
       grind)
    | exact resolve eq196994 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196994
  have eq515365 : ∀ X0 X1 X2 : G, (M.op X2 X0) = X0 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 X1 X0 x
       have i₂ := eq196995 X0 X1
       grind)
    | exact superpose eq196995 eq64
    | (have j1 := eq196995 X0 X1
       grind)
    | exact resolve eq64 eq196995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq522129 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq515365 X0 X1 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515365
  have eq522142 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq522129 X0 X1
       have j1 := eq196995 X0 X1
       grind)
    | (have r₁ := eq522129 X0 X1
       have r₂ := eq196995 X0 X1
       grind)
    | exact resolve eq522129 eq196995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196995 eq522129
  have eq522953 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op (k X0 (M.op X0 X0)) X1)) ∨ (M.op X1 (k X0 (M.op X0 X0))) = (M.op (k X0 (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9936 X0 X1
       have i₂ := eq522142 X1 (k X0 (M.op X0 X0))
       grind)
    | exact superpose eq522142 eq9936
    | (have j1 := eq522142 X1 (k X0 (M.op X0 X0))
       grind)
    | exact resolve eq9936 eq522142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9936
  have eq522997 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 (k X0 (M.op X0 X0))) = (M.op (k X0 (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq522953 X0 X1
       have i₂ := eq9937 X0
       grind)
    | exact superpose eq9937 eq522953
    | (have j0 := eq522953 X0 X1
       grind)
    | exact resolve eq522953 eq9937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522953
  have eq523244 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq522997 X0 X1
       have i₂ := eq9937 X0
       grind)
    | exact superpose eq9937 eq522997
    | (have j0 := eq522997 X0 X1
       grind)
    | exact resolve eq522997 eq9937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9937 eq522997
  have eq523924 : ∀ X0 X1 : G, (τ (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1)))) = (k (τ (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1)))) (k X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq478 (k X0 X1)
       have i₂ := eq523244 X0 X1
       grind)
    | exact superpose eq523244 eq478
    | (have j1 := eq523244 X0 X1
       grind)
    | exact resolve eq478 eq523244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478 eq523244
  have eq524186 : ∀ X0 X1 : G, (τ (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1)))) = (M.op (τ (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1)))) (k X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq523924 X0 X1
       have i₂ := eq22479 (σ (M.op X0 X1)) (σ (M.op X0 X1)) (k X0 X1)
       grind)
    | exact superpose eq22479 eq523924
    | (have j0 := eq523924 X0 X1
       grind)
    | exact resolve eq523924 eq22479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22479 eq523924
  have eq524404 : ∀ X0 X1 : G, (k (M.op X0 X1) (τ (σ (M.op X0 X1)))) = (M.op (k (M.op X0 X1) (τ (σ (M.op X0 X1)))) (k X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq524186 X0 X1
       have i₂ := eq22680 X0 X1 (σ (M.op X0 X1))
       grind)
    | exact superpose eq22680 eq524186
    | (have j0 := eq524186 X0 X1
       grind)
    | exact resolve eq524186 eq22680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22680 eq524186
  have eq524531 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (τ (σ (M.op X0 X1)))) = (M.op (M.op (M.op X0 X1) (τ (σ (M.op X0 X1)))) (k X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq524404 X0 X1
       have i₂ := eq22896 X0 X1 (τ (σ (M.op X0 X1)))
       grind)
    | exact superpose eq22896 eq524404
    | (have j0 := eq524404 X0 X1
       grind)
    | exact resolve eq524404 eq22896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524404
  have eq524590 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (k X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq524531 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq524531
    | (have j0 := eq524531 X0 X1
       grind)
    | exact resolve eq524531 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524531
  have eq524630 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (k X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq524590 X0 X1
       have i₂ := eq64 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq64 eq524590
    | (have j0 := eq524590 X0 X1
       grind)
    | exact resolve eq524590 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524590
  have eq524822 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (σ (M.op X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq524630 X0 X1
       have i₂ := eq38949 X1 X0
       grind)
    | exact superpose eq38949 eq524630
    | (have j0 := eq524630 X0 X1
       have j1 := eq38949 X1 X0
       grind)
    | exact resolve eq524630 eq38949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524630
  have eq525618 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (σ (M.op X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq524822 X0 X1
       have i₂ := eq68 X0 X1
       grind)
    | exact superpose eq68 eq524822
    | (have j0 := eq524822 X0 X1
       grind)
    | exact resolve eq524822 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524822
  have eq525619 : ∀ X0 X1 : G, (σ (M.op X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq525618 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525618
  have eq526427 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq525619 y x
       grind)
    | exact superpose eq525619 eq16
    | (have j1 := eq525619 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq525619 y x
       grind)
    | exact resolve eq16 eq525619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525619
  have eq526719 : (M.op x y) = (M.op y x) := by grind
  clear eq526427
  have eq527653 : (M.op x y) ≠ (M.op x y) ∨ y = (k y x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq24628 y x
       have i₂ := eq526719
       grind)
    | exact superpose eq526719 eq24628
    | (have j0 := eq24628 y x
       grind)
    | (have r₁ := eq24628 x y
       have r₂ := eq526719
       grind)
    | (have r₁ := eq24628 y x
       have r₂ := eq526719
       grind)
    | exact resolve eq24628 eq526719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24628
  have eq527763 : y = (k y x) ∨ (M.op x y) = (k y x) := by grind
  clear eq527653
  have eq529229 : ∀ X0 : G, y = (M.op y x) ∨ (k X0 x) = (k X0 (k x y)) ∨ (M.op x y) = (k y x) := by
    intro X0
    first
    | (have i₁ := eq162132 X0 x y
       have i₂ := eq527763
       grind)
    | exact superpose eq527763 eq162132
    | (have j0 := eq162132 X0 x y
       grind)
    | exact resolve eq162132 eq527763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162132
  have eq529265 : y ≠ (M.op x y) ∨ (M.op x y) = (k y x) := by grind
  clear eq527763
  have eq529285 : ∀ X0 : G, y = (M.op x y) ∨ (k X0 x) = (k X0 (k x y)) ∨ (M.op x y) = (k y x) := by
    intro X0
    first
    | (have i₁ := eq529229 X0
       have i₂ := eq526719
       grind)
    | exact superpose eq526719 eq529229
    | (have j0 := eq529229 X0
       grind)
    | exact resolve eq529229 eq526719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529229
  have eq529332 : ∀ X0 : G, (M.op x y) = (k y x) ∨ (k X0 x) = (k X0 (k x y)) := by
    intro X0
    first
    | (have j0 := eq529285 X0
       grind)
    | (have r₁ := eq529285 X0
       have r₂ := eq529265
       grind)
    | exact resolve eq529285 eq529265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529265 eq529285
  have eq538242 : ∀ X0 : G, y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (k X0 x) = (k X0 (k x y)) := by
    intro X0
    first
    | (have i₁ := eq38949 x y
       have i₂ := eq529332 X0
       grind)
    | exact superpose eq529332 eq38949
    | (have j0 := eq38949 x y
       have j1 := eq529332 X0
       grind)
    | exact resolve eq38949 eq529332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38949
  have eq538255 : ∀ X0 : G, (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (k X0 x) = (k X0 (k x y)) := by
    intro X0
    first
    | (have i₁ := eq39697 y x
       have i₂ := eq529332 X0
       grind)
    | exact superpose eq529332 eq39697
    | (have j0 := eq39697 y x
       have j1 := eq529332 X0
       grind)
    | exact resolve eq39697 eq529332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39697 eq529332
  have eq538675 : ∀ X0 : G, (σ (M.op x y)) = (σ y) ∨ (k X0 x) = (k X0 (k x y)) := by
    intro X0
    first
    | (have j0 := eq538255 X0
       grind)
    | (have r₁ := eq538255 X0
       have r₂ := eq16
       grind)
    | exact resolve eq538255 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538255
  have eq538678 : ∀ X0 : G, y = (M.op x y) ∨ (k X0 x) = (k X0 (k x y)) := by
    intro X0
    first
    | (have j0 := eq538242 X0
       grind)
    | (have r₁ := eq538242 X0
       have r₂ := eq16
       grind)
    | exact resolve eq538242 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538242
  have eq538804 : ∀ X0 X1 : G, (σ y) = (M.op X0 (σ y)) ∨ (k X1 (k x y)) = (k X1 x) := by
    intro X0 X1
    first
    | (have i₁ := eq10776 x y x
       have i₂ := eq538678 X0
       grind)
    | exact superpose eq538678 eq10776
    | (have j1 := eq538678 X1
       grind)
    | exact resolve eq10776 eq538678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538678
  have eq551201 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ y) ∨ (k X0 x) = (k X0 (k x y)) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq538804 (σ x) X0
       grind)
    | exact superpose eq538804 eq16
    | (have j1 := eq538804 X0 X0
       grind)
    | exact resolve eq16 eq538804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538804
  have eq551295 : ∀ X0 : G, (k X0 x) = (k X0 (k x y)) := by
    intro X0
    first
    | (have j0 := eq551201 X0
       have j1 := eq538675 X0
       grind)
    | (have r₁ := eq551201 X0
       have r₂ := eq538675 X0
       grind)
    | exact resolve eq551201 eq538675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538675 eq551201
  have eq551807 : (k (k x y) x) = (k (k (k x y) x) (k x y)) := by
    first
    | (have i₁ := eq9593 (k x y)
       have i₂ := eq551295 (k x y)
       grind)
    | exact superpose eq551295 eq9593
    | exact resolve eq9593 eq551295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9593
  have eq552190 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (k x y)) = (k (M.op X0 X1) x) := by
    intro X0 X1
    first
    | (have i₁ := eq22896 X0 X1 (k x y)
       have i₂ := eq551295 (M.op X0 X1)
       grind)
    | exact superpose eq551295 eq22896
    | exact resolve eq22896 eq551295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq552308 : ∀ X0 X1 : G, (M.op (M.op X0 X1) x) = (M.op (M.op X0 X1) (k x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq552190 X0 X1
       have i₂ := eq22896 X0 X1 x
       grind)
    | exact superpose eq22896 eq552190
    | exact resolve eq552190 eq22896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552190
  have eq552318 : (k (k x y) x) = (k (k (k x y) x) x) := by
    first
    | (have i₁ := eq551807
       have i₂ := eq551295 (k (k x y) x)
       grind)
    | exact superpose eq551295 eq551807
    | exact resolve eq551807 eq551295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551807
  have eq557360 : ∀ X0 : G, (M.op X0 (k x y)) = (M.op (M.op (k x y) X0) x) := by
    intro X0
    first
    | (have i₁ := eq68 (k x y) X0
       have i₂ := eq552308 (k x y) X0
       grind)
    | exact superpose eq552308 eq68
    | exact resolve eq68 eq552308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq552308
  have eq558046 : (M.op (k x y) x) = (k (M.op (k x y) x) x) ∨ (M.op (k x y) x) = (M.op x (k x y)) := by
    first
    | (have i₁ := eq552318
       have i₂ := eq522142 x (k x y)
       grind)
    | exact superpose eq522142 eq552318
    | (have j1 := eq522142 (k x y) x
       grind)
    | exact resolve eq552318 eq522142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522142 eq552318
  have eq558228 : (M.op (k x y) x) = (M.op (M.op (k x y) x) x) ∨ (M.op (k x y) x) = (M.op x (k x y)) := by
    first
    | (have i₁ := eq558046
       have i₂ := eq22896 (k x y) x x
       grind)
    | exact superpose eq22896 eq558046
    | exact resolve eq558046 eq22896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22896 eq558046
  have eq558287 : (M.op (k x y) x) = (M.op x (k x y)) ∨ (M.op (k x y) x) = (M.op x (k x y)) := by
    first
    | (have i₁ := eq558228
       have i₂ := eq557360 x
       grind)
    | exact superpose eq557360 eq558228
    | exact resolve eq558228 eq557360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557360 eq558228
  have eq558288 : (M.op (k x y) x) = (M.op x (k x y)) := by grind
  clear eq558287
  have eq558934 : (k x y) ≠ (M.op x (k x y)) ∨ x = (k x (k x y)) := by
    first
    | (have i₁ := eq12 x (k x y)
       have i₂ := eq558288
       grind)
    | exact superpose eq558288 eq12
    | (have j0 := eq12 x (k x y)
       grind)
    | exact resolve eq12 eq558288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq559092 : (σ (M.op x (k x y))) ≠ (σ (M.op x (k x y))) ∨ x = (k x (M.op x (k x y))) := by
    first
    | (have i₁ := eq109008 (k x y) x
       have i₂ := eq558288
       grind)
    | exact superpose eq558288 eq109008
    | (have j0 := eq109008 (k x y) x
       grind)
    | exact resolve eq109008 eq558288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109008 eq558288
  have eq559134 : x = (k x (M.op x (k x y))) := by grind
  clear eq559092
  have eq559184 : x = (k x x) ∨ (k x y) ≠ (M.op x (k x y)) := by
    first
    | (have i₁ := eq558934
       have i₂ := eq551295 x
       grind)
    | exact superpose eq551295 eq558934
    | exact resolve eq558934 eq551295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558934
  have eq559239 : (k x y) ≠ (M.op x (k x y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq559184
       have i₂ := eq9646 x
       grind)
    | exact superpose eq9646 eq559184
    | exact resolve eq559184 eq9646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559184
  have eq559360 : x = (k x (k x y)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq559134
       have i₂ := eq40595 x y x
       grind)
    | exact superpose eq40595 eq559134
    | (have j1 := eq40595 (k x y) x x
       grind)
    | exact resolve eq559134 eq40595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40595 eq559134
  have eq559656 : x = (k x x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq559360
       have i₂ := eq551295 x
       grind)
    | exact superpose eq551295 eq559360
    | exact resolve eq559360 eq551295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551295 eq559360
  have eq559792 : x = (M.op x x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq559656
       have i₂ := eq9646 x
       grind)
    | exact superpose eq9646 eq559656
    | exact resolve eq559656 eq9646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9646 eq559656
  have eq559976 : ∀ X0 : G, x = (M.op X0 x) ∨ y = (k y x) := by
    intro X0
    first
    | (have i₁ := eq64 x x x
       have i₂ := eq559792
       grind)
    | exact superpose eq559792 eq64
    | exact resolve eq64 eq559792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559792
  have eq560873 : x = (M.op x y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq526719
       have i₂ := eq559976 y
       grind)
    | exact superpose eq559976 eq526719
    | exact resolve eq526719 eq559976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559976
  have eq560883 : y = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq560873
       have r₂ := eq12 y x
       grind)
    | exact resolve eq560873 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560873
  have eq588926 : ∀ X0 : G, (M.op y x) ≠ (M.op x (M.op y x)) ∨ x = (M.op x x) ∨ y = (M.op X0 y) ∨ (k y x) = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq559239
       have i₂ := eq2591 y x x
       grind)
    | exact superpose eq2591 eq559239
    | (have j1 := eq2591 y x X0
       grind)
    | (have r₁ := eq559239
       have r₂ := eq2591 (k x y) x x
       grind)
    | exact resolve eq559239 eq2591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2591 eq559239
  have eq589094 : ∀ X0 : G, x = (M.op x x) ∨ y = (M.op X0 y) ∨ (k y x) = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq588926 X0
       grind)
    | (have r₁ := eq588926 X0
       have r₂ := eq64 y x x
       grind)
    | exact resolve eq588926 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588926
  have eq589099 : ∀ X0 : G, (M.op x y) = (k y x) ∨ x = (M.op x x) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq589094 X0
       have i₂ := eq526719
       grind)
    | exact superpose eq526719 eq589094
    | (have j0 := eq589094 X0
       grind)
    | exact resolve eq589094 eq526719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589094
  have eq589102 : ∀ X0 : G, y = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq589099 X0
       have i₂ := eq560883
       grind)
    | exact superpose eq560883 eq589099
    | (have j0 := eq589099 x
       grind)
    | exact resolve eq589099 eq560883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589099
  have eq615021 : y ≠ y ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have j0 := eq589102 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589102
  have eq615022 : y = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq615021
  have eq615092 : ∀ X0 : G, x = (M.op x x) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq64 x y x
       have i₂ := eq615022
       grind)
    | exact superpose eq615022 eq64
    | exact resolve eq64 eq615022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq615022
  have eq615353 : ∀ X0 X1 : G, x = (M.op X0 x) ∨ y = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq64 x x x
       have i₂ := eq615092 X0
       grind)
    | exact superpose eq615092 eq64
    | (have j1 := eq615092 X1
       grind)
    | exact resolve eq64 eq615092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq615092
  have eq615968 : ∀ X0 : G, x = (M.op x y) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq526719
       have i₂ := eq615353 y X0
       grind)
    | exact superpose eq615353 eq526719
    | (have j1 := eq615353 X0 X0
       grind)
    | exact resolve eq526719 eq615353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526719 eq615353
  have eq616057 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq606
       have i₂ := eq615968 X0
       grind)
    | exact superpose eq615968 eq606
    | (have j1 := eq615968 X0
       grind)
    | exact resolve eq606 eq615968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606 eq615968
  have eq616274 : ∀ X0 : G, (M.op (σ y) (σ x)) = (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq616057 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616057
  have eq616290 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq616274 X0
       have i₂ := eq560883
       grind)
    | exact superpose eq560883 eq616274
    | (have j0 := eq616274 X0
       grind)
    | exact resolve eq616274 eq560883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560883 eq616274
  have eq616291 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq616290 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616290
  have eq627896 : ∀ X0 X1 : G, (τ (σ y)) = (M.op X0 (τ (σ y))) ∨ y = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq11266 (σ y) (σ x) x
       have i₂ := eq616291 X0
       grind)
    | exact superpose eq616291 eq11266
    | (have j1 := eq616291 X1
       grind)
    | exact resolve eq11266 eq616291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11266 eq616291
  have eq628135 : ∀ X0 X1 : G, y = (M.op X0 y) ∨ y = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq627896 X0 X1
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq627896
    | (have j0 := eq627896 X0 X0
       grind)
    | exact resolve eq627896 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq627896
  have eq628784 : ∀ X0 : G, y ≠ y ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq628135 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628135
  have eq628785 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq628784 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628784
  have eq628936 : ∀ X1 : G, (σ y) = (M.op X1 (σ y)) := by
    intro X1
    first
    | (have i₁ := eq10776 x y x
       have i₂ := eq628785 x
       grind)
    | exact superpose eq628785 eq10776
    | exact resolve eq10776 eq628785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10776
  have eq629653 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq628936 (σ x)
       grind)
    | exact superpose eq628936 eq16
    | exact resolve eq16 eq628936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628936
  have eq629757 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq629653
       have i₂ := eq628785 x
       grind)
    | exact superpose eq628785 eq629653
    | exact resolve eq629653 eq628785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628785 eq629653
  have eq629758 : False := by grind
  exact eq629758
