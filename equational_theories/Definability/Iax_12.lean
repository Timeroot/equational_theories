import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1171`: `x = y ◇ ((z ◇ (y ◇ z)) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation1171 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1171 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law1171.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 (M.op X1 X2)) X0)) = X0 := by
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
  have eq22 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X1)) (M.op X0 X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 (M.op X1 (M.op X0 X1)) X0
       have i₂ := eq8 X0 X0 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq33 (σ X0)
       grind)
    | exact superpose eq33 eq13
    | exact resolve eq13 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq35
    | exact resolve eq35 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq35
  have eq50 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq53 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq56 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq58 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq53
    | (have j0 := eq53 X0 X1
       grind)
    | exact resolve eq53 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq139 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq56 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq143 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq139 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq139 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq139 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq139 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq162 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq143 (σ X0) (σ X1)
       grind)
    | exact superpose eq143 eq13
    | exact resolve eq13 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq171 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq162 X0 X1
       have i₂ := eq143 X0 X1
       grind)
    | exact superpose eq143 eq162
    | exact resolve eq162 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162
  have eq561 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq58 x y
       grind)
    | exact superpose eq58 eq14
    | (have j1 := eq58 x y
       grind)
    | exact resolve eq14 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq586 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq561
       have i₂ := eq143 x y
       grind)
    | exact superpose eq143 eq561
    | exact resolve eq561 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143 eq561
  have eq587 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq586
  have eq641 : (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq587
       have i₂ := eq171 x y
       grind)
    | exact superpose eq171 eq587
    | exact resolve eq587 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171 eq587
  have eq764 : (M.op x y) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq9 (M.op x y)
       have i₂ := eq641
       grind)
    | exact superpose eq641 eq9
    | exact resolve eq9 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641
  have eq783 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq764
       have i₂ := eq9 (M.op x x)
       grind)
    | exact superpose eq9 eq764
    | exact resolve eq764 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764
  have eq930 : ∀ X0 : G, y = (M.op (M.op X0 (M.op x X0)) (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq22 x X0 y
       have i₂ := eq783
       grind)
    | exact superpose eq783 eq22
    | exact resolve eq22 eq783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq783
  have eq934 : x = y := by
    first
    | (have i₁ := eq930 x
       have i₂ := eq22 x x x
       grind)
    | exact superpose eq22 eq930
    | exact resolve eq930 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq930
  have eq977 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq934
       grind)
    | exact superpose eq934 eq14
    | exact resolve eq14 eq934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq934
  have eq978 : False := by grind
  exact eq978

/-- `Equation1184`: `x = y ◇ ((z ◇ (z ◇ y)) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation1184 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1184 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law1184.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 (M.op X2 X1)) X0)) = X0 := by
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
  have eq22 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X3 (M.op X3 (M.op X2 (M.op X2 X1)))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op (M.op X3 (M.op X3 (M.op X2 (M.op X2 X1)))) X0) X1 X2
       have i₂ := eq8 X0 (M.op X2 (M.op X2 X1)) X3
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq32 (σ X0)
       grind)
    | exact superpose eq32 eq13
    | exact resolve eq13 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq34 X0
       have i₂ := eq32 X0
       grind)
    | exact superpose eq32 eq34
    | exact resolve eq34 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq34
  have eq49 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq52 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq55 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq57 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X1
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq52
    | (have j0 := eq52 X0 X1
       grind)
    | exact resolve eq52 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq93 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq97 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq93 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq93 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq93 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq93 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq113 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq97 (σ X0) (σ X1)
       grind)
    | exact superpose eq97 eq13
    | exact resolve eq13 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq113 X0 X1
       have i₂ := eq97 X0 X1
       grind)
    | exact superpose eq97 eq113
    | exact resolve eq113 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq215 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X2 X0)) (M.op X0 X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 (M.op X2 (M.op X2 X0)) x
       have i₂ := eq22 X1 X0 X2 x
       grind)
    | exact superpose eq22 eq8
    | exact resolve eq8 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq518 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq57 x y
       grind)
    | exact superpose eq57 eq14
    | (have j1 := eq57 x y
       grind)
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq541 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq518
       have i₂ := eq97 x y
       grind)
    | exact superpose eq97 eq518
    | exact resolve eq518 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq518
  have eq542 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq541
  have eq594 : (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq542
       have i₂ := eq120 x y
       grind)
    | exact superpose eq120 eq542
    | exact resolve eq542 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq542
  have eq714 : (M.op x y) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq9 (M.op x y)
       have i₂ := eq594
       grind)
    | exact superpose eq594 eq9
    | exact resolve eq9 eq594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594
  have eq733 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq714
       have i₂ := eq9 (M.op x x)
       grind)
    | exact superpose eq9 eq714
    | exact resolve eq714 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714
  have eq1133 : ∀ X0 : G, y = (M.op (M.op X0 (M.op X0 x)) (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq215 x y X0
       have i₂ := eq733
       grind)
    | exact superpose eq733 eq215
    | exact resolve eq215 eq733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq733
  have eq1173 : x = y := by
    first
    | (have i₁ := eq1133 x
       have i₂ := eq215 x x x
       grind)
    | exact superpose eq215 eq1133
    | exact resolve eq1133 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215 eq1133
  have eq1194 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1173
       grind)
    | exact superpose eq1173 eq14
    | exact resolve eq14 eq1173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1173
  have eq1195 : False := by grind
  exact eq1195

/-- `Equation1226`: `x = x ◇ (((x ◇ x) ◇ y) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pxx_pxy_Equation1226 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1226 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law1226.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (M.op X0 X0) X1) X1)) = X0 := by
    intro X0 X1
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
  have eq18 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X0) (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) X1)
       have i₂ := eq8 (M.op X0 X0) X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq18 X0 x
       have i₂ := eq8 (M.op X0 X0) x
       grind)
    | exact superpose eq8 eq18
    | exact resolve eq18 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq24 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq19 X0
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq19
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq19 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq28 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq53 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq26 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq26
    | exact resolve eq26 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X0
       have i₂ := eq12 (σ X0) X1
       grind)
    | (have i₁ := eq28 X0 X1
       have i₂ := eq12 X0 (M.op (σ X0) (σ X1))
       grind)
    | exact superpose eq12 eq28
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq28 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq152 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq28 x y
       grind)
    | exact superpose eq28 eq14
    | (have j1 := eq28 x y
       grind)
    | exact resolve eq14 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq159 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq9
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq9 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq168 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (σ X1)
       have i₂ := eq28 X1 X0
       grind)
    | exact superpose eq28 eq19
    | (have j1 := eq28 X1 X0
       grind)
    | exact resolve eq19 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq439 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
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
  have eq495 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq439 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq439
    | (have j0 := eq439 X0 X1
       grind)
    | exact resolve eq439 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439
  have eq545 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq546 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1
       have i₂ := eq495 X0 X1
       grind)
    | (have i₁ := eq19 X0
       have i₂ := eq495 (M.op X0 X0) X1
       grind)
    | exact superpose eq495 eq19
    | (have j1 := eq495 X0 X1
       grind)
    | exact resolve eq19 eq495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq905 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq19 (σ X0)
       have i₂ := eq53 X0 X0
       grind)
    | exact superpose eq53 eq19
    | (have j1 := eq53 X0 X0
       grind)
    | exact resolve eq19 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1124 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq152
       have i₂ := eq546 y x
       grind)
    | exact superpose eq546 eq152
    | (have j1 := eq546 y x
       grind)
    | (have r₁ := eq152
       have r₂ := eq546 y x
       grind)
    | exact resolve eq152 eq546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546
  have eq1125 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq152
       have i₂ := eq545 y x
       grind)
    | exact superpose eq545 eq152
    | (have j1 := eq545 y x
       grind)
    | (have r₁ := eq152
       have r₂ := eq545 y x
       grind)
    | exact resolve eq152 eq545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545
  have eq1126 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq152
       have i₂ := eq495 y x
       grind)
    | exact superpose eq495 eq152
    | (have j1 := eq495 (σ y) (σ x)
       grind)
    | (have r₁ := eq152
       have r₂ := eq495 y x
       grind)
    | exact resolve eq152 eq495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq495
  have eq1127 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq1126
  have eq1128 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k x y) := by grind
  clear eq1125
  have eq1129 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq1124
  have eq1144 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  have eq1145 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq19 (σ x)
       have i₂ := eq1127
       grind)
    | exact superpose eq1127 eq19
    | exact resolve eq19 eq1127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1127
  have eq1152 : (σ y) = (σ (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1144
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq1144
    | exact resolve eq1144 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1144
  have eq1297 : (k x y) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (k x y)
       have i₂ := eq1152
       grind)
    | exact superpose eq1152 eq9
    | exact resolve eq9 eq1152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1152
  have eq1340 : y = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1297
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1297
    | exact resolve eq1297 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1297
  have eq1385 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq168 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq1399 : y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq1340
       grind)
    | exact superpose eq1340 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq1340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1340
  have eq1406 : y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq1399
  have eq1413 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ (k (τ X0) (τ X0))) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq140 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq140
    | (have j0 := eq140 X1 (τ X0)
       grind)
    | exact resolve eq140 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq1509 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1413 X0 X1
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq1413
    | (have j0 := eq1413 X0 X1
       grind)
    | exact resolve eq1413 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1413
  have eq1517 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1509 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1509
    | (have j0 := eq1509 X0 X1
       grind)
    | exact resolve eq1509 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1509
  have eq1715 : (σ y) = (k (σ x) (σ y)) ∨ y = (k x y) := by grind
  clear eq1128
  have eq1725 : (σ y) = (σ (k x y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq1715
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq1715
    | exact resolve eq1715 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1715
  have eq1888 : (k x y) = (τ (σ y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq9 (k x y)
       have i₂ := eq1725
       grind)
    | exact superpose eq1725 eq9
    | exact resolve eq9 eq1725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1725
  have eq1933 : y = (k x y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq1888
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1888
    | exact resolve eq1888 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1888
  have eq1934 : y = (k x y) := by grind
  clear eq1933
  have eq2075 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24 y x
       have i₂ := eq1934
       grind)
    | exact superpose eq1934 eq24
    | (have j0 := eq24 y x
       grind)
    | exact resolve eq24 eq1934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq2329 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq2075
  have eq3034 : (σ y) = (σ (k x x)) ∨ x = (τ (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq159 x x
       have i₂ := eq1129
       grind)
    | exact superpose eq1129 eq159
    | exact resolve eq159 eq1129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159 eq1129
  have eq3055 : x = y ∨ (σ y) = (σ (k x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3034
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq3034
    | exact resolve eq3034 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3034
  have eq3056 : (σ y) = (σ (k x x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq3055
       have r₂ := eq2329
       grind)
    | exact resolve eq3055 eq2329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3055
  have eq3343 : (k x x) = (τ (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq3056
       grind)
    | exact superpose eq3056 eq9
    | exact resolve eq9 eq3056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3056
  have eq3400 : y = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3343
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq3343
    | exact resolve eq3343 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3343
  have eq3703 : y = (M.op x x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq26 x x
       have i₂ := eq3400
       grind)
    | exact superpose eq3400 eq26
    | exact resolve eq26 eq3400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq3400
  have eq3709 : x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq3703
       have r₂ := eq2329
       grind)
    | exact resolve eq3703 eq2329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3703
  have eq3865 : x = y ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1406
       have i₂ := eq3709
       grind)
    | exact superpose eq3709 eq1406
    | exact resolve eq1406 eq3709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1406 eq3709
  have eq3872 : y = (M.op x x) ∨ x = y := by grind
  clear eq3865
  have eq4229 : x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq19 x
       have i₂ := eq3872
       grind)
    | exact superpose eq3872 eq19
    | exact resolve eq19 eq3872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq3872
  have eq4239 : x = (M.op x y) := by
    first
    | (have r₁ := eq4229
       have r₂ := eq2329
       grind)
    | exact resolve eq4229 eq2329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2329 eq4229
  have eq6711 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1145
       grind)
    | exact superpose eq1145 eq14
    | exact resolve eq14 eq1145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1145
  have eq6727 : (σ x) ≠ (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq6711
       have i₂ := eq4239
       grind)
    | exact superpose eq4239 eq6711
    | exact resolve eq6711 eq4239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6711
  have eq6728 : y = (M.op x x) := by grind
  clear eq6727
  have eq11658 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1385 x y
       have i₂ := eq1934
       grind)
    | exact superpose eq1934 eq1385
    | (have j0 := eq1385 x y
       grind)
    | exact resolve eq1385 eq1934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1385
  have eq11838 : y = (M.op x y) ∨ y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq1934
       have i₂ := eq1517 x y
       grind)
    | exact superpose eq1517 eq1934
    | (have j1 := eq1517 x y
       grind)
    | exact resolve eq1934 eq1517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1517 eq1934
  have eq11946 : x = y ∨ y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq11838
       have i₂ := eq4239
       grind)
    | exact superpose eq4239 eq11838
    | exact resolve eq11838 eq4239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11838
  have eq11947 : y = (k x x) ∨ x = y := by grind
  clear eq11946
  have eq16629 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq905 x
       have i₂ := eq11947
       grind)
    | exact superpose eq11947 eq905
    | exact resolve eq905 eq11947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905 eq11947
  have eq16717 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq16629
       have r₂ := eq11658
       grind)
    | exact resolve eq16629 eq11658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16629
  have eq16765 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq16717
       grind)
    | exact superpose eq16717 eq14
    | exact resolve eq14 eq16717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16717
  have eq16809 : (σ x) ≠ (σ x) ∨ x = y := by
    first
    | (have i₁ := eq16765
       have i₂ := eq4239
       grind)
    | exact superpose eq4239 eq16765
    | exact resolve eq16765 eq4239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4239 eq16765
  have eq16810 : x = y := by grind
  clear eq16809
  have eq16864 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq16810
       grind)
    | exact superpose eq16810 eq14
    | exact resolve eq14 eq16810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16889 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq11658
       have i₂ := eq16810
       grind)
    | exact superpose eq16810 eq11658
    | exact resolve eq11658 eq16810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11658
  have eq16894 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq16889
  have eq16903 : (σ y) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16864
       have i₂ := eq6728
       grind)
    | exact superpose eq6728 eq16864
    | exact resolve eq16864 eq6728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6728 eq16864
  have eq16905 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq16903
       have i₂ := eq16894
       grind)
    | exact superpose eq16894 eq16903
    | exact resolve eq16903 eq16894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16894 eq16903
  have eq16906 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq16905
       have i₂ := eq16810
       grind)
    | exact superpose eq16810 eq16905
    | exact resolve eq16905 eq16810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16810 eq16905
  have eq16907 : False := by grind
  exact eq16907

/-- `Equation1234`: `x = x ◇ (((x ◇ y) ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pxx_pxy_Equation1234 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1234 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law1234.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X0 X1) X2) X0)) = X0 := by
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq19 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X1) X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 (M.op (M.op (M.op (M.op X0 X1) x) x) (M.op X0 X1))
       have i₂ := eq8 (M.op X0 X1) x x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq19 X0 (M.op (M.op X0 x) X0)
       have i₂ := eq19 X0 x
       grind)
    | exact superpose eq19 eq19
    | exact resolve eq19 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq26 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    grind
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
  have eq31 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq21 X1
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq21 X0
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq21
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq21 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq42 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
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
  clear eq17
  have eq50 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq26 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq26
    | exact resolve eq26 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq40 X0 X1
       have i₂ := eq12 X0 (σ X1)
       grind)
    | exact superpose eq12 eq40
    | (have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq40 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq180 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
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
  have eq190 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq30 X0 X1
       grind)
    | exact superpose eq30 eq9
    | (have j1 := eq30 X0 X1
       grind)
    | exact resolve eq9 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq198 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq21 (σ X1)
       have i₂ := eq30 X1 X0
       grind)
    | exact superpose eq30 eq21
    | (have j1 := eq30 X1 X0
       grind)
    | exact resolve eq21 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq486 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq42 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq42
    | exact resolve eq42 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq544 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq486 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq486
    | (have j0 := eq486 X0 X1
       grind)
    | exact resolve eq486 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486
  have eq592 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq21 X1
       have i₂ := eq544 X0 X1
       grind)
    | (have i₁ := eq21 X0
       have i₂ := eq544 (M.op X0 X0) X1
       grind)
    | exact superpose eq544 eq21
    | (have j1 := eq544 X0 X1
       grind)
    | exact resolve eq21 eq544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq594 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq894 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq21 (σ X0)
       have i₂ := eq50 X0 X0
       grind)
    | exact superpose eq50 eq21
    | (have j1 := eq50 X0 X0
       grind)
    | exact resolve eq21 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq1102 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq180
       have i₂ := eq594 y x
       grind)
    | exact superpose eq594 eq180
    | (have j1 := eq594 y x
       grind)
    | (have r₁ := eq180
       have r₂ := eq594 y x
       grind)
    | exact resolve eq180 eq594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594
  have eq1103 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq180
       have i₂ := eq592 y x
       grind)
    | exact superpose eq592 eq180
    | (have j1 := eq592 y x
       grind)
    | (have r₁ := eq180
       have r₂ := eq592 y x
       grind)
    | exact resolve eq180 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592
  have eq1104 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq180
       have i₂ := eq544 y x
       grind)
    | exact superpose eq544 eq180
    | (have j1 := eq544 (σ y) (σ x)
       grind)
    | (have r₁ := eq180
       have r₂ := eq544 y x
       grind)
    | exact resolve eq180 eq544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq1105 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq1104
  have eq1106 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq1103
  have eq1107 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k x y) := by grind
  clear eq1102
  have eq1120 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq21 (σ x)
       have i₂ := eq1105
       grind)
    | exact superpose eq1105 eq21
    | exact resolve eq21 eq1105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1122 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  have eq1132 : (σ y) = (σ (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1122
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq1122
    | exact resolve eq1122 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1122
  have eq1158 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (τ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq190 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq190
    | exact resolve eq190 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq1204 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (τ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1158 X0 X1
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq1158
    | (have j0 := eq1158 X0 X1
       grind)
    | exact resolve eq1158 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq1158
  have eq1221 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq544 y x
       have i₂ := eq1132
       grind)
    | exact superpose eq1132 eq544
    | (have j0 := eq544 y x
       grind)
    | exact resolve eq544 eq1132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544 eq1132
  have eq1245 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by grind
  clear eq1221
  have eq1824 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1106
  have eq1835 : (σ y) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1824
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq1824
    | exact resolve eq1824 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1824
  have eq1902 : (k x y) = (τ (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9 (k x y)
       have i₂ := eq1835
       grind)
    | exact superpose eq1835 eq9
    | exact resolve eq9 eq1835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1835
  have eq1946 : y = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1902
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1902
    | exact resolve eq1902 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1902
  have eq2082 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq31 y x
       have i₂ := eq1946
       grind)
    | exact superpose eq1946 eq31
    | (have j0 := eq31 y x
       grind)
    | exact resolve eq31 eq1946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1946
  have eq2087 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq2082
  have eq2204 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq2087
  have eq3068 : (σ y) = (k (σ x) (σ y)) ∨ y = (k x y) := by grind
  clear eq1107
  have eq3080 : (σ y) = (σ (k x y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq3068
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq3068
    | exact resolve eq3068 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3068
  have eq3373 : (k x y) = (τ (σ y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq9 (k x y)
       have i₂ := eq3080
       grind)
    | exact superpose eq3080 eq9
    | exact resolve eq9 eq3080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3080
  have eq3428 : y = (k x y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq3373
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq3373
    | exact resolve eq3373 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3373
  have eq3429 : y = (k x y) := by grind
  clear eq3428
  have eq4235 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1120
       grind)
    | exact superpose eq1120 eq14
    | exact resolve eq14 eq1120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1120
  have eq4639 : (σ x) ≠ (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq4235
       have i₂ := eq1245
       grind)
    | exact superpose eq1245 eq4235
    | exact resolve eq4235 eq1245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1245
  have eq4640 : (σ x) ≠ (σ y) ∨ y = (M.op x x) := by grind
  clear eq4639
  have eq11940 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1204 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1204
    | (have j0 := eq1204 X1 (τ X0)
       grind)
    | exact resolve eq1204 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1204
  have eq13396 : (τ (σ y)) = (k (τ (σ x)) x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq61 (σ x) x
       have i₂ := eq1105
       grind)
    | exact superpose eq1105 eq61
    | exact resolve eq61 eq1105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq1105
  have eq13821 : (τ (σ y)) = (k (τ (σ x)) x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq13396
       have r₂ := eq4640
       grind)
    | exact resolve eq13396 eq4640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4640 eq13396
  have eq13869 : (k x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq13821
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq13821
    | exact resolve eq13821 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13821
  have eq13878 : y = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq13869
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq13869
    | exact resolve eq13869 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13869
  have eq13897 : y = (M.op x x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq26 x x
       have i₂ := eq13878
       grind)
    | exact superpose eq13878 eq26
    | exact resolve eq26 eq13878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq13878
  have eq13907 : y = (M.op x x) ∨ x = y := by grind
  clear eq13897
  have eq14159 : x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq21 x
       have i₂ := eq13907
       grind)
    | exact superpose eq13907 eq21
    | exact resolve eq21 eq13907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq13907
  have eq14181 : x = (M.op x y) := by
    first
    | (have r₁ := eq14159
       have r₂ := eq2204
       grind)
    | exact resolve eq14159 eq2204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2204 eq14159
  have eq14339 : (σ x) ≠ (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq4235
       have i₂ := eq14181
       grind)
    | exact superpose eq14181 eq4235
    | exact resolve eq4235 eq14181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4235
  have eq14358 : y = (M.op x x) := by grind
  clear eq14339
  have eq14736 : ∀ X0 : G, (M.op x X0) = (k x X0) ∨ (τ X0) = (τ y) := by
    intro X0
    first
    | (have i₁ := eq11940 X0 x
       have i₂ := eq14358
       grind)
    | exact superpose eq14358 eq11940
    | (have j0 := eq11940 X0 x
       grind)
    | exact resolve eq11940 eq14358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11940
  have eq17391 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq198 y x
       grind)
    | exact superpose eq198 eq14
    | (have j1 := eq198 y x
       grind)
    | exact resolve eq14 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq17479 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17391
       have i₂ := eq3429
       grind)
    | exact superpose eq3429 eq17391
    | exact resolve eq17391 eq3429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3429 eq17391
  have eq17484 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17479
       have i₂ := eq14181
       grind)
    | exact superpose eq14181 eq17479
    | exact resolve eq17479 eq14181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17479
  have eq17646 : (σ x) = (M.op (σ x) (σ (M.op x x))) ∨ (σ x) = (σ (M.op x x)) ∨ (τ y) = (τ x) := by
    first
    | (have i₁ := eq894 x
       have i₂ := eq14736 x
       grind)
    | exact superpose eq14736 eq894
    | (have j1 := eq14736 x
       grind)
    | exact resolve eq894 eq14736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq894 eq14736
  have eq17700 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op x x)) ∨ (τ y) = (τ x) := by
    first
    | (have i₁ := eq17646
       have i₂ := eq14358
       grind)
    | exact superpose eq14358 eq17646
    | exact resolve eq17646 eq14358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17646
  have eq17709 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (τ y) = (τ x) := by
    first
    | (have i₁ := eq17700
       have i₂ := eq14358
       grind)
    | exact superpose eq14358 eq17700
    | exact resolve eq17700 eq14358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17700
  have eq17711 : (σ x) = (M.op (σ x) (σ y)) ∨ (τ y) = (τ x) := by
    first
    | (have r₁ := eq17709
       have r₂ := eq17484
       grind)
    | exact resolve eq17709 eq17484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17709
  have eq20686 : (σ (M.op x y)) ≠ (σ x) ∨ (τ y) = (τ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq17711
       grind)
    | exact superpose eq17711 eq14
    | exact resolve eq14 eq17711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17711
  have eq20742 : (σ x) ≠ (σ x) ∨ (τ y) = (τ x) := by
    first
    | (have i₁ := eq20686
       have i₂ := eq14181
       grind)
    | exact superpose eq14181 eq20686
    | exact resolve eq20686 eq14181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14181 eq20686
  have eq20743 : (τ y) = (τ x) := by grind
  clear eq20742
  have eq21254 : y = (σ (τ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq20743
       grind)
    | exact superpose eq20743 eq10
    | exact resolve eq10 eq20743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20743
  have eq21289 : x = y := by
    first
    | (have i₁ := eq21254
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq21254
    | exact resolve eq21254 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21254
  have eq21859 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq21289
       grind)
    | exact superpose eq21289 eq14
    | exact resolve eq14 eq21289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21889 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq17484
       have i₂ := eq21289
       grind)
    | exact superpose eq21289 eq17484
    | exact resolve eq17484 eq21289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17484
  have eq21892 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq21889
  have eq21900 : (σ y) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq21859
       have i₂ := eq14358
       grind)
    | exact superpose eq14358 eq21859
    | exact resolve eq21859 eq14358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14358 eq21859
  have eq21902 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq21900
       have i₂ := eq21892
       grind)
    | exact superpose eq21892 eq21900
    | exact resolve eq21900 eq21892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21892 eq21900
  have eq21905 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq21902
       have i₂ := eq21289
       grind)
    | exact superpose eq21289 eq21902
    | exact resolve eq21902 eq21289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21289 eq21902
  have eq21906 : False := by grind
  exact eq21906

/-- `Equation1235`: `x = x ◇ (((x ◇ y) ◇ z) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation1235 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1235 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law1235.models_iff G M).mp hM
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
  have eq50 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X0 X1) = (k X0 X2) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq682 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq683 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq682 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682
  have eq691 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq683 (σ X0) (σ X1)
       grind)
    | exact superpose eq683 eq13
    | exact resolve eq13 eq683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq706 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq691 X0 X1
       have i₂ := eq683 X0 X1
       grind)
    | exact superpose eq683 eq691
    | exact resolve eq691 eq683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683 eq691
  have eq2113 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq706 x y
       grind)
    | exact superpose eq706 eq14
    | (have r₁ := eq14
       have r₂ := eq706 x y
       grind)
    | exact resolve eq14 eq706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706
  have eq2146 : False := by grind
  exact eq2146

/-- `Equation1236`: `x = x ◇ (((x ◇ y) ◇ z) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation1236 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1236 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law1236.models_iff G M).mp hM
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
  have eq50 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X0 X1) = (k X0 X2) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq568 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq569 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq568 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568
  have eq577 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq569 (σ X0) (σ X1)
       grind)
    | exact superpose eq569 eq13
    | exact resolve eq13 eq569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq592 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq577 X0 X1
       have i₂ := eq569 X0 X1
       grind)
    | exact superpose eq569 eq577
    | exact resolve eq577 eq569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569 eq577
  have eq1839 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq592 x y
       grind)
    | exact superpose eq592 eq14
    | (have r₁ := eq14
       have r₂ := eq592 x y
       grind)
    | exact resolve eq14 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592
  have eq1864 : False := by grind
  exact eq1864

/-- `Equation1243`: `x = x ◇ (((y ◇ x) ◇ y) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation1243 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1243 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law1243.models_iff G M).mp hM
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
  have eq1178 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
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
  have eq1200 : False := by grind
  exact eq1200

/-- `Equation1245`: `x = x ◇ (((y ◇ x) ◇ z) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation1245 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1245 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law1245.models_iff G M).mp hM
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
  have eq1334 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
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
  have eq1356 : False := by grind
  exact eq1356
