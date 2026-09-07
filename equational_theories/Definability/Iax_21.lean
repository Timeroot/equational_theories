import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation413 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law413 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
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
  have eq47 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq52 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq87 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq91 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq87 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq87 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq87 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq87 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq107 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq91 (σ X0) (σ X1)
       grind)
    | exact superpose eq91 eq13
    | exact resolve eq13 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq107 X0 X1
       have i₂ := eq91 X0 X1
       grind)
    | exact superpose eq91 eq107
    | exact resolve eq107 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq107
  have eq1473 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq114 x y
       grind)
    | exact superpose eq114 eq14
    | (have r₁ := eq14
       have r₂ := eq114 x y
       grind)
    | exact resolve eq14 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq1492 : False := by grind
  exact eq1492

/-- `Equation417`: `x = x ◇ (x ◇ (y ◇ (x ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation417 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law417 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law417.models_iff G M).mp hM
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
  have eq53 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq87 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq91 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq87 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq87 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq87 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq87 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq107 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq91 (σ X0) (σ X1)
       grind)
    | exact superpose eq91 eq13
    | exact resolve eq13 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq107 X0 X1
       have i₂ := eq91 X0 X1
       grind)
    | exact superpose eq91 eq107
    | exact resolve eq107 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq107
  have eq1474 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq114 x y
       grind)
    | exact superpose eq114 eq14
    | (have r₁ := eq14
       have r₂ := eq114 x y
       grind)
    | exact resolve eq14 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq1493 : False := by grind
  exact eq1493

/-- `Equation418`: `x = x ◇ (x ◇ (y ◇ (x ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation418 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law418 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law418.models_iff G M).mp hM
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
  have eq45 : ∀ X0 X1 X2 : G, (M.op X0 X2) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X2) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq11 X1 X1
       have i₂ := eq12 X1 X1
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
  have eq425 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq426 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq425 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425
  have eq432 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq426 (σ X0) (σ X1)
       grind)
    | exact superpose eq426 eq13
    | exact resolve eq13 eq426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq445 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq432 X0 X1
       have i₂ := eq426 X0 X1
       grind)
    | exact superpose eq426 eq432
    | exact resolve eq432 eq426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426 eq432
  have eq1184 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq445 x y
       grind)
    | exact superpose eq445 eq14
    | (have r₁ := eq14
       have r₂ := eq445 x y
       grind)
    | exact resolve eq14 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445
  have eq1208 : False := by grind
  exact eq1208

/-- `Equation419`: `x = x ◇ (x ◇ (y ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation419 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law419 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law419.models_iff G M).mp hM
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
  have eq48 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq53 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq88 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq92 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq88 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq88 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq88 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq88 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq108 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq92 (σ X0) (σ X1)
       grind)
    | exact superpose eq92 eq13
    | exact resolve eq13 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq108 X0 X1
       have i₂ := eq92 X0 X1
       grind)
    | exact superpose eq92 eq108
    | exact resolve eq108 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq108
  have eq1315 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq115 x y
       grind)
    | exact superpose eq115 eq14
    | (have r₁ := eq14
       have r₂ := eq115 x y
       grind)
    | exact resolve eq14 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq1336 : False := by grind
  exact eq1336

/-- `Equation422`: `x = x ◇ (x ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation422 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law422 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law422.models_iff G M).mp hM
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
  have eq55 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq91 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq95 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq91 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq91 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq91 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq91 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq111 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq95 (σ X0) (σ X1)
       grind)
    | exact superpose eq95 eq13
    | exact resolve eq13 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq111 X0 X1
       have i₂ := eq95 X0 X1
       grind)
    | exact superpose eq95 eq111
    | exact resolve eq111 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq111
  have eq1034 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq118 x y
       grind)
    | exact superpose eq118 eq14
    | (have r₁ := eq14
       have r₂ := eq118 x y
       grind)
    | exact resolve eq14 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq1058 : False := by grind
  exact eq1058

/-- `Equation4268`: `x ◇ (x ◇ x) = x ◇ (x ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pxx_pxy_Equation4268 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4268 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4268.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X1)) := by
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
  have eq18 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X2
       have i₂ := eq8 X0 X1
       grind)
    | (have i₁ := eq8 X1 X1
       have i₂ := eq8 X1 X1
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
  have eq29 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 (M.op X1 X2)) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq8 X0 X1
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq31 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq34 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
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
  have eq39 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq66 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq81 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq30 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq136 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X0) (M.op (σ X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq29 (σ X1) (σ X0) X2
       grind)
    | exact superpose eq29 eq13
    | (have j1 := eq29 (σ X1) (σ X0) X2
       grind)
    | exact resolve eq13 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq142 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op X0 X2) ∨ (M.op X0 X2) = (k X0 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq81 X0 (M.op X0 X2)
       have i₂ := eq18 X0 X2 X1
       grind)
    | (have i₁ := eq81 X0 (M.op X0 X2)
       have i₂ := eq18 X0 X1 X2
       grind)
    | exact superpose eq18 eq81
    | (have j0 := eq81 X0 (M.op X0 X2)
       grind)
    | (have r₁ := eq81 X0 (M.op X0 (M.op X0 X2))
       have r₂ := eq18 X0 (M.op X0 X2) X2
       grind)
    | (have r₁ := eq81 X0 (M.op X0 (M.op X0 X1))
       have r₂ := eq18 X0 X1 (M.op X0 X1)
       grind)
    | exact resolve eq81 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq207 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq31 x y
       grind)
    | exact superpose eq31 eq14
    | (have j1 := eq31 x y
       grind)
    | exact resolve eq14 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq9
    | (have j1 := eq31 X0 X1
       grind)
    | exact resolve eq9 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219 : ∀ X0 X1 X2 : G, (σ (k X1 X2)) = (k (σ X1) (M.op (σ X0) (σ X0))) ∨ (σ (k X0 X2)) = (M.op (σ X0) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X2
       have i₂ := eq31 X0 X2
       grind)
    | exact superpose eq31 eq13
    | (have j1 := eq31 X0 X2
       grind)
    | exact resolve eq13 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq475 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq34
    | exact resolve eq34 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq508 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq10
    | (have j1 := eq34 X0 X1
       grind)
    | exact resolve eq10 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq528 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq475 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq475
    | (have j0 := eq475 X0 X1
       grind)
    | exact resolve eq475 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475
  have eq1083 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq207
       have i₂ := eq528 y x
       grind)
    | exact superpose eq528 eq207
    | (have j1 := eq528 (σ y) (σ x)
       grind)
    | (have r₁ := eq207
       have r₂ := eq528 y x
       grind)
    | exact resolve eq207 eq528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq1084 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq1083
  have eq1123 : ∀ X0 X1 X2 : G, X0 = X2 ∨ (σ (k X1 X2)) = (M.op (σ X1) (σ X2)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq217 X1 X2
       have i₂ := eq217 X1 X0
       grind)
    | (have i₁ := eq217 X0 X1
       have i₂ := eq217 X0 (τ (M.op (σ X0) (σ X0)))
       grind)
    | exact superpose eq217 eq217
    | (have j0 := eq217 X1 X2
       have j1 := eq217 X1 X2
       grind)
    | exact resolve eq217 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1130 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (τ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq217 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq217
    | exact resolve eq217 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1167 : ∀ X0 X1 X2 : G, (M.op (σ X0) (M.op (σ X0) X2)) = (M.op (σ X0) (σ (k X0 X1))) ∨ (τ (M.op (σ X0) (σ X0))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 (σ X0) (σ X1) X2
       have i₂ := eq217 X0 X1
       grind)
    | exact superpose eq217 eq18
    | (have j1 := eq217 X0 X1
       grind)
    | exact resolve eq18 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq1174 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (τ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1130 X0 X1
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq1130
    | (have j0 := eq1130 X0 X1
       grind)
    | exact resolve eq1130 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq1130
  have eq2868 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (M.op (σ X0) X2)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq136 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq4309 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  clear eq219
  have eq5181 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1174 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1174
    | (have j0 := eq1174 X1 (τ X0)
       grind)
    | exact resolve eq1174 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1174
  have eq14599 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (k X0 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq142 X0 X1 (M.op X0 X1)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq31861 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq4309 (τ X1) (τ X0)
       have i₂ := eq66 X0 X1
       grind)
    | exact superpose eq66 eq4309
    | exact resolve eq4309 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32179 : (σ y) = (σ (k x x)) ∨ (σ y) = (σ (k x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq4309 x x
       have i₂ := eq1084
       grind)
    | exact superpose eq1084 eq4309
    | exact resolve eq4309 eq1084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1084
  have eq32444 : ∀ X0 : G, (σ (k X0 X0)) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq4309 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4309
  have eq32445 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq32444 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32444
  have eq32452 : (σ y) = (σ (k x x)) ∨ y = (M.op x x) := by grind
  clear eq32179
  have eq32870 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (σ (k (τ X0) (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq31861 X0 X1
       have i₂ := eq32445 (τ X0)
       grind)
    | exact superpose eq32445 eq31861
    | (have j0 := eq31861 X0 X1
       grind)
    | exact resolve eq31861 eq32445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31861
  have eq33130 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (k (σ (τ X0)) X0) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq32870 X0 X1
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq32870
    | (have j0 := eq32870 X0 X1
       grind)
    | exact resolve eq32870 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32870
  have eq33271 : ∀ X0 X1 : G, (k X0 X0) = (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq33130 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq33130
    | (have j0 := eq33130 X0 X1
       grind)
    | exact resolve eq33130 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33130
  have eq33346 : ∀ X0 X1 : G, (k X0 X1) = (k X0 X0) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq33271 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq33271
    | (have j0 := eq33271 X0 X1
       grind)
    | exact resolve eq33271 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33271
  have eq33384 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq33346 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq33346
    | (have j0 := eq33346 X0 X1
       grind)
    | exact resolve eq33346 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33346
  have eq33402 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (k X0 X1))) ∨ (k X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq33384 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq33384
    | (have j0 := eq33384 X0 X1
       grind)
    | exact resolve eq33384 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33384
  have eq33407 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq33402 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq33402
    | (have j0 := eq33402 X0 X1
       grind)
    | exact resolve eq33402 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33402
  have eq33441 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq32445 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq32445
    | exact resolve eq32445 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33548 : ∀ X0 X1 : G, (τ X1) = (τ (σ (k X0 X0))) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5181 X1 (σ X0)
       have i₂ := eq32445 X0
       grind)
    | exact superpose eq32445 eq5181
    | (have j0 := eq5181 X1 (σ X0)
       grind)
    | exact resolve eq5181 eq32445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5181
  have eq33557 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ X0) X1)) = (M.op (σ X0) (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 (σ X0) X1 (σ X0)
       have i₂ := eq32445 X0
       grind)
    | exact superpose eq32445 eq18
    | exact resolve eq18 eq32445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33574 : ∀ X0 X1 : G, (τ X1) = (k X0 X0) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq33548 X0 X1
       have i₂ := eq9 (k X0 X0)
       grind)
    | exact superpose eq9 eq33548
    | (have j0 := eq33548 X0 X1
       grind)
    | exact resolve eq33548 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33548
  have eq33620 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq33441 X0
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq33441
    | exact resolve eq33441 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq33441
  have eq33645 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq33620 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq33620
    | exact resolve eq33620 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33620
  have eq42839 : (k x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq32452
       grind)
    | exact superpose eq32452 eq9
    | exact resolve eq9 eq32452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32452
  have eq43071 : y = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq42839
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq42839
    | exact resolve eq42839 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42839
  have eq43157 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq43071
       have i₂ := eq33645 x
       grind)
    | exact superpose eq33645 eq43071
    | exact resolve eq43071 eq33645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43071
  have eq43158 : y = (M.op x x) := by grind
  clear eq43157
  have eq43954 : ∀ X0 : G, (M.op x y) = (M.op x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq18 x X0 x
       have i₂ := eq43158
       grind)
    | exact superpose eq43158 eq18
    | exact resolve eq18 eq43158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq43959 : (M.op x y) = (k x (M.op x y)) := by
    first
    | (have i₁ := eq14599 x x
       have i₂ := eq43158
       grind)
    | exact superpose eq43158 eq14599
    | exact resolve eq14599 eq43158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55269 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq33645 X0
       have i₂ := eq33407 X0 X1
       grind)
    | (have i₁ := eq33645 X1
       have i₂ := eq33407 X1 X1
       grind)
    | exact superpose eq33407 eq33645
    | (have j1 := eq33407 X0 X1
       grind)
    | exact resolve eq33645 eq33407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55385 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 X0) ∨ (k X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq33407 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55386 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq33407 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33407
  have eq55387 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq55386 X0 X1
       have i₂ := eq33645 X0
       grind)
    | exact superpose eq33645 eq55386
    | (have j0 := eq55386 X0 X1
       grind)
    | (have r₁ := eq55386 X0 X0
       have r₂ := eq33645 X0
       grind)
    | exact resolve eq55386 eq33645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55386
  have eq55388 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq55385 X0 X1
       have i₂ := eq33645 X0
       grind)
    | exact superpose eq33645 eq55385
    | (have j0 := eq55385 X0 X1
       grind)
    | (have r₁ := eq55385 X0 X0
       have r₂ := eq33645 X0
       grind)
    | exact resolve eq55385 eq33645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55385
  have eq55753 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq55388 X0 X1
       have i₂ := eq33645 X0
       grind)
    | exact superpose eq33645 eq55388
    | (have j0 := eq55388 X0 X1
       grind)
    | exact resolve eq55388 eq33645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55388
  have eq58976 : ∀ X0 : G, (M.op x y) ≠ (M.op x x) ∨ (M.op x x) = (k x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq55753 x (M.op x X0)
       have i₂ := eq43954 X0
       grind)
    | exact superpose eq43954 eq55753
    | (have j0 := eq55753 x y
       grind)
    | exact resolve eq55753 eq43954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55753
  have eq59027 : ∀ X0 : G, y ≠ (M.op x y) ∨ (M.op x x) = (k x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq58976 X0
       have i₂ := eq43158
       grind)
    | exact superpose eq43158 eq58976
    | (have j0 := eq58976 X0
       grind)
    | exact resolve eq58976 eq43158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58976
  have eq59095 : ∀ X0 : G, y ≠ (M.op x y) ∨ y = (k x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq59027 X0
       have i₂ := eq43158
       grind)
    | exact superpose eq43158 eq59027
    | exact resolve eq59027 eq43158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59027
  have eq87198 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) ≠ (M.op (σ (τ X0)) (M.op (σ (τ X0)) X2)) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2868 (τ X1) (τ X0) X2
       have i₂ := eq66 X0 X1
       grind)
    | exact superpose eq66 eq2868
    | exact resolve eq2868 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq2868
  have eq87581 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X2)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq87198 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq87198
    | (have j0 := eq87198 X0 X1 X2
       grind)
    | exact resolve eq87198 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87198
  have eq87698 : ∀ X0 X1 X2 : G, (k X0 X1) ≠ (M.op X0 (M.op X0 X2)) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq87581 X0 X1 X2
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq87581
    | (have j0 := eq87581 X0 X1 X2
       grind)
    | exact resolve eq87581 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87581
  have eq87762 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ (M.op X0 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq87698 X0 X1 X2
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq87698
    | (have j0 := eq87698 X0 X1 X2
       grind)
    | exact resolve eq87698 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87698
  have eq87803 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (σ (τ (k X0 X1))) ∨ (k X0 X1) ≠ (M.op X0 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq87762 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq87762
    | (have j0 := eq87762 X0 X1 X2
       grind)
    | exact resolve eq87762 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87762
  have eq87826 : ∀ X0 X1 X2 : G, (k X0 X1) ≠ (M.op X0 (M.op X0 X2)) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq87803 X0 X1 X2
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq87803
    | (have j0 := eq87803 X0 X1 X2
       grind)
    | exact resolve eq87803 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87803
  have eq88073 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ X0) X1)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq33557 X0 X1
       have i₂ := eq33645 X0
       grind)
    | exact superpose eq33645 eq33557
    | exact resolve eq33557 eq33645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33557
  have eq89872 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq33574 X0 (σ X1)
       grind)
    | exact superpose eq33574 eq9
    | (have j1 := eq33574 X0 (σ X1)
       grind)
    | exact resolve eq9 eq33574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33574
  have eq90382 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq89872 X0 X1
       have i₂ := eq33645 X0
       grind)
    | exact superpose eq33645 eq89872
    | (have j0 := eq89872 X0 X1
       grind)
    | exact resolve eq89872 eq33645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89872
  have eq90770 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq90382 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq90382
    | (have j0 := eq90382 X0 X1
       grind)
    | exact resolve eq90382 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90382
  have eq119392 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq88073 x X0
       have i₂ := eq43158
       grind)
    | exact superpose eq43158 eq88073
    | exact resolve eq88073 eq43158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88073
  have eq124259 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq14599 (σ x) x
       have i₂ := eq119392 x
       grind)
    | exact superpose eq119392 eq14599
    | exact resolve eq14599 eq119392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14599
  have eq128405 : (τ (M.op (σ x) (σ y))) = (k x (τ (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq39 x (M.op (σ x) (σ y))
       have i₂ := eq124259
       grind)
    | exact superpose eq124259 eq39
    | exact resolve eq39 eq124259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq130711 : ∀ X0 X1 X2 : G, X0 = X2 ∨ (σ (k X1 X2)) = (σ (M.op X1 X2)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq528 X2 X1
       have i₂ := eq90770 X1 X0
       grind)
    | (have i₁ := eq528 X0 X1
       have i₂ := eq90770 X0 (M.op X1 X1)
       grind)
    | exact superpose eq90770 eq528
    | (have j0 := eq528 X2 X1
       have j1 := eq90770 X1 X0
       grind)
    | exact resolve eq528 eq90770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528 eq90770
  have eq139518 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = X0 ∨ (σ (k x X0)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq1123 y x X0
       grind)
    | exact superpose eq1123 eq14
    | (have j1 := eq1123 y x X0
       grind)
    | (have r₁ := eq14
       have r₂ := eq1123 (σ (M.op x y)) x (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq14
       have r₂ := eq1123 (M.op (σ x) (σ y)) x (σ (M.op x y))
       grind)
    | exact resolve eq14 eq1123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1123
  have eq139730 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ y = X0 := by
    intro X0
    first
    | (have j0 := eq139518 X0
       have j1 := eq130711 (σ (k x X0)) x (M.op (σ x) (σ X0))
       grind)
    | (have r₁ := eq139518 X0
       have r₂ := eq130711 (σ (M.op x y)) x (σ (k x y))
       grind)
    | (have r₁ := eq139518 X0
       have r₂ := eq130711 (σ (k x y)) x (σ (M.op x y))
       grind)
    | (have r₁ := eq139518 X0
       have r₂ := eq130711 X0 x y
       grind)
    | exact resolve eq139518 eq130711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130711 eq139518
  have eq141277 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op x y) = (τ (M.op (σ x) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq1167 x (M.op x y) X0
       have i₂ := eq43959
       grind)
    | exact superpose eq43959 eq1167
    | (have j0 := eq1167 x (M.op x y) x
       grind)
    | exact resolve eq1167 eq43959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1167
  have eq141724 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op x y) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq141277 x
       have i₂ := eq119392 x
       grind)
    | exact superpose eq119392 eq141277
    | exact resolve eq141277 eq119392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119392 eq141277
  have eq142099 : (M.op x y) = (τ (σ (k x x))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq141724
       have i₂ := eq32445 x
       grind)
    | exact superpose eq32445 eq141724
    | exact resolve eq141724 eq32445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32445 eq141724
  have eq142437 : (M.op x y) = (k x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq142099
       have i₂ := eq9 (k x x)
       grind)
    | exact superpose eq9 eq142099
    | exact resolve eq142099 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142099
  have eq142704 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq142437
       have i₂ := eq33645 x
       grind)
    | exact superpose eq33645 eq142437
    | exact resolve eq142437 eq33645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33645 eq142437
  have eq142881 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq142704
       have i₂ := eq43158
       grind)
    | exact superpose eq43158 eq142704
    | exact resolve eq142704 eq43158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142704
  have eq205683 : ∀ X0 : G, (M.op x y) ≠ (k x X0) ∨ (M.op x X0) = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq87826 x X0 x
       have i₂ := eq43954 x
       grind)
    | exact superpose eq43954 eq87826
    | (have j0 := eq87826 x X0 x
       grind)
    | exact resolve eq87826 eq43954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43954 eq87826
  have eq206881 : ∀ X0 : G, (M.op x y) ≠ (M.op x x) ∨ (M.op x X0) = (M.op x x) ∨ (M.op x X0) = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq205683 x
       have i₂ := eq55269 x x
       grind)
    | exact superpose eq55269 eq205683
    | (have j0 := eq205683 X0
       have j1 := eq55269 x X0
       grind)
    | (have r₁ := eq205683 y
       have r₂ := eq55269 x y
       grind)
    | exact resolve eq205683 eq55269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55269 eq205683
  have eq206913 : ∀ X0 : G, (M.op x y) ≠ (M.op x x) ∨ (M.op x X0) = (k x X0) := by
    intro X0
    first
    | (have j0 := eq206881 X0
       have j1 := eq55387 x y
       grind)
    | (have r₁ := eq206881 x
       have r₂ := eq55387 x x
       grind)
    | (have r₁ := eq206881 x
       have r₂ := eq55387 x x
       grind)
    | exact resolve eq206881 eq55387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55387 eq206881
  have eq206925 : ∀ X0 : G, y ≠ (M.op x y) ∨ (M.op x X0) = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq206913 X0
       have i₂ := eq43158
       grind)
    | exact superpose eq43158 eq206913
    | (have j0 := eq206913 X0
       grind)
    | exact resolve eq206913 eq43158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206913
  have eq1132494 : (M.op (σ x) (σ y)) = (σ (k x (M.op x y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq139730 (M.op x y)
       have i₂ := eq142881
       grind)
    | exact superpose eq142881 eq139730
    | (have j0 := eq139730 (M.op x y)
       grind)
    | exact resolve eq139730 eq142881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139730 eq142881
  have eq1132504 : (M.op (σ x) (σ y)) = (σ (k x (M.op x y))) ∨ y = (M.op x y) := by grind
  clear eq1132494
  have eq1132507 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1132504
       have i₂ := eq43959
       grind)
    | exact superpose eq43959 eq1132504
    | exact resolve eq1132504 eq43959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43959 eq1132504
  have eq1132509 : y = (M.op x y) := by
    first
    | (have r₁ := eq1132507
       have r₂ := eq14
       grind)
    | exact resolve eq1132507 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1132507
  have eq1132532 : ∀ X0 : G, y ≠ y ∨ y = (k x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq59095 X0
       have i₂ := eq1132509
       grind)
    | exact superpose eq1132509 eq59095
    | (have j0 := eq59095 X0
       grind)
    | (have r₁ := eq59095 X0
       have r₂ := eq1132509
       grind)
    | exact resolve eq59095 eq1132509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59095
  have eq1132539 : ∀ X0 : G, y ≠ y ∨ (M.op x X0) = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq206925 X0
       have i₂ := eq1132509
       grind)
    | exact superpose eq1132509 eq206925
    | (have j0 := eq206925 X0
       grind)
    | (have r₁ := eq206925 X0
       have r₂ := eq1132509
       grind)
    | exact resolve eq206925 eq1132509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206925
  have eq1132598 : ∀ X0 : G, (M.op x X0) = (k x X0) := by
    intro X0
    first
    | (have j0 := eq1132539 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1132539
  have eq1132605 : ∀ X0 : G, y = (k x (M.op x X0)) := by
    intro X0
    first
    | (have j0 := eq1132532 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1132532
  have eq1132627 : ∀ X0 : G, y = (M.op x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq1132605 X0
       have i₂ := eq1132598 (M.op x X0)
       grind)
    | exact superpose eq1132598 eq1132605
    | exact resolve eq1132605 eq1132598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1132605
  have eq1132768 : (τ (M.op (σ x) (σ y))) = (M.op x (τ (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq128405
       have i₂ := eq1132598 (τ (M.op (σ x) (σ y)))
       grind)
    | exact superpose eq1132598 eq128405
    | exact resolve eq128405 eq1132598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128405 eq1132598
  have eq1169764 : y = (M.op x (τ (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq1132627 (τ (M.op (σ x) (σ y)))
       have i₂ := eq1132768
       grind)
    | exact superpose eq1132768 eq1132627
    | exact resolve eq1132627 eq1132768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1132627 eq1132768
  have eq1169969 : (σ y) = (k (σ x) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq508 x (M.op (σ x) (σ y))
       have i₂ := eq1169764
       grind)
    | exact superpose eq1169764 eq508
    | (have j0 := eq508 x (M.op (σ x) (σ y))
       grind)
    | exact resolve eq508 eq1169764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508 eq1169764
  have eq1170018 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq1169969
       have i₂ := eq124259
       grind)
    | exact superpose eq124259 eq1169969
    | exact resolve eq1169969 eq124259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124259 eq1169969
  have eq1170070 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1170018
       have i₂ := eq43158
       grind)
    | exact superpose eq43158 eq1170018
    | exact resolve eq1170018 eq43158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43158 eq1170018
  have eq1170071 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1170070
  have eq1178086 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1170071
       grind)
    | exact superpose eq1170071 eq14
    | exact resolve eq14 eq1170071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1170071
  have eq1178257 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq1178086
       have i₂ := eq1132509
       grind)
    | exact superpose eq1132509 eq1178086
    | exact resolve eq1178086 eq1132509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1132509 eq1178086
  have eq1178258 : False := by grind
  exact eq1178258

/-- `Equation4277`: `x ◇ (x ◇ x) = y ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation4277 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4277 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4277.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X1 X2)) := by
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
  have eq18 : ∀ X0 X1 X3 X4 : G, (M.op X0 (M.op X0 X1)) = (M.op X3 (M.op X3 X4)) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq8 x X3 X4
       have i₂ := eq8 x X0 X1
       grind)
    | (have i₁ := eq8 x X1 x
       have i₂ := eq8 X0 x x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X2)) = (M.op X3 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 X3 (M.op X3 X3)
       have i₂ := eq8 X3 X0 X1
       grind)
    | (have i₁ := eq8 X0 X1 (M.op X1 X2)
       have i₂ := eq8 X0 X1 X2
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
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq32 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X3)) = (M.op X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
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
  have eq33 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq35 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq38 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
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
  have eq43 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq57 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X2 X3)) = (M.op X4 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq18 X2 X3 X4 (M.op X4 x)
       have i₂ := eq18 X4 x X0 X1
       grind)
    | (have i₁ := eq18 X2 X3 X4 (M.op X4 x)
       have i₂ := eq18 X0 X1 X4 x
       grind)
    | exact superpose eq18 eq18
    | exact resolve eq18 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq79 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq33 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq33
    | exact resolve eq33 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq33 (τ X1) X0
       grind)
    | exact superpose eq33 eq17
    | (have j1 := eq33 (τ X1) X0
       grind)
    | exact resolve eq17 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq33 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 X1 X2 X4 X5 X6 : G, (M.op X0 (M.op X1 (M.op X1 X2))) = (M.op X4 (M.op X5 (M.op X5 X6))) := by
    intro X0 X1 X2 X4 X5 X6
    first
    | (have i₁ := eq20 X5 X6 x X4
       have i₂ := eq20 X1 X2 x X0
       grind)
    | exact superpose eq20 eq20
    | exact resolve eq20 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (k (M.op X1 (M.op X1 X2)) (M.op X0 (M.op X0 X0))) := by
    intro X0 X1 X2
    grind
  clear eq20
  have eq150 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq43
  have eq164 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq150 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq150
    | exact resolve eq150 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150
  have eq295 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (M.op X0 (M.op X0 X1)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq14
       have i₂ := eq32 (σ y) (σ x) X0 X1
       grind)
    | exact superpose eq32 eq14
    | (have j1 := eq32 (σ y) (σ x) x x
       grind)
    | exact resolve eq14 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq305 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (M.op X0 (M.op X0 X1)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq295 X0 X1
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq295
    | (have j0 := eq295 X0 X1
       grind)
    | exact resolve eq295 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295
  have eq410 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq164 X1
       have i₂ := eq12 (σ X1) X0
       grind)
    | (have i₁ := eq164 X0
       have i₂ := eq12 X0 (M.op (σ X0) (σ X0))
       grind)
    | exact superpose eq12 eq164
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq164 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq562 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X3)) = (k (M.op X2 (M.op X2 X3)) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    grind
  have eq584 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq35 X0 X0
       have i₂ := eq12 (σ X0) X1
       grind)
    | (have i₁ := eq35 X0 X1
       have i₂ := eq12 X0 (M.op (σ X0) (σ X1))
       grind)
    | exact superpose eq12 eq35
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq35 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq600 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq35 x y
       grind)
    | exact superpose eq35 eq14
    | (have j1 := eq35 x y
       grind)
    | exact resolve eq14 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq619 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq9
    | (have j1 := eq35 X0 X1
       grind)
    | exact resolve eq9 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq647 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq35 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1734 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq647 (τ X0)
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq647
    | (have j0 := eq647 (τ X0)
       grind)
    | exact resolve eq647 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1736 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1734 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1734
    | (have j0 := eq1734 X0
       grind)
    | exact resolve eq1734 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1734
  have eq1739 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1736 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1736
    | (have j0 := eq1736 X0
       grind)
    | exact resolve eq1736 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1736
  have eq1766 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq38
    | exact resolve eq38 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq1862 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1766 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1766
    | (have j0 := eq1766 X0 X1
       grind)
    | exact resolve eq1766 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1766
  have eq1884 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1739 (τ X0)
       have i₂ := eq70 X0 X0
       grind)
    | exact superpose eq70 eq1739
    | (have j0 := eq1739 (τ X0)
       grind)
    | exact resolve eq1739 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq1739
  have eq1886 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq82 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq82
    | exact resolve eq82 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq1927 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1886 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1886
    | (have j0 := eq1886 X0 X1
       grind)
    | exact resolve eq1886 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1886
  have eq2418 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq79 x y
       grind)
    | exact superpose eq79 eq14
    | (have j1 := eq79 x y
       grind)
    | exact resolve eq14 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq3112 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) ≠ (σ (M.op X0 (M.op X0 X0))) ∨ (σ (M.op X0 (M.op X0 X0))) = (M.op (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq647 (M.op X0 (M.op X0 X0))
       have i₂ := eq142 X0 X0 X0
       grind)
    | exact superpose eq142 eq647
    | (have j0 := eq647 (M.op X0 (M.op X0 X0))
       grind)
    | exact resolve eq647 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq3121 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have j0 := eq3112 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3112
  have eq3181 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq600
       have i₂ := eq1927 y x
       grind)
    | exact superpose eq1927 eq600
    | (have j1 := eq1927 y x
       grind)
    | (have r₁ := eq600
       have r₂ := eq1927 y x
       grind)
    | exact resolve eq600 eq1927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1927
  have eq3182 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq600
       have i₂ := eq1862 y x
       grind)
    | exact superpose eq1862 eq600
    | (have j1 := eq1862 (σ y) (σ x)
       grind)
    | (have r₁ := eq600
       have r₂ := eq1862 y x
       grind)
    | exact resolve eq600 eq1862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600 eq1862
  have eq3183 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq3182
  have eq3184 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by grind
  clear eq3181
  have eq3196 : x = (k x (τ (σ y))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq164 x
       have i₂ := eq3183
       grind)
    | exact superpose eq3183 eq164
    | exact resolve eq164 eq3183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3232 : x = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq3196
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq3196
    | exact resolve eq3196 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3196
  have eq3312 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq3232
       grind)
    | exact superpose eq3232 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq3232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3232
  have eq3317 : x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq3312
  have eq4365 : (σ y) = (σ (k x x)) ∨ x = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq619 x x
       have i₂ := eq3183
       grind)
    | exact superpose eq3183 eq619
    | exact resolve eq619 eq3183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619
  have eq4416 : (σ y) = (σ (k x x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq4365
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq4365
    | exact resolve eq4365 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4365
  have eq4732 : x = (k x (τ (σ y))) ∨ x = (k x y) := by
    first
    | (have i₁ := eq164 x
       have i₂ := eq3184
       grind)
    | exact superpose eq3184 eq164
    | exact resolve eq164 eq3184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164 eq3184
  have eq4778 : x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq4732
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq4732
    | exact resolve eq4732 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4732
  have eq4779 : x = (k x y) := by grind
  clear eq4778
  have eq4789 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ (k (τ X0) (τ X0))) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq584 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq584
    | (have j0 := eq584 X1 (τ X0)
       grind)
    | exact resolve eq584 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584
  have eq4906 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4789 X0 X1
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq4789
    | (have j0 := eq4789 X0 X1
       grind)
    | exact resolve eq4789 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq4789
  have eq4916 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4906 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4906
    | (have j0 := eq4906 X0 X1
       grind)
    | exact resolve eq4906 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4906
  have eq6835 : ∀ X0 X1 X2 : G, (σ (M.op x y)) ≠ (M.op X0 (M.op X1 (M.op X1 X2))) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq305 x (M.op x x)
       have i₂ := eq107 x x x X0 X1 X2
       grind)
    | (have i₁ := eq305 x (M.op x x)
       have i₂ := eq107 X0 X1 X2 x x x
       grind)
    | exact superpose eq107 eq305
    | exact resolve eq305 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq305
  have eq6855 : ∀ X0 X1 X2 : G, (σ (M.op x y)) ≠ (M.op X0 (M.op X1 (M.op X1 X2))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6835 X0 X1 X2
       have i₂ := eq4779
       grind)
    | exact superpose eq4779 eq6835
    | (have j0 := eq6835 X0 X1 X2
       grind)
    | exact resolve eq6835 eq4779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4779 eq6835
  have eq23352 : ∀ X0 : G, (τ (σ X0)) ≠ (τ (M.op (σ X0) (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (k X0 (τ (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1884 (σ X0)
       have i₂ := eq410 (σ X0) X0
       grind)
    | exact superpose eq410 eq1884
    | (have j0 := eq1884 (σ X0)
       have j1 := eq410 (σ X0) X0
       grind)
    | exact resolve eq1884 eq410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410 eq1884
  have eq23382 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) ≠ X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (k X0 (τ (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq23352 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq23352
    | (have j0 := eq23352 X0
       grind)
    | exact resolve eq23352 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23352
  have eq23393 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ (M.op (σ X0) (σ X0))) ≠ X0 ∨ (k X0 (τ (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq23382 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq23382
    | (have j0 := eq23382 X0
       grind)
    | exact resolve eq23382 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23382
  have eq23397 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (τ (M.op (σ X0) (σ X0))) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq23393 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq23393
    | (have j0 := eq23393 X0
       grind)
    | exact resolve eq23393 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23393
  have eq23401 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) ≠ X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq23397 X0
       have j1 := eq85 X0 X0
       grind)
    | (have r₁ := eq23397 x
       have r₂ := eq85 x x
       grind)
    | exact resolve eq23397 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23397
  have eq24512 : x ≠ (τ (σ y)) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq23401 x
       have i₂ := eq3183
       grind)
    | exact superpose eq3183 eq23401
    | (have j0 := eq23401 x
       grind)
    | exact resolve eq23401 eq3183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3183 eq23401
  have eq24542 : x ≠ y ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq24512
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq24512
    | exact resolve eq24512 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24512
  have eq28484 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq2418
       have i₂ := eq4916 x y
       grind)
    | exact superpose eq4916 eq2418
    | (have j1 := eq4916 x y
       grind)
    | (have r₁ := eq2418
       have r₂ := eq4916 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq2418
       have r₂ := eq4916 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq2418 eq4916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2418 eq4916
  have eq28493 : (σ (M.op x y)) = (σ x) ∨ y = (k x x) ∨ x = y := by grind
  clear eq28484
  have eq33354 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X0 X1))) ≠ (σ (M.op X0 (M.op X0 X1))) ∨ (σ (M.op X0 (M.op X0 X1))) = (M.op (σ (M.op X0 (M.op X0 X1))) (σ (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq647 (M.op X0 (M.op X0 X1))
       have i₂ := eq562 X0 X1 X0 X1
       grind)
    | exact superpose eq562 eq647
    | (have j0 := eq647 (M.op X0 (M.op X0 X1))
       grind)
    | exact resolve eq647 eq562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq33403 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X0 X1))) = (M.op (σ (M.op X0 (M.op X0 X1))) (σ (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have j0 := eq33354 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33354
  have eq34475 : (k x x) = (τ (σ y)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq4416
       grind)
    | exact superpose eq4416 eq9
    | exact resolve eq9 eq4416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4416
  have eq34584 : y = (k x x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq34475
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq34475
    | exact resolve eq34475 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34475
  have eq35054 : y = (M.op x x) ∨ x = y ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq33 x x
       have i₂ := eq34584
       grind)
    | exact superpose eq34584 eq33
    | exact resolve eq33 eq34584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq34584
  have eq35073 : y = (M.op x x) ∨ x = y := by grind
  clear eq35054
  have eq35338 : ∀ X0 X1 : G, (M.op x y) = (M.op X0 (M.op X0 X1)) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1 x x
       have i₂ := eq35073
       grind)
    | exact superpose eq35073 eq18
    | exact resolve eq18 eq35073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35341 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op x y)) ∨ x = y := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57 x x X0 X1 X2
       have i₂ := eq35073
       grind)
    | exact superpose eq35073 eq57
    | exact resolve eq57 eq35073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq35073
  have eq35869 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ x = y ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq35338 X0 (M.op X0 x)
       have i₂ := eq35338 X0 x
       grind)
    | exact superpose eq35338 eq35338
    | exact resolve eq35338 eq35338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36146 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq35869 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35869
  have eq36946 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = y := by grind
  have eq40863 : ∀ X0 X1 : G, (M.op x y) = (M.op X1 (M.op X0 (M.op x y))) ∨ x = y ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq35338 X1 (M.op X1 x)
       have i₂ := eq35341 X1 x X0
       grind)
    | (have i₁ := eq35338 x (M.op x y)
       have i₂ := eq35341 X0 X1 x
       grind)
    | exact superpose eq35341 eq35338
    | exact resolve eq35338 eq35341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35341
  have eq41022 : ∀ X0 X1 : G, (M.op x y) = (M.op X1 (M.op X0 (M.op x y))) ∨ x = y := by
    intro X0 X1
    first
    | (have j0 := eq40863 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40863
  have eq43165 : x = (k x x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq36946
       have i₂ := eq3317
       grind)
    | exact superpose eq3317 eq36946
    | exact resolve eq36946 eq3317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3317 eq36946
  have eq43185 : x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq43165
       have r₂ := eq24542
       grind)
    | exact resolve eq43165 eq24542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24542 eq43165
  have eq43273 : x = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 x x
       have i₂ := eq43185
       grind)
    | exact superpose eq43185 eq12
    | (have j0 := eq12 x x
       grind)
    | exact resolve eq12 eq43185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43185
  have eq43281 : y = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq43273
  have eq43331 : x ≠ y ∨ x = (k x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq85 x x
       have i₂ := eq43281
       grind)
    | exact superpose eq43281 eq85
    | (have j0 := eq85 x x
       grind)
    | (have r₁ := eq85 x x
       have r₂ := eq43281
       grind)
    | exact resolve eq85 eq43281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43371 : x ≠ y ∨ x = (M.op x x) := by grind
  clear eq43281
  have eq43373 : x ≠ y ∨ x = (k x x) := by
    first
    | (have j1 := eq85 x x
       grind)
    | (have r₁ := eq43331
       have r₂ := eq85 x x
       grind)
    | exact resolve eq43331 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq43331
  have eq47264 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (M.op (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X1 X2 (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0)))
       have i₂ := eq3121 X0
       grind)
    | exact superpose eq3121 eq18
    | exact resolve eq18 eq3121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq47281 : ∀ X0 : G, (M.op x y) = (M.op (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0)))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq35338 (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0)))
       have i₂ := eq3121 X0
       grind)
    | exact superpose eq3121 eq35338
    | exact resolve eq35338 eq3121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47288 : ∀ X0 : G, (M.op x y) = (σ (M.op X0 (M.op X0 X0))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq47281 X0
       have i₂ := eq3121 X0
       grind)
    | exact superpose eq3121 eq47281
    | exact resolve eq47281 eq3121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3121 eq47281
  have eq47305 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq47264 X0 X1 X2
       have i₂ := eq33403 X0 X0
       grind)
    | exact superpose eq33403 eq47264
    | exact resolve eq47264 eq33403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33403 eq47264
  have eq47598 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op X0 (M.op X0 X1)) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq47305 (M.op x y) X0 X1
       have i₂ := eq41022 (M.op x y) (M.op x y)
       grind)
    | exact superpose eq41022 eq47305
    | exact resolve eq47305 eq41022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47305
  have eq53635 : (M.op x y) = (σ (M.op x y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq47288 (M.op x y)
       have i₂ := eq41022 (M.op x y) (M.op x y)
       grind)
    | exact superpose eq41022 eq47288
    | exact resolve eq47288 eq41022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41022 eq47288
  have eq53667 : (M.op x y) = (σ (M.op x y)) ∨ x = y := by grind
  clear eq53635
  have eq54011 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq6855 x x x
       have i₂ := eq47598 x (M.op x x)
       grind)
    | exact superpose eq47598 eq6855
    | (have r₁ := eq6855 x x x
       have r₂ := eq47598 x (M.op x x)
       grind)
    | exact resolve eq6855 eq47598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6855 eq47598
  have eq54101 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq54011
  have eq54151 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq54101
       grind)
    | exact superpose eq54101 eq14
    | exact resolve eq14 eq54101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54202 : (M.op x y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq35338 (σ x) (σ y)
       have i₂ := eq54101
       grind)
    | exact superpose eq54101 eq35338
    | exact resolve eq35338 eq54101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35338
  have eq54229 : (M.op x y) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq54202
  have eq54263 : (M.op x y) ≠ (σ x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq54151
       have i₂ := eq53667
       grind)
    | exact superpose eq53667 eq54151
    | exact resolve eq54151 eq53667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53667
  have eq54264 : (σ x) ≠ (σ x) ∨ x = y ∨ y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq54151
       have i₂ := eq28493
       grind)
    | exact superpose eq28493 eq54151
    | (have r₁ := eq54151
       have r₂ := eq28493
       grind)
    | exact resolve eq54151 eq28493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28493 eq54151
  have eq54268 : (σ x) ≠ (σ x) ∨ x = y ∨ y = (k x x) := by grind
  clear eq54264
  have eq54269 : y = (k x x) ∨ x = y := by grind
  clear eq54268
  have eq54270 : (M.op x y) ≠ (σ x) ∨ x = y := by grind
  clear eq54263
  have eq56002 : (M.op x y) = (σ (k x x)) ∨ (M.op x y) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq35 x x
       have i₂ := eq54229
       grind)
    | exact superpose eq54229 eq35
    | exact resolve eq35 eq54229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq54229
  have eq56102 : (M.op x y) = (σ (k x x)) ∨ x = y := by
    first
    | (have r₁ := eq56002
       have r₂ := eq54270
       grind)
    | exact resolve eq56002 eq54270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56002
  have eq56149 : (M.op x y) = (σ y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq56102
       have i₂ := eq54269
       grind)
    | exact superpose eq54269 eq56102
    | exact resolve eq56102 eq54269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54269 eq56102
  have eq56181 : (M.op x y) = (σ y) ∨ x = y := by grind
  clear eq56149
  have eq56198 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = y ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq36146 X0
       have i₂ := eq56181
       grind)
    | exact superpose eq56181 eq36146
    | exact resolve eq36146 eq56181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36146
  have eq56206 : (σ x) ≠ (σ y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq54270
       have i₂ := eq56181
       grind)
    | exact superpose eq56181 eq54270
    | exact resolve eq54270 eq56181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54270 eq56181
  have eq56264 : (σ x) ≠ (σ y) ∨ x = y := by grind
  clear eq56206
  have eq56272 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq56198 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56198
  have eq57259 : (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq54101
       have i₂ := eq56272 (σ x)
       grind)
    | exact superpose eq56272 eq54101
    | exact resolve eq54101 eq56272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54101 eq56272
  have eq57266 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq57259
  have eq57279 : x = y := by
    first
    | (have r₁ := eq57266
       have r₂ := eq56264
       grind)
    | exact resolve eq57266 eq56264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56264 eq57266
  have eq57296 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq57279
       grind)
    | exact superpose eq57279 eq14
    | exact resolve eq14 eq57279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57310 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq43371
       have i₂ := eq57279
       grind)
    | exact superpose eq57279 eq43371
    | (have r₁ := eq43371
       have r₂ := eq57279
       grind)
    | exact resolve eq43371 eq57279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43371
  have eq57311 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq43373
       have i₂ := eq57279
       grind)
    | exact superpose eq57279 eq43373
    | (have r₁ := eq43373
       have r₂ := eq57279
       grind)
    | exact resolve eq43373 eq57279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43373 eq57279
  have eq57314 : x = (k x x) := by grind
  clear eq57311
  have eq57315 : x = (M.op x x) := by grind
  clear eq57310
  have eq57322 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq57296
       have i₂ := eq57315
       grind)
    | exact superpose eq57315 eq57296
    | exact resolve eq57296 eq57315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57296 eq57315
  have eq57347 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq647 x
       have i₂ := eq57314
       grind)
    | exact superpose eq57314 eq647
    | (have j0 := eq647 x
       grind)
    | exact resolve eq647 eq57314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647 eq57314
  have eq57388 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq57347
  have eq57406 : False := by grind
  exact eq57406

/-- `Equation4277`: `x ◇ (x ◇ x) = y ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_x_y_pyx_Equation4277 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law4277 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4277.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X1 X2)) := by
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq18 : ∀ X0 X1 X3 X4 : G, (M.op X0 (M.op X0 X1)) = (M.op X3 (M.op X3 X4)) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq8 x X3 X4
       have i₂ := eq8 x X0 X1
       grind)
    | (have i₁ := eq8 x X1 x
       have i₂ := eq8 X0 x x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X2)) = (M.op X3 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 X3 (M.op X3 X3)
       have i₂ := eq8 X3 X0 X1
       grind)
    | (have i₁ := eq8 X0 X1 (M.op X1 X2)
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq30 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op X2 X3)) ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq31 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq33 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq34 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq12 (τ X1) X0
       grind)
    | exact superpose eq12 eq16
    | (have j1 := eq12 (τ X1) X0
       grind)
    | exact resolve eq16 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq57 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X2 X3)) = (M.op X4 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq18 X2 X3 X4 (M.op X4 x)
       have i₂ := eq18 X4 x X0 X1
       grind)
    | (have i₁ := eq18 X2 X3 X4 (M.op X4 x)
       have i₂ := eq18 X0 X1 X4 x
       grind)
    | exact superpose eq18 eq18
    | exact resolve eq18 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    grind
  clear eq27
  have eq80 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq73 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq73
    | exact resolve eq73 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq81 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq31 (σ X0) (σ X1)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq31
    | exact resolve eq31 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (k (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq31 (τ X1) X0
       grind)
    | exact superpose eq31 eq16
    | (have j1 := eq31 (τ X1) X0
       grind)
    | exact resolve eq16 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq87 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq31 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq42 X1 X0
       have i₂ := eq12 (σ X1) X0
       grind)
    | exact superpose eq12 eq42
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq42 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq106 : ∀ X0 X1 X2 X4 X5 X6 : G, (M.op X0 (M.op X1 (M.op X1 X2))) = (M.op X4 (M.op X5 (M.op X5 X6))) := by
    intro X0 X1 X2 X4 X5 X6
    first
    | (have i₁ := eq20 X5 X6 x X4
       have i₂ := eq20 X1 X2 x X0
       grind)
    | exact superpose eq20 eq20
    | exact resolve eq20 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (k (M.op X0 (M.op X0 X0)) (M.op X1 (M.op X1 X2))) := by
    intro X0 X1 X2
    grind
  clear eq20
  have eq280 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (M.op X0 (M.op X0 X1)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq14
       have i₂ := eq30 (σ y) (σ x) X0 X1
       grind)
    | exact superpose eq30 eq14
    | (have j1 := eq30 (σ y) (σ x) x x
       grind)
    | exact resolve eq14 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq305 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (M.op X0 (M.op X0 X1)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    intro X0 X1
    first
    | (have i₁ := eq280 X0 X1
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq280
    | (have j0 := eq280 X0 X1
       grind)
    | exact resolve eq280 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280
  have eq562 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X3)) = (k (M.op X0 (M.op X0 X1)) (M.op X2 (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    grind
  have eq584 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq33 X0 X0
       have i₂ := eq12 X0 (σ X0)
       grind)
    | (have i₁ := eq33 X0 X1
       have i₂ := eq12 (M.op (σ X0) (σ X1)) X1
       grind)
    | exact superpose eq12 eq33
    | (have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq33 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq600 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
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
  have eq619 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
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
  have eq647 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq33 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1766 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq34
    | exact resolve eq34 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq1862 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1766 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq1766
    | (have j0 := eq1766 X0 X1
       grind)
    | exact resolve eq1766 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1766
  have eq1886 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq86 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq86
    | exact resolve eq86 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq1927 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1886 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq1886
    | (have j0 := eq1886 X0 X1
       grind)
    | exact resolve eq1886 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1886
  have eq2418 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq81 y x
       grind)
    | exact superpose eq81 eq14
    | (have j1 := eq81 y x
       grind)
    | exact resolve eq14 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq3113 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) ≠ (σ (M.op X0 (M.op X0 X0))) ∨ (σ (M.op X0 (M.op X0 X0))) = (M.op (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq647 (M.op X0 (M.op X0 X0))
       have i₂ := eq141 X0 X0 X0
       grind)
    | exact superpose eq141 eq647
    | (have j0 := eq647 (M.op X0 (M.op X0 X0))
       grind)
    | exact resolve eq647 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq3122 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have j0 := eq3113 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3113
  have eq3183 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq600
       have i₂ := eq1927 y x
       grind)
    | exact superpose eq1927 eq600
    | (have j1 := eq1927 y x
       grind)
    | (have r₁ := eq600
       have r₂ := eq1927 y x
       grind)
    | exact resolve eq600 eq1927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1927
  have eq3184 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq600
       have i₂ := eq1862 y x
       grind)
    | exact superpose eq1862 eq600
    | (have j1 := eq1862 (σ y) (σ x)
       grind)
    | (have r₁ := eq600
       have r₂ := eq1862 y x
       grind)
    | exact resolve eq600 eq1862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600 eq1862
  have eq3185 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq3184
  have eq3186 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (k y x) := by grind
  clear eq3183
  have eq4368 : (σ y) = (σ (k x x)) ∨ x = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq619 x x
       have i₂ := eq3185
       grind)
    | exact superpose eq3185 eq619
    | exact resolve eq619 eq3185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619
  have eq4419 : (σ y) = (σ (k x x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq4368
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq4368
    | exact resolve eq4368 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4368
  have eq4735 : x = (k (τ (σ y)) x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq80 x
       have i₂ := eq3186
       grind)
    | exact superpose eq3186 eq80
    | exact resolve eq80 eq3186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3186
  have eq4781 : x = (k y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq4735
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq4735
    | exact resolve eq4735 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4735
  have eq4782 : x = (k y x) := by grind
  clear eq4781
  have eq4792 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (σ (k (τ X0) (τ X0))) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq584 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq584
    | (have j0 := eq584 X1 (τ X0)
       grind)
    | exact resolve eq584 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584
  have eq4909 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4792 X0 X1
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq4792
    | (have j0 := eq4792 X0 X1
       grind)
    | exact resolve eq4792 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq4792
  have eq4919 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4909 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4909
    | (have j0 := eq4909 X0 X1
       grind)
    | exact resolve eq4909 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4909
  have eq6838 : ∀ X0 X1 X2 : G, (σ (M.op x y)) ≠ (M.op X0 (M.op X1 (M.op X1 X2))) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq305 x (M.op x x)
       have i₂ := eq106 x x x X0 X1 X2
       grind)
    | (have i₁ := eq305 x (M.op x x)
       have i₂ := eq106 X0 X1 X2 x x x
       grind)
    | exact superpose eq106 eq305
    | exact resolve eq305 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq305
  have eq6858 : ∀ X0 X1 X2 : G, (σ (M.op x y)) ≠ (M.op X0 (M.op X1 (M.op X1 X2))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6838 X0 X1 X2
       have i₂ := eq4782
       grind)
    | exact superpose eq4782 eq6838
    | (have j0 := eq6838 X0 X1 X2
       grind)
    | exact resolve eq6838 eq4782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4782 eq6838
  have eq25638 : (k x x) = (τ (σ y)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq4419
       grind)
    | exact superpose eq4419 eq9
    | exact resolve eq9 eq4419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4419
  have eq25740 : y = (k x x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq25638
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq25638
    | exact resolve eq25638 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25638
  have eq25987 : y = (M.op x x) ∨ x = y ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq31 x x
       have i₂ := eq25740
       grind)
    | exact superpose eq25740 eq31
    | exact resolve eq31 eq25740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq25740
  have eq26001 : y = (M.op x x) ∨ x = y := by grind
  clear eq25987
  have eq26356 : ∀ X0 X1 : G, (k (τ (σ X0)) X1) = X1 ∨ (k X0 (τ (σ X1))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq80 X1
       have i₂ := eq95 (σ X1) X0
       grind)
    | exact superpose eq95 eq80
    | (have j1 := eq95 (σ X1) X0
       grind)
    | exact resolve eq80 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq95
  have eq26601 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (k X0 (τ (σ X1))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq26356 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq26356
    | (have j0 := eq26356 X0 X1
       grind)
    | exact resolve eq26356 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26356
  have eq26692 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X1) (σ X0))) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq26601 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq26601
    | (have j0 := eq26601 X0 X1
       grind)
    | exact resolve eq26601 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26601
  have eq26720 : ∀ X0 X1 : G, (M.op x y) = (M.op X0 (M.op X0 X1)) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1 x x
       have i₂ := eq26001
       grind)
    | exact superpose eq26001 eq18
    | exact resolve eq18 eq26001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26723 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op x y)) ∨ x = y := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57 x x X0 X1 X2
       have i₂ := eq26001
       grind)
    | exact superpose eq26001 eq57
    | exact resolve eq57 eq26001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq26001
  have eq26900 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ x = y ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq26720 X0 (M.op X0 x)
       have i₂ := eq26720 X0 x
       grind)
    | exact superpose eq26720 eq26720
    | exact resolve eq26720 eq26720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27135 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq26900 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26900
  have eq28344 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq2418
       have i₂ := eq4919 x y
       grind)
    | exact superpose eq4919 eq2418
    | (have j1 := eq4919 x y
       grind)
    | (have r₁ := eq2418
       have r₂ := eq4919 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq2418
       have r₂ := eq4919 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq2418 eq4919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2418 eq4919
  have eq28353 : (σ (M.op x y)) = (σ x) ∨ y = (k x x) ∨ x = y := by grind
  clear eq28344
  have eq32422 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X0 X1))) ≠ (σ (M.op X0 (M.op X0 X1))) ∨ (σ (M.op X0 (M.op X0 X1))) = (M.op (σ (M.op X0 (M.op X0 X1))) (σ (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq647 (M.op X0 (M.op X0 X1))
       have i₂ := eq562 X0 X1 X0 X1
       grind)
    | exact superpose eq562 eq647
    | (have j0 := eq647 (M.op X0 (M.op X0 X1))
       grind)
    | exact resolve eq647 eq562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq32469 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X0 X1))) = (M.op (σ (M.op X0 (M.op X0 X1))) (σ (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have j0 := eq32422 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32422
  have eq33236 : ∀ X0 X1 : G, (M.op x y) = (M.op X1 (M.op X0 (M.op x y))) ∨ x = y ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq26720 X1 (M.op X1 x)
       have i₂ := eq26723 X1 x X0
       grind)
    | (have i₁ := eq26720 x (M.op x y)
       have i₂ := eq26723 X0 X1 x
       grind)
    | exact superpose eq26723 eq26720
    | exact resolve eq26720 eq26723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26723
  have eq33370 : ∀ X0 X1 : G, (M.op x y) = (M.op X1 (M.op X0 (M.op x y))) ∨ x = y := by
    intro X0 X1
    first
    | (have j0 := eq33236 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33236
  have eq36194 : (k x x) = (τ (σ y)) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq26692 x x
       have i₂ := eq3185
       grind)
    | exact superpose eq3185 eq26692
    | (have j0 := eq26692 x x
       grind)
    | exact resolve eq26692 eq3185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3185 eq26692
  have eq36280 : y = (k x x) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq36194
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq36194
    | exact resolve eq36194 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36194
  have eq51692 : y = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq36280
       have i₂ := eq12 x x
       grind)
    | exact superpose eq12 eq36280
    | (have j1 := eq12 y x
       grind)
    | exact resolve eq36280 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36280
  have eq51752 : y = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq51692
  have eq52327 : x ≠ y ∨ x = (k x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq87 x x
       have i₂ := eq51752
       grind)
    | exact superpose eq51752 eq87
    | (have j0 := eq87 x x
       grind)
    | (have r₁ := eq87 x x
       have r₂ := eq51752
       grind)
    | exact resolve eq87 eq51752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52372 : x ≠ y ∨ x = (M.op x x) := by grind
  clear eq51752
  have eq52374 : x ≠ y ∨ x = (k x x) := by
    first
    | (have j1 := eq87 x x
       grind)
    | (have r₁ := eq52327
       have r₂ := eq87 x x
       grind)
    | exact resolve eq52327 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq52327
  have eq66149 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (M.op (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X1 X2 (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0)))
       have i₂ := eq3122 X0
       grind)
    | exact superpose eq3122 eq18
    | exact resolve eq18 eq3122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq66225 : ∀ X0 : G, (M.op x y) = (M.op (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0)))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq26720 (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0)))
       have i₂ := eq3122 X0
       grind)
    | exact superpose eq3122 eq26720
    | exact resolve eq26720 eq3122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66246 : ∀ X0 : G, (M.op x y) = (σ (M.op X0 (M.op X0 X0))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq66225 X0
       have i₂ := eq3122 X0
       grind)
    | exact superpose eq3122 eq66225
    | exact resolve eq66225 eq3122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3122 eq66225
  have eq66322 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq66149 X0 X1 X2
       have i₂ := eq32469 X0 X0
       grind)
    | exact superpose eq32469 eq66149
    | exact resolve eq66149 eq32469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32469 eq66149
  have eq66765 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op X0 (M.op X0 X1)) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq66322 (M.op x y) X0 X1
       have i₂ := eq33370 (M.op x y) (M.op x y)
       grind)
    | exact superpose eq33370 eq66322
    | exact resolve eq66322 eq33370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66322
  have eq94045 : (M.op x y) = (σ (M.op x y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq66246 (M.op x y)
       have i₂ := eq33370 (M.op x y) (M.op x y)
       grind)
    | exact superpose eq33370 eq66246
    | exact resolve eq66246 eq33370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33370 eq66246
  have eq94259 : (M.op x y) = (σ (M.op x y)) ∨ x = y := by grind
  clear eq94045
  have eq99110 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq6858 x x x
       have i₂ := eq66765 x (M.op x x)
       grind)
    | exact superpose eq66765 eq6858
    | (have r₁ := eq6858 x x x
       have r₂ := eq66765 x (M.op x x)
       grind)
    | exact resolve eq6858 eq66765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6858 eq66765
  have eq99293 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq99110
  have eq100846 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq99293
       grind)
    | exact superpose eq99293 eq14
    | exact resolve eq14 eq99293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100964 : (M.op x y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq26720 (σ x) (σ y)
       have i₂ := eq99293
       grind)
    | exact superpose eq99293 eq26720
    | exact resolve eq26720 eq99293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26720
  have eq100992 : (M.op x y) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq100964
  have eq102381 : (M.op x y) ≠ (σ x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq100846
       have i₂ := eq94259
       grind)
    | exact superpose eq94259 eq100846
    | exact resolve eq100846 eq94259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94259
  have eq102382 : (σ x) ≠ (σ x) ∨ x = y ∨ y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq100846
       have i₂ := eq28353
       grind)
    | exact superpose eq28353 eq100846
    | (have r₁ := eq100846
       have r₂ := eq28353
       grind)
    | exact resolve eq100846 eq28353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28353 eq100846
  have eq102391 : (σ x) ≠ (σ x) ∨ x = y ∨ y = (k x x) := by grind
  clear eq102382
  have eq102392 : y = (k x x) ∨ x = y := by grind
  clear eq102391
  have eq102393 : (M.op x y) ≠ (σ x) ∨ x = y := by grind
  clear eq102381
  have eq108058 : (M.op x y) = (σ (k x x)) ∨ (M.op x y) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq33 x x
       have i₂ := eq100992
       grind)
    | exact superpose eq100992 eq33
    | exact resolve eq33 eq100992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq100992
  have eq108263 : (M.op x y) = (σ (k x x)) ∨ x = y := by
    first
    | (have r₁ := eq108058
       have r₂ := eq102393
       grind)
    | exact resolve eq108058 eq102393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108058
  have eq111107 : (M.op x y) = (σ y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq108263
       have i₂ := eq102392
       grind)
    | exact superpose eq102392 eq108263
    | exact resolve eq108263 eq102392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102392 eq108263
  have eq111285 : (M.op x y) = (σ y) ∨ x = y := by grind
  clear eq111107
  have eq112062 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = y ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq27135 X0
       have i₂ := eq111285
       grind)
    | exact superpose eq111285 eq27135
    | exact resolve eq27135 eq111285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27135
  have eq112073 : (σ x) ≠ (σ y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq102393
       have i₂ := eq111285
       grind)
    | exact superpose eq111285 eq102393
    | exact resolve eq102393 eq111285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102393 eq111285
  have eq112167 : (σ x) ≠ (σ y) ∨ x = y := by grind
  clear eq112073
  have eq112176 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq112062 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112062
  have eq126072 : (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq99293
       have i₂ := eq112176 (σ x)
       grind)
    | exact superpose eq112176 eq99293
    | exact resolve eq99293 eq112176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99293 eq112176
  have eq126085 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq126072
  have eq126101 : x = y := by
    first
    | (have r₁ := eq126085
       have r₂ := eq112167
       grind)
    | exact resolve eq126085 eq112167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112167 eq126085
  have eq126748 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq126101
       grind)
    | exact superpose eq126101 eq14
    | exact resolve eq14 eq126101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126761 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq52372
       have i₂ := eq126101
       grind)
    | exact superpose eq126101 eq52372
    | (have r₁ := eq52372
       have r₂ := eq126101
       grind)
    | exact resolve eq52372 eq126101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52372
  have eq126762 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq52374
       have i₂ := eq126101
       grind)
    | exact superpose eq126101 eq52374
    | (have r₁ := eq52374
       have r₂ := eq126101
       grind)
    | exact resolve eq52374 eq126101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52374 eq126101
  have eq126765 : x = (k x x) := by grind
  clear eq126762
  have eq126766 : x = (M.op x x) := by grind
  clear eq126761
  have eq126772 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq126748
       have i₂ := eq126766
       grind)
    | exact superpose eq126766 eq126748
    | exact resolve eq126748 eq126766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126748 eq126766
  have eq127922 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq647 x
       have i₂ := eq126765
       grind)
    | exact superpose eq126765 eq647
    | (have j0 := eq647 x
       grind)
    | exact resolve eq647 eq126765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647 eq126765
  have eq127965 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq127922
  have eq127984 : False := by grind
  exact eq127984
