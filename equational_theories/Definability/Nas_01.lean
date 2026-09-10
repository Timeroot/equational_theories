import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1740`: `x = (y ◇ y) ◇ ((z ◇ x) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,X) else if m(X,X) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxx_y_pxx_y_pxy_Equation1740 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1740 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1740.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X2 X0) X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
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
  have eq31 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq37 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 y X0
       grind)
    | exact resolve eq10 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10
    | exact resolve eq10 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 X0 y
       grind)
    | exact resolve eq10 eq25
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
  have eq47 : (σ (k x (k x x))) = (k (σ x) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq36 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq36
    | exact resolve eq36 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, y = (M.op (M.op X0 X0) (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y X0 x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X2) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X2 X0) X2) X1 (M.op (M.op X2 X0) X2)
       have i₂ := eq14 X0 (M.op (M.op X2 X0) X2) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq77 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ x) (σ X0)
       grind)
    | exact resolve eq11 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq78 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ y) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | exact superpose eq37 eq11
    | (have j0 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq11 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq83 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
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
  have eq91 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq83
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq83
    | exact resolve eq83 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq93 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq91
    | exact resolve eq91 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq94 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq93
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq93
    | exact resolve eq93 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq106 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq16
    | exact resolve eq16 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    grind
  have eq131 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ X0) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ X0) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq11 sF1 (σ X0)
       grind)
    | exact superpose eq11 eq38
    | (have j1 := eq11 (σ (M.op x y)) (σ X0)
       grind)
    | exact resolve eq38 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq188 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ X0)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq11 (σ X0) sF3
       grind)
    | exact superpose eq11 eq41
    | (have j1 := eq11 (σ X0) (σ y)
       grind)
    | exact resolve eq41 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq334 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 (τ X1))
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq16
    | exact resolve eq16 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq409 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) (M.op (M.op X2 X0) X2)) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq54 (M.op (M.op X2 X0) X2) X3 (M.op X1 X1)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq411 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op (M.op (σ x) (σ y)) (σ x))) = (M.op (σ y) (M.op X0 X0)) := by
    intro X0 X1
    first
    | exact superpose eq52 eq54
    | exact resolve eq54 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq414 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) X2) = (M.op (M.op (M.op X0 X0) X1) (M.op X2 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq54 X2 X3 (M.op X2 X1)
       have i₂ := eq54 X1 X0 X2
       grind)
    | (have i₁ := eq54 X0 X1 (M.op X1 X1)
       have i₂ := eq54 X0 X1 X2
       grind)
    | exact superpose eq54 eq54
    | exact resolve eq54 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq423 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X2 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X1 x X0
       have i₂ := eq54 X1 x X2
       grind)
    | (have i₁ := eq54 X0 X0 X2
       have i₂ := eq54 X0 X1 X0
       grind)
    | exact superpose eq54 eq54
    | exact resolve eq54 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq424 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X2 X0) X2)) X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 (M.op (M.op X2 X0) X2) x X1
       have i₂ := eq14 X0 x X2
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq425 : ∀ X0 : G, y = (M.op (M.op X0 (M.op (M.op x y) x)) X0) := by
    intro X0
    first
    | exact superpose eq51 eq54
    | exact resolve eq54 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq430 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op (M.op X0 X0) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 X2 x
       have i₂ := eq54 X1 X0 x
       grind)
    | (have i₁ := eq14 X0 X1 X0
       have i₂ := eq54 X0 X0 X2
       grind)
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq454 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq52 eq411
    | exact resolve eq411 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq411
  have eq456 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq409 X0 X1 x x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq409
    | exact resolve eq409 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409
  have eq483 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 X2)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 (M.op X2 X2) X0 X1
       have i₂ := eq456 (M.op X0 X0) X2
       grind)
    | exact superpose eq456 eq54
    | exact resolve eq54 eq456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq484 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq483 X1 X0 x
       have i₂ := eq456 X0 x
       grind)
    | exact superpose eq456 eq483
    | exact resolve eq483 eq456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483
  have eq502 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq114 X1
       have i₂ := eq484 X0 X1
       grind)
    | (have i₁ := eq114 X0
       have i₂ := eq484 X0 X1
       grind)
    | exact superpose eq484 eq114
    | exact resolve eq114 eq484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq685 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq76 X0 X1
       grind)
    | exact superpose eq76 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq76 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq76 X1 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq76 X0 X1
       grind)
    | exact resolve eq13 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq687 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq76 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq688 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq76 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq689 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq687 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687
  have eq704 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq685 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq685 X1 X1
       have r₂ := eq13 (σ X1) (σ X1)
       grind)
    | (have r₁ := eq685 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq685 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685
  have eq714 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq704 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq704
    | (have j0 := eq704 X0 X1
       grind)
    | exact resolve eq704 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704
  have eq753 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X1 (M.op X0 X0)
       have i₂ := eq502 X0 (τ X1)
       grind)
    | exact superpose eq502 eq35
    | exact resolve eq35 eq502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq817 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq334 X1 (M.op X0 X0)
       have i₂ := eq502 X0 (σ X1)
       grind)
    | exact superpose eq502 eq334
    | exact resolve eq334 eq502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334 eq502
  have eq1212 : ∀ X0 X1 : G, y = (M.op (M.op (M.op X0 X1) X0) (M.op (M.op (M.op x y) x) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq425 (M.op (M.op sF0 x) X1)
       have i₂ := eq423 (M.op sF0 x) X1 x
       grind)
    | (have i₁ := eq425 (M.op (M.op sF0 x) X1)
       have i₂ := eq423 X0 X1 (M.op sF0 x)
       grind)
    | exact superpose eq423 eq425
    | exact resolve eq425 eq423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3406 : ∀ X0 X1 : G, y = (M.op (M.op (M.op X0 X0) (M.op x y)) (M.op (M.op X1 X1) x)) := by
    intro X0 X1
    first
    | (have i₁ := eq425 (M.op (M.op X0 X0) x)
       have i₂ := eq414 X0 x sF0 x
       grind)
    | exact superpose eq414 eq425
    | exact resolve eq425 eq414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425
  have eq3428 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) X1) ≠ (M.op X1 X3) ∨ (M.op (M.op (M.op X2 X2) X3) (M.op (M.op X2 X2) X3)) = (k (M.op (M.op X2 X2) X3) (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 (M.op (M.op X2 X2) X3) (M.op X1 X3)
       have i₂ := eq414 X2 X3 X1 X0
       grind)
    | exact superpose eq414 eq13
    | (have j0 := eq13 (M.op (M.op X2 X2) X3) (M.op X1 X3)
       grind)
    | (have r₁ := eq13 (M.op (M.op X0 X0) (M.op X3 X3)) (M.op (M.op X3 X3) (M.op X3 X3))
       have r₂ := eq414 X0 (M.op X3 X3) (M.op X3 X3) X3
       grind)
    | exact resolve eq13 eq414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3431 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X2 X2) X3)) = (M.op (M.op X4 (M.op X1 X3)) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq423 (M.op (M.op X2 X2) X3) (M.op X1 X3) X4
       have i₂ := eq414 X2 X3 X1 X0
       grind)
    | exact superpose eq414 eq423
    | exact resolve eq423 eq414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414 eq423
  have eq4124 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq689 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq689
    | (have j0 := eq689 (τ X0)
       grind)
    | exact resolve eq689 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq4135 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq4124 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq4124
    | (have j0 := eq4124 X0
       grind)
    | exact resolve eq4124 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4124
  have eq4142 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4135 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq4135
    | (have j0 := eq4135 X0
       grind)
    | exact resolve eq4135 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4135
  have eq5388 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq77 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq77
    | (have j0 := eq77 x
       grind)
    | exact resolve eq77 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq5403 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq5388
  have eq5407 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq5403
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq5403
    | exact resolve eq5403 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5403
  have eq5424 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq5407
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq5407 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5407
  have eq5429 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq5424 eq50
    | exact resolve eq50 eq5424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq5437 : ∀ X0 : G, (k x x) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq5429
       have i₂ := eq484 X0 sF2
       grind)
    | (have i₁ := eq5429
       have i₂ := eq484 sF2 x
       grind)
    | exact superpose eq484 eq5429
    | exact resolve eq5429 eq484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5439 : ∀ X0 : G, (k x x) = (k X0 (k x x)) := by
    intro X0
    first
    | exact superpose eq5429 eq817
    | exact resolve eq817 eq5429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq817
  have eq5654 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq78 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq78
    | (have j0 := eq78 y
       grind)
    | exact resolve eq78 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq5668 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq5654
  have eq5672 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq5668
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq5668
    | exact resolve eq5668 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5668
  have eq5696 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq5672
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq5672 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5672
  have eq5724 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq5696 eq106
    | exact resolve eq106 eq5696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq5732 : (k x x) = (k y y) := by
    first
    | (have i₁ := eq5724
       have i₂ := eq5437 sF3
       grind)
    | exact superpose eq5437 eq5724
    | exact resolve eq5724 eq5437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5724
  have eq5741 : (σ y) ≠ (σ (k x x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq689 y
       have i₂ := eq5732
       grind)
    | exact superpose eq5732 eq689
    | (have j0 := eq689 y
       grind)
    | exact resolve eq689 eq5732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689
  have eq5747 : y ≠ (k x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq4142 y
       have i₂ := eq5732
       grind)
    | exact superpose eq5732 eq4142
    | (have j0 := eq4142 y
       grind)
    | exact resolve eq4142 eq5732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5732
  have eq5756 : (σ y) ≠ (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq5741
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq5741
    | exact resolve eq5741 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5741
  have eq5769 : (σ y) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq5424 eq5756
    | exact resolve eq5756 eq5424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5756
  have eq5778 : (σ y) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq5769
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq5769
    | exact resolve eq5769 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5769
  have eq5787 : (σ y) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq5778
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq5778
    | exact resolve eq5778 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5778
  have eq5835 : (k x x) ≠ (k x x) ∨ (k x x) = (M.op (k x x) (k x x)) := by
    first
    | (have i₁ := eq4142 (k x x)
       have i₂ := eq5439 (k x x)
       grind)
    | exact superpose eq5439 eq4142
    | (have j0 := eq4142 (k x x)
       grind)
    | (have r₁ := eq4142 (k x x)
       have r₂ := eq5439 (k x x)
       grind)
    | exact resolve eq4142 eq5439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5439
  have eq5848 : (k x x) = (M.op (k x x) (k x x)) := by grind
  clear eq5835
  have eq5991 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq132
    | (have j0 := eq132 (M.op x y)
       grind)
    | exact resolve eq132 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq6004 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq5991
  have eq6006 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq131 eq6004
    | exact resolve eq6004 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq6004
  have eq6037 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq6006
       have r₂ := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq6006 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6006
  have eq6461 : ∀ X0 : G, (M.op X0 X0) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq5787
       have i₂ := eq484 X0 sF2
       grind)
    | (have i₁ := eq5787
       have i₂ := eq484 sF2 x
       grind)
    | exact superpose eq484 eq5787
    | exact resolve eq5787 eq484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5787
  have eq6564 : ∀ X0 X1 : G, (σ y) = (M.op (M.op X1 (M.op (σ (k X0 y)) (σ X0))) X1) ∨ (σ y) = (M.op (σ X0) (σ X0)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq188 eq424
    | (have j1 := eq188 X0
       grind)
    | exact resolve eq424 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188 eq424
  have eq7318 : ∀ X0 : G, (M.op X0 X0) = (k x x) := by
    intro X0
    first
    | (have i₁ := eq5848
       have i₂ := eq484 X0 (k x x)
       grind)
    | (have i₁ := eq5848
       have i₂ := eq484 (k x x) X0
       grind)
    | exact superpose eq484 eq5848
    | exact resolve eq5848 eq484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7320 : ∀ X0 X1 : G, (M.op (k x x) (M.op (M.op X0 X1) X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (k x x) X0
       have i₂ := eq5848
       grind)
    | exact superpose eq5848 eq14
    | exact resolve eq14 eq5848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7323 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (k x x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X1 (k x x) X0
       have i₂ := eq5848
       grind)
    | exact superpose eq5848 eq54
    | exact resolve eq54 eq5848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq7336 : (σ y) = (M.op (σ y) (k x x)) := by
    first
    | (have i₁ := eq454 (k x x)
       have i₂ := eq5848
       grind)
    | exact superpose eq5848 eq454
    | exact resolve eq454 eq5848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454
  have eq7348 : (σ y) ≠ (k x x) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq6461 (k x x)
       have i₂ := eq5848
       grind)
    | exact superpose eq5848 eq6461
    | exact resolve eq6461 eq5848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5848 eq6461
  have eq7918 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (k x x) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq688 X0 X1
       have i₂ := eq7318 (σ X0)
       grind)
    | exact superpose eq7318 eq688
    | (have j0 := eq688 X0 X1
       grind)
    | exact resolve eq688 eq7318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688
  have eq8014 : (σ y) ≠ (k (σ x) (σ y)) ∨ (σ y) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7918 x y
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq7918
    | (have j0 := eq7918 x y
       grind)
    | exact resolve eq7918 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8029 : (σ y) ≠ (k (σ y) (σ y)) ∨ (σ y) = (k x x) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq7918 y y
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq7918
    | (have j0 := eq7918 y y
       grind)
    | exact resolve eq7918 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq7918
  have eq8072 : (σ y) ≠ (M.op (σ y) (σ y)) ∨ (σ y) = (k x x) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq5696 eq8029
    | exact resolve eq8029 eq5696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5696 eq8029
  have eq8087 : (σ y) ≠ (k (σ x) (σ y)) ∨ (σ y) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8014
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq8014
    | exact resolve eq8014 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8014
  have eq8177 : (σ y) ≠ (M.op (σ y) (σ y)) ∨ (σ y) = (k x x) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq8072
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq8072
    | exact resolve eq8072 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8072
  have eq8192 : (σ y) = (k x x) ∨ (σ y) ≠ (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8087
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq8087
    | exact resolve eq8087 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8087
  have eq8270 : (σ y) = (k x x) ∨ (σ y) ≠ (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq8177
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq8177
    | exact resolve eq8177 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8177
  have eq8285 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k x x) ∨ (σ y) ≠ (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq8192
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq8192
    | exact resolve eq8192 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8192
  have eq8359 : (σ y) = (k x x) ∨ (σ y) = (k x x) ∨ (σ y) ≠ (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq8270
       have i₂ := eq7318 (σ y)
       grind)
    | exact superpose eq7318 eq8270
    | exact resolve eq8270 eq7318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8270
  have eq8374 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k x x) ∨ (σ y) ≠ (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq8285
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq8285
    | exact resolve eq8285 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8285
  have eq8436 : (σ y) = (k x x) ∨ (σ y) = (k x x) ∨ (σ y) ≠ (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq8359
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq8359
    | exact resolve eq8359 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8359
  have eq8437 : (σ y) ≠ (M.op (σ y) (σ y)) ∨ (σ y) = (k x x) := by grind
  clear eq8436
  have eq8441 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k x x) ∨ (σ y) ≠ (k (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq8374
    | exact resolve eq8374 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8374
  have eq8499 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k x x) ∨ (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq714 X0 X1
       have i₂ := eq7318 (σ X0)
       grind)
    | exact superpose eq7318 eq714
    | (have j0 := eq714 X0 X1
       grind)
    | exact resolve eq714 eq7318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714
  have eq8500 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (k x x) ∨ (σ X1) = (k x x) := by
    intro X0 X1
    first
    | (have i₁ := eq8499 X0 X1
       have i₂ := eq7318 (σ X0)
       grind)
    | exact superpose eq7318 eq8499
    | (have j0 := eq8499 X0 X1
       grind)
    | exact resolve eq8499 eq7318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8499
  have eq8597 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (k x x) = (σ (M.op X0 X0)) ∨ (k x x) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq8500 X0 (M.op X0 X0)
       have i₂ := eq114 X0
       grind)
    | exact superpose eq114 eq8500
    | (have j0 := eq8500 X0 (M.op X0 X0)
       grind)
    | exact resolve eq8500 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8500
  have eq8741 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (k x x) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq8597 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8597
  have eq8742 : ∀ X0 : G, (k x x) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq8741 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8741
  have eq12947 : ∀ X0 : G, (M.op X0 X0) ≠ (σ y) ∨ (σ y) = (k x x) := by
    intro X0
    first
    | (have i₁ := eq8437
       have i₂ := eq484 X0 sF3
       grind)
    | (have i₁ := eq8437
       have i₂ := eq484 sF3 x
       grind)
    | exact superpose eq484 eq8437
    | exact resolve eq8437 eq484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8437
  have eq17692 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq94 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17693 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq17692
    | exact resolve eq17692 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17692
  have eq17698 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq17693
       have r₂ := eq28
       grind)
    | exact resolve eq17693 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17693
  have eq17700 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq17698
    | exact resolve eq17698 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17698
  have eq17702 : ∀ X0 : G, y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq17700
       have i₂ := eq484 X0 sF2
       grind)
    | (have i₁ := eq17700
       have i₂ := eq484 sF2 x
       grind)
    | exact superpose eq484 eq17700
    | exact resolve eq17700 eq484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484 eq17700
  have eq18014 : ∀ X0 : G, (σ y) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq8742 x
       have i₂ := eq17702 X0
       grind)
    | exact superpose eq17702 eq8742
    | (have j1 := eq17702 X0
       grind)
    | exact resolve eq8742 eq17702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17702
  have eq18038 : ∀ X0 : G, (σ y) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq18014 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq18014
    | (have j0 := eq18014 X0
       grind)
    | exact resolve eq18014 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18014
  have eq18044 : (σ y) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq18038 x
       have r₂ := eq12947 x
       grind)
    | exact resolve eq18038 eq12947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12947 eq18038
  have eq18045 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq18044
       have r₂ := eq7348
       grind)
    | exact resolve eq18044 eq7348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18044
  have eq18080 : (τ (σ y)) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18045 eq5437
    | exact resolve eq5437 eq18045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18045
  have eq18135 : y = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq18080
    | exact resolve eq18080 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18080
  have eq18941 : (σ (k x y)) = (k (σ x) (k (σ x) (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq47
       have i₂ := eq18135
       grind)
    | exact superpose eq18135 eq47
    | exact resolve eq47 eq18135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq18135
  have eq19005 : (σ (k x y)) = (k (σ x) (M.op (σ x) (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5424 eq18941
    | exact resolve eq18941 eq5424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18941
  have eq19023 : (σ (k x y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19005
       have i₂ := eq114 sF2
       grind)
    | exact superpose eq114 eq19005
    | exact resolve eq19005 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq19005
  have eq19040 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19023
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq19023
    | exact resolve eq19023 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq19023
  have eq19049 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq19040
       have r₂ := eq65
       grind)
    | exact resolve eq19040 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq19040
  have eq19239 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19049 eq94
    | exact resolve eq94 eq19049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq19242 : (k x y) = (τ (M.op (σ x) (σ x))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19049 eq58
    | exact resolve eq58 eq19049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq19049
  have eq19251 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq19239
  have eq19259 : (k x x) = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5429 eq19242
    | exact resolve eq19242 eq5429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5429 eq19242
  have eq19563 : (M.op x y) = (k x x) ∨ y = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq19259
       grind)
    | exact superpose eq19259 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq19259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19564 : (M.op x y) = (k x x) ∨ y = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19563
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq19563
    | exact resolve eq19563 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19563
  have eq19578 : y = (M.op x y) ∨ (M.op x y) = (k x x) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19564
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq19564
    | exact resolve eq19564 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19564
  have eq19579 : (M.op x y) = (k x x) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq19578
  have eq35682 : (σ y) ≠ (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq8441
       have r₂ := eq7348
       grind)
    | exact resolve eq8441 eq7348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8441
  have eq37366 : (σ y) = (M.op (σ y) (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq7336
       have i₂ := eq19579
       grind)
    | exact superpose eq19579 eq7336
    | exact resolve eq7336 eq19579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7336 eq19579
  have eq88204 : y = (M.op (M.op (σ y) (σ y)) (M.op (M.op (M.op x y) x) (M.op x y))) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq37366 eq1212
    | exact resolve eq1212 eq37366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1212 eq37366
  have eq88239 : y = (M.op x x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq88204
       have i₂ := eq14 x sF3 sF0
       grind)
    | exact superpose eq14 eq88204
    | exact resolve eq88204 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88204
  have eq88281 : ∀ X0 : G, (M.op X0 y) = X0 ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq456 X0 x
       have i₂ := eq88239
       grind)
    | exact superpose eq88239 eq456
    | exact resolve eq456 eq88239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88338 : (σ y) = (k x x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq8742 x
       have i₂ := eq88239
       grind)
    | exact superpose eq88239 eq8742
    | exact resolve eq8742 eq88239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8742 eq88239
  have eq88416 : (σ y) = (k x x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq88338
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq88338
    | exact resolve eq88338 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88338
  have eq88425 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq88416
       have r₂ := eq7348
       grind)
    | exact resolve eq88416 eq7348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88416
  have eq89239 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq88281 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq88281
    | (have j0 := eq88281 x
       grind)
    | exact resolve eq88281 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88281
  have eq89629 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq89239 eq21
    | exact resolve eq21 eq89239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89239
  have eq89780 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq89629
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq89629
    | exact resolve eq89629 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89629
  have eq90667 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq88425 eq456
    | exact resolve eq456 eq88425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88425
  have eq94434 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq90667
    | (have j0 := eq90667 (σ x)
       grind)
    | exact resolve eq90667 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90667
  have eq94872 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq94434 eq28
    | exact resolve eq28 eq94434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94434
  have eq279181 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X2 X2) X3)) = (M.op (k x x) (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3431 X0 X1 X2 X3 x
       have i₂ := eq7323 x (M.op X1 X3)
       grind)
    | exact superpose eq7323 eq3431
    | exact resolve eq3431 eq7323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3431
  have eq622325 : ∀ X0 : G, (σ y) = (M.op (k x x) (M.op (σ (k X0 y)) (σ X0))) ∨ (σ y) = (M.op (σ X0) (σ X0)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq6564 X0 x
       have i₂ := eq7323 x (M.op (σ (k X0 y)) (σ X0))
       grind)
    | exact superpose eq7323 eq6564
    | (have j0 := eq6564 X0 x
       grind)
    | exact resolve eq6564 eq7323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6564 eq7323
  have eq622326 : ∀ X0 : G, (σ y) = (k x x) ∨ (σ y) = (M.op (k x x) (M.op (σ (k X0 y)) (σ X0))) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq622325 X0
       have i₂ := eq7318 (σ X0)
       grind)
    | exact superpose eq7318 eq622325
    | (have j0 := eq622325 X0
       grind)
    | exact resolve eq622325 eq7318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7318 eq622325
  have eq622327 : ∀ X0 : G, (σ y) = (M.op (k x x) (M.op (σ (k X0 y)) (σ X0))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have j0 := eq622326 X0
       grind)
    | (have r₁ := eq622326 X0
       have r₂ := eq7348
       grind)
    | exact resolve eq622326 eq7348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7348 eq622326
  have eq819039 : ∀ X0 X1 X2 X3 : G, (k (M.op (M.op X2 X2) X3) (M.op X1 X3)) = (M.op (k x x) (M.op X3 X3)) ∨ (M.op (M.op X0 X0) X1) ≠ (M.op X1 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3428 X0 X1 X2 X3
       have i₂ := eq279181 X2 X3 X2 X3
       grind)
    | exact superpose eq279181 eq3428
    | (have j0 := eq3428 X0 X1 X2 X3
       grind)
    | exact resolve eq3428 eq279181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3428 eq279181
  have eq819040 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) X1) ≠ (M.op X1 X3) ∨ (k x x) = (k (M.op (M.op X2 X2) X3) (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq819039 X0 X1 X2 X3
       have i₂ := eq456 (k x x) X3
       grind)
    | exact superpose eq456 eq819039
    | (have j0 := eq819039 X0 X1 X2 X3
       grind)
    | (have r₁ := eq819039 (M.op X1 X1) (M.op X1 X1) X2 (M.op X1 X1)
       have r₂ := eq456 (M.op (M.op X1 X1) (M.op X1 X1)) X1
       grind)
    | exact resolve eq819039 eq456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq819039
  have eq819816 : ∀ X0 X1 X2 X3 : G, y ≠ (M.op (M.op X0 X0) (M.op (M.op X1 X1) (M.op x y))) ∨ (k x x) = (k (M.op (M.op X3 X3) (M.op (M.op X2 X2) x)) y) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq3406 eq819040
    | exact resolve eq819040 eq3406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3406 eq819040
  have eq820060 : ∀ X2 X3 : G, y ≠ (M.op x y) ∨ (k x x) = (k (M.op (M.op X3 X3) (M.op (M.op X2 X2) x)) y) := by
    intro X2 X3
    first
    | (have i₁ := eq819816 X2 x X2 X3
       have i₂ := eq430 x sF0 X2
       grind)
    | exact superpose eq430 eq819816
    | (have j0 := eq819816 x x X2 X3
       grind)
    | exact resolve eq819816 eq430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq819816
  have eq820350 : (k x x) = (k x y) ∨ y ≠ (M.op x y) := by
    first
    | (have i₁ := eq820060 x x
       have i₂ := eq430 x x x
       grind)
    | exact superpose eq430 eq820060
    | exact resolve eq820060 eq430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430 eq820060
  have eq820457 : (k x x) = (k x y) := by
    first
    | (have r₁ := eq820350
       have r₂ := eq19259
       grind)
    | exact resolve eq820350 eq19259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19259 eq820350
  have eq820660 : (σ y) = (M.op (k x x) (M.op (σ (k x x)) (σ x))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq622327 x
       have i₂ := eq820457
       grind)
    | exact superpose eq820457 eq622327
    | (have j0 := eq622327 y
       grind)
    | exact resolve eq622327 eq820457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622327 eq820457
  have eq820708 : (σ y) = (M.op (k x x) (M.op (σ (k x x)) (σ x))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq820660
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq820660
    | exact resolve eq820660 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq820660
  have eq820784 : (σ y) = (M.op (k x x) (M.op (k (σ x) (σ x)) (σ x))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq820708
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq820708
    | exact resolve eq820708 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq820708
  have eq820835 : (σ y) = (M.op (k x x) (M.op (M.op (σ x) (σ x)) (σ x))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5424 eq820784
    | exact resolve eq820784 eq5424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5424 eq820784
  have eq820869 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq820835
       have i₂ := eq7320 sF2 sF2
       grind)
    | exact superpose eq7320 eq820835
    | exact resolve eq820835 eq7320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7320 eq820835
  have eq820891 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq820869
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq820869
    | exact resolve eq820869 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq820869
  have eq820908 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq820891
    | exact resolve eq820891 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq820891
  have eq821358 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq820908 eq5437
    | exact resolve eq5437 eq820908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5437 eq820908
  have eq821674 : y = (k x x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq821358
    | exact resolve eq821358 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq821358
  have eq843294 : y ≠ y ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5747
       have i₂ := eq821674
       grind)
    | exact superpose eq821674 eq5747
    | (have r₁ := eq5747
       have r₂ := eq821674
       grind)
    | exact resolve eq5747 eq821674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5747 eq821674
  have eq843549 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq843294
  have eq858190 : ∀ X0 : G, (M.op X0 y) = X0 ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq456 X0 y
       have i₂ := eq843549
       grind)
    | exact superpose eq843549 eq456
    | exact resolve eq456 eq843549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456 eq843549
  have eq862284 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq858190 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq858190
    | (have j0 := eq858190 x
       grind)
    | exact resolve eq858190 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq858190
  have eq863378 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq862284 eq28
    | exact resolve eq28 eq862284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq862284
  have eq863457 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq89780 eq863378
    | (have r₁ := eq863378
       have r₂ := eq89780
       grind)
    | exact resolve eq863378 eq89780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89780 eq863378
  have eq863458 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq863457
  have eq863459 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq863458
  have eq863461 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq863459 eq29
    | exact resolve eq29 eq863459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq863459
  have eq863818 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq863461
    | exact resolve eq863461 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq863461
  have eq863819 : x = (M.op x y) ∨ x = y := by grind
  clear eq863818
  have eq863837 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq863819 eq21
    | exact resolve eq21 eq863819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq864479 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq863837
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq863837
    | exact resolve eq863837 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq863837
  have eq866990 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq864479 eq94872
    | (have r₁ := eq94872
       have r₂ := eq864479
       grind)
    | exact resolve eq94872 eq864479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94872 eq864479
  have eq867107 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq866990
  have eq867108 : y = (M.op x y) ∨ x = y := by grind
  clear eq867107
  have eq867408 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq867108 eq863819
    | exact resolve eq863819 eq867108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq863819 eq867108
  have eq867409 : x = y := by grind
  clear eq867408
  have eq869850 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq867409
       grind)
    | exact superpose eq867409 eq19
    | exact resolve eq19 eq867409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq869851 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq867409
       grind)
    | exact superpose eq867409 eq25
    | exact resolve eq25 eq867409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq870442 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq869851
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq869851
    | exact resolve eq869851 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869851
  have eq870537 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq870442 eq27
    | exact resolve eq27 eq870442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq874520 : ∀ X0 : G, (σ (M.op x y)) = (k X0 (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq753 x x
       have i₂ := eq869850
       grind)
    | exact superpose eq869850 eq753
    | exact resolve eq753 eq869850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq753
  have eq874958 : ∀ X0 : G, (σ (M.op x y)) = (k X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq21 eq874520
    | (have j0 := eq874520 X0
       grind)
    | exact resolve eq874520 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874520
  have eq875143 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq870537 eq19251
    | exact resolve eq19251 eq870537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19251
  have eq875659 : y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq875143
       have r₂ := eq28
       grind)
    | exact resolve eq875143 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq875143
  have eq875769 : x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq875659
       have i₂ := eq867409
       grind)
    | exact superpose eq867409 eq875659
    | exact resolve eq875659 eq867409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq875659
  have eq875833 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq875769
       have i₂ := eq869850
       grind)
    | exact superpose eq869850 eq875769
    | exact resolve eq875769 eq869850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869850 eq875769
  have eq875859 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq875833
       have i₂ := eq867409
       grind)
    | exact superpose eq867409 eq875833
    | exact resolve eq875833 eq867409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq867409 eq875833
  have eq875860 : x = (M.op x y) := by grind
  clear eq875859
  have eq875874 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq875860 eq21
    | exact resolve eq21 eq875860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq875860
  have eq876412 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq875874
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq875874
    | exact resolve eq875874 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq875874
  have eq876890 : (σ y) ≠ (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq876412 eq35682
    | exact resolve eq35682 eq876412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35682
  have eq877108 : (σ x) ≠ (k (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq870442 eq876890
    | exact resolve eq876890 eq870442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq876890
  have eq877279 : (σ (M.op x y)) ≠ (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq876412 eq877108
    | exact resolve eq877108 eq876412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq877108
  have eq877413 : (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq6037 eq877279
    | exact resolve eq877279 eq6037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6037 eq877279
  have eq877515 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq870442 eq877413
    | exact resolve eq877413 eq870442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq877413
  have eq877597 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq876412 eq877515
    | exact resolve eq877515 eq876412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq877515
  have eq877647 : (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq877597
       have r₂ := eq28
       grind)
    | exact resolve eq877597 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq877597
  have eq877681 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq870442 eq877647
    | exact resolve eq877647 eq870442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq870442 eq877647
  have eq877689 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq870537 eq877681
    | exact resolve eq877681 eq870537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq870537 eq877681
  have eq877692 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq876412 eq877689
    | exact resolve eq877689 eq876412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq876412 eq877689
  have eq877695 : (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq877692
       have r₂ := eq28
       grind)
    | exact resolve eq877692 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq877692
  have eq887088 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq874958 eq4142
    | (have j0 := eq4142 (σ (M.op x y))
       grind)
    | (have r₁ := eq4142 (σ (M.op x y))
       have r₂ := eq874958 (σ (M.op x y))
       grind)
    | exact resolve eq4142 eq874958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4142 eq874958
  have eq887475 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq887088
  have eq887744 : False := by grind
  exact eq887744

/-- `Equation1764`: `x = (y ◇ z) ◇ ((x ◇ z) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(Y,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyy_x_pyx_pyx_pxy_Equation1764 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1764 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1764.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op (M.op X0 X2) X1)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 := by
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
  have eq32 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  clear eq23
  have eq64 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) X1) X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op (M.op X0 X1) X2) X1
       have i₂ := eq9 X0 X2 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X3) X1) (M.op (M.op (M.op X1 X2) X0) X2)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq64 (M.op (M.op (M.op X1 X2) X0) X2) X1 X3
       have i₂ := eq64 X1 X2 X0
       grind)
    | exact superpose eq64 eq64
    | exact resolve eq64 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq64 (M.op X0 X1) X0 X1
       have i₂ := eq64 X0 X1 X0
       grind)
    | exact superpose eq64 eq64
    | exact resolve eq64 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X3) X0) X3) = (M.op (M.op X1 X2) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op (M.op X2 X3) X0) X3) X1 X2
       have i₂ := eq64 X2 X3 X0
       grind)
    | exact superpose eq64 eq9
    | exact resolve eq9 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X1 : G, (k (M.op X1 X1) X1) = X1 ∨ (M.op X1 X1) = (M.op X1 (M.op X1 X1)) := by
    intro X1
    grind
  have eq72 : ∀ X1 : G, (k (M.op X1 X1) X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X1
    first
    | (have i₁ := eq71 X1
       have i₂ := eq68 X1 X1
       grind)
    | exact superpose eq68 eq71
    | (have j0 := eq71 X1
       grind)
    | exact resolve eq71 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq75 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X1 X0)) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 X1 (M.op X1 X0) X2
       have i₂ := eq68 X1 X0
       grind)
    | exact superpose eq68 eq64
    | exact resolve eq64 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X0)) (M.op X0 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1 (M.op X2 X0)
       have i₂ := eq68 X2 X0
       grind)
    | exact superpose eq68 eq9
    | exact resolve eq9 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X1) = (M.op (M.op X1 X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 X1 X2 (M.op (M.op X1 X2) X0)
       have i₂ := eq68 (M.op X1 X2) X0
       grind)
    | exact superpose eq68 eq64
    | exact resolve eq64 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op X2 (M.op X1 X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq75 (M.op X1 X0) X2 (M.op (M.op X2 (M.op X1 X0)) X1)
       have i₂ := eq75 X1 (M.op X2 (M.op X1 X0)) X0
       grind)
    | exact superpose eq75 eq75
    | exact resolve eq75 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq107 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X3) X0) X3) = (M.op (M.op X1 X0) (M.op X2 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq76 X2 X1 (M.op (M.op (M.op X2 X3) X0) X3)
       have i₂ := eq64 X2 X3 X0
       grind)
    | exact superpose eq64 eq76
    | exact resolve eq76 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq122 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 X2)) = (M.op (M.op X1 (M.op X2 X3)) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X3 (M.op X0 X2)) X1 (M.op X2 X3)
       have i₂ := eq76 X2 X3 X0
       grind)
    | exact superpose eq76 eq9
    | exact resolve eq9 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq133 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op X2 X1)) = (M.op (M.op X3 X0) (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq107 X0 X3 X2 X1
       have i₂ := eq78 (M.op X2 X1) X1 X0
       grind)
    | (have i₁ := eq107 X0 X3 X2 X1
       have i₂ := eq78 X1 (M.op X2 X1) X0
       grind)
    | exact superpose eq78 eq107
    | exact resolve eq107 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq276 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq281 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq276 (σ X0)
       grind)
    | exact superpose eq276 eq15
    | exact resolve eq15 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq283 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq276 (τ X0)
       grind)
    | exact superpose eq276 eq32
    | exact resolve eq32 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq286 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq283 X0
       have i₂ := eq276 X0
       grind)
    | exact superpose eq276 eq283
    | exact resolve eq283 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283
  have eq288 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq281 X0
       have i₂ := eq276 X0
       grind)
    | exact superpose eq276 eq281
    | exact resolve eq281 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276 eq281
  have eq312 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq68 (σ X0) (σ X0)
       have i₂ := eq288 X0
       grind)
    | exact superpose eq288 eq68
    | exact resolve eq68 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq314 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = (M.op (M.op X1 (σ X0)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq78 (σ X0) X1 (σ X0)
       have i₂ := eq288 X0
       grind)
    | exact superpose eq288 eq78
    | exact resolve eq78 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq316 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op (M.op X1 (σ (M.op X0 X0))) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq89 (σ X0) (σ X0) X1
       have i₂ := eq288 X0
       grind)
    | exact superpose eq288 eq89
    | exact resolve eq89 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq318 : ∀ X0 : G, (σ X0) = (k (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq72 (σ X0)
       have i₂ := eq288 X0
       grind)
    | exact superpose eq288 eq72
    | exact resolve eq72 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq320 : ∀ X0 : G, (σ X0) = (σ (k (M.op X0 X0) X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq318 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq318
    | (have j0 := eq318 X0
       grind)
    | exact resolve eq318 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318
  have eq330 : ∀ X0 : G, (σ X0) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq12 (σ (M.op X0 X0)) (σ X0)
       have i₂ := eq312 X0
       grind)
    | exact superpose eq312 eq12
    | exact resolve eq12 eq312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq339 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq330 X0
       have i₂ := eq288 X0
       grind)
    | exact superpose eq288 eq330
    | (have j0 := eq330 X0
       grind)
    | exact resolve eq330 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330
  have eq344 : ∀ X0 : G, (σ X0) = (σ (k (M.op X0 X0) X0)) ∨ (σ X0) ≠ (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq339 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq339
    | (have j0 := eq339 X0
       grind)
    | exact resolve eq339 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339
  have eq346 : ∀ X0 : G, (σ X0) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have j0 := eq344 X0
       have j1 := eq320 X0
       grind)
    | (have r₁ := eq344 X0
       have r₂ := eq320 X0
       grind)
    | exact resolve eq344 eq320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320 eq344
  have eq350 : ∀ X0 : G, (τ (σ X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq10 (k (M.op X0 X0) X0)
       have i₂ := eq346 X0
       grind)
    | exact superpose eq346 eq10
    | exact resolve eq10 eq346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346
  have eq362 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq350 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq350
    | exact resolve eq350 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350
  have eq386 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq68 (τ X0) (τ X0)
       have i₂ := eq286 X0
       grind)
    | exact superpose eq286 eq68
    | exact resolve eq68 eq286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq388 : ∀ X0 X1 : G, (M.op (τ (M.op X0 X0)) X1) = (M.op (M.op X1 (τ X0)) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq78 (τ X0) X1 (τ X0)
       have i₂ := eq286 X0
       grind)
    | exact superpose eq286 eq78
    | exact resolve eq78 eq286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq490 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op (σ (M.op (M.op X0 X0) (M.op X0 X0))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq314 (M.op X0 X0) (σ X0)
       have i₂ := eq312 X0
       grind)
    | exact superpose eq312 eq314
    | exact resolve eq314 eq312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314
  have eq527 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op (M.op X0 X0) (M.op X0 X0))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq490 X0
       have i₂ := eq312 X0
       grind)
    | exact superpose eq312 eq490
    | exact resolve eq490 eq312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490
  have eq723 : ∀ X0 : G, (M.op (τ X0) (τ (M.op X0 X0))) = (M.op (τ (M.op (M.op X0 X0) (M.op X0 X0))) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq388 (M.op X0 X0) (τ X0)
       have i₂ := eq386 X0
       grind)
    | exact superpose eq386 eq388
    | exact resolve eq388 eq386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388
  have eq760 : ∀ X0 : G, (τ X0) = (M.op (τ (M.op (M.op X0 X0) (M.op X0 X0))) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq723 X0
       have i₂ := eq386 X0
       grind)
    | exact superpose eq386 eq723
    | exact resolve eq723 eq386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386 eq723
  have eq842 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq879 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op X2 (M.op X0 X1)) X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq89 X0 X0 X2
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq89 X0 X1 X2
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq89
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq89 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq895 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq842 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842
  have eq909 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X0 X2) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq879 X0 X1 X2
       have i₂ := eq89 X1 X0 X2
       grind)
    | exact superpose eq89 eq879
    | (have j0 := eq879 X0 X1 X2
       grind)
    | exact resolve eq879 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879
  have eq1606 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X2 X0) X3)) = (M.op X0 (M.op (M.op X3 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq89 X1 (M.op (M.op X3 X1) X2) (M.op (M.op X2 X0) X3)
       have i₂ := eq66 X2 X3 X1 X0
       grind)
    | exact superpose eq66 eq89
    | exact resolve eq89 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq2062 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X1 (M.op X4 X0))) X3) = (M.op (M.op X4 X2) (M.op X0 X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq69 (M.op X1 (M.op X4 X0)) X4 X2 X3
       have i₂ := eq89 X0 X4 X1
       grind)
    | exact superpose eq89 eq69
    | exact resolve eq69 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq2117 : ∀ X0 X1 : G, (τ X0) = (M.op (τ (M.op (M.op (M.op X0 X1) X0) X1)) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq760 X0
       have i₂ := eq69 X0 X0 X0 X1
       grind)
    | exact superpose eq69 eq760
    | exact resolve eq760 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq760
  have eq2118 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op (M.op (M.op X0 X1) X0) X1)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq527 X0
       have i₂ := eq69 X0 X0 X0 X1
       grind)
    | exact superpose eq69 eq527
    | exact resolve eq527 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq527
  have eq2187 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op (M.op X1 X0) (M.op X0 X1))) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2118 X0 X1
       have i₂ := eq78 (M.op X0 X1) X1 X0
       grind)
    | (have i₁ := eq2118 X0 X1
       have i₂ := eq78 X1 (M.op X0 X1) X0
       grind)
    | exact superpose eq78 eq2118
    | exact resolve eq2118 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2118
  have eq2188 : ∀ X0 X1 : G, (τ X0) = (M.op (τ (M.op (M.op X1 X0) (M.op X0 X1))) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2117 X0 X1
       have i₂ := eq78 (M.op X0 X1) X1 X0
       grind)
    | (have i₁ := eq2117 X0 X1
       have i₂ := eq78 X1 (M.op X0 X1) X0
       grind)
    | exact superpose eq78 eq2117
    | exact resolve eq2117 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2117
  have eq2234 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X2) (M.op X0 X1)) = (M.op (M.op X3 (M.op X1 (M.op X4 X0))) (M.op X2 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2062 X0 X1 X2 X3 X4
       have i₂ := eq78 (M.op X2 X3) X3 (M.op X1 (M.op X4 X0))
       grind)
    | (have i₁ := eq2062 X0 X1 X2 X3 X4
       have i₂ := eq78 X3 (M.op X2 X3) (M.op X1 (M.op X4 X0))
       grind)
    | exact superpose eq78 eq2062
    | exact resolve eq2062 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2062
  have eq2352 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X4 X2) (M.op X0 X1)) = (M.op (M.op X4 X0) (M.op X2 X1)) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq2234 X0 X1 X2 x X4
       have i₂ := eq122 X2 x X1 (M.op X4 X0)
       grind)
    | exact superpose eq122 eq2234
    | exact resolve eq2234 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq2234
  have eq2512 : ∀ X0 X1 : G, (M.op (σ (M.op (M.op X1 (τ X0)) (M.op (τ X0) X1))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2187 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2187
    | exact resolve eq2187 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7453 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq895 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq895
  have eq7457 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq7453 X0 X1
       have j1 := eq909 X1 X0 x
       grind)
    | (have r₁ := eq7453 X0 x
       have r₂ := eq909 X0 x x
       grind)
    | (have r₁ := eq7453 X1 x
       have r₂ := eq909 x X1 x
       grind)
    | (have r₁ := eq7453 X0 X0
       have r₂ := eq909 X0 (M.op X0 X0) x
       grind)
    | exact resolve eq7453 eq909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq909 eq7453
  have eq7589 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X0)) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq312 X1
       have i₂ := eq7457 X0 X1
       grind)
    | (have i₁ := eq312 X0
       have i₂ := eq7457 (M.op X0 X0) X1
       grind)
    | exact superpose eq7457 eq312
    | (have j1 := eq7457 X0 X1
       grind)
    | exact resolve eq312 eq7457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312
  have eq7592 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq362 X1
       have i₂ := eq7457 X0 X1
       grind)
    | (have i₁ := eq362 X0
       have i₂ := eq7457 (M.op X0 X0) X1
       grind)
    | exact superpose eq7457 eq362
    | (have j1 := eq7457 X0 X1
       grind)
    | exact resolve eq362 eq7457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7602 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq68 X1 X1
       have i₂ := eq7457 X0 X1
       grind)
    | (have i₁ := eq68 X0 X1
       have i₂ := eq7457 (M.op X0 X1) X1
       grind)
    | exact superpose eq7457 eq68
    | (have j1 := eq7457 X0 X1
       grind)
    | exact resolve eq68 eq7457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7660 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = X0 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq288 X1
       have i₂ := eq7457 X0 (σ X1)
       grind)
    | (have i₁ := eq288 X0
       have i₂ := eq7457 (M.op (σ X0) (σ X0)) X1
       grind)
    | exact superpose eq7457 eq288
    | (have j1 := eq7457 X0 (σ X1)
       grind)
    | exact resolve eq288 eq7457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7754 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq7592 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7592
  have eq7797 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (k (τ (M.op (M.op X1 X0) (M.op X0 X1))) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq7754 (τ (M.op (M.op X1 X0) (M.op X0 X1))) (τ X0)
       have i₂ := eq2188 X0 X1
       grind)
    | exact superpose eq2188 eq7754
    | (have j0 := eq7754 (τ (M.op (M.op X1 X0) (M.op X0 X1))) (τ X0)
       grind)
    | (have r₁ := eq7754 (τ (M.op (M.op X1 X0) (M.op X0 X1))) (τ X0)
       have r₂ := eq2188 X0 X1
       grind)
    | exact resolve eq7754 eq2188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2188 eq7754
  have eq7800 : ∀ X0 X1 : G, (τ X0) = (k (τ (M.op (M.op X1 X0) (M.op X0 X1))) (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq7797 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7797
  have eq7803 : ∀ X0 X1 : G, (τ X0) = (τ (k (M.op (M.op X1 X0) (M.op X0 X1)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq7800 X0 X1
       have i₂ := eq32 X0 (M.op (M.op X1 X0) (M.op X0 X1))
       grind)
    | exact superpose eq32 eq7800
    | exact resolve eq7800 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7800
  have eq7913 : ∀ X0 X1 : G, (σ (τ X0)) = (k (M.op (M.op X1 X0) (M.op X0 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k (M.op (M.op X1 X0) (M.op X0 X1)) X0)
       have i₂ := eq7803 X0 X1
       grind)
    | exact superpose eq7803 eq11
    | exact resolve eq11 eq7803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7803
  have eq7956 : ∀ X0 X1 : G, (k (M.op (M.op X1 X0) (M.op X0 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7913 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7913
    | exact resolve eq7913 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7913
  have eq9156 : ∀ X0 X1 : G, (τ X0) = (M.op X1 X1) ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq7660 X0 X1
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq7660 (σ X0) X1
       grind)
    | exact superpose eq7660 eq10
    | (have j1 := eq7660 X0 X1
       grind)
    | exact resolve eq10 eq7660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7660
  have eq9259 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq68 (σ X0) (σ X1)
       have i₂ := eq7589 X1 X0
       grind)
    | exact superpose eq7589 eq68
    | (have j1 := eq7589 X1 X0
       grind)
    | exact resolve eq68 eq7589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7589
  have eq9308 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9259 X0 X1
       have i₂ := eq288 X0
       grind)
    | exact superpose eq288 eq9259
    | (have j0 := eq9259 X0 X1
       grind)
    | exact resolve eq9259 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9259
  have eq9517 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X1 X0
       have i₂ := eq9308 (τ X1) (τ X0)
       grind)
    | exact superpose eq9308 eq32
    | (have j1 := eq9308 (τ X1) (τ X0)
       grind)
    | exact resolve eq32 eq9308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq9308
  have eq9531 : ∀ X0 X1 : G, (σ (τ X0)) = (σ (τ (M.op X1 X1))) ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9517 X0 X1
       have i₂ := eq286 X1
       grind)
    | exact superpose eq286 eq9517
    | (have j0 := eq9517 X0 X1
       grind)
    | exact resolve eq9517 eq286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9517
  have eq9582 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9531 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq9531
    | (have j0 := eq9531 X0 X1
       grind)
    | exact resolve eq9531 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9531
  have eq9597 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9582 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq9582
    | (have j0 := eq9582 X0 X1
       grind)
    | exact resolve eq9582 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9582
  have eq9696 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq68 X1 X1
       have i₂ := eq9156 X0 X1
       grind)
    | exact superpose eq9156 eq68
    | (have j1 := eq9156 X0 X1
       grind)
    | exact resolve eq68 eq9156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9775 : ∀ X0 X1 : G, (M.op (σ (M.op (τ X0) (τ X0))) X1) = X1 ∨ (k X0 (σ (τ X1))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2512 X0 (τ X0)
       have i₂ := eq9156 X0 (τ X0)
       grind)
    | exact superpose eq9156 eq2512
    | (have j1 := eq9156 X0 (τ X1)
       grind)
    | exact resolve eq2512 eq9156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2512
  have eq9780 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (τ (σ X0)) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq9156 (σ X0) X1
       grind)
    | exact superpose eq9156 eq15
    | (have j1 := eq9156 (σ X0) X1
       grind)
    | exact resolve eq15 eq9156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9156
  have eq9793 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9780 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9780
    | (have j0 := eq9780 X0 X1
       grind)
    | exact resolve eq9780 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9780
  have eq9796 : ∀ X0 X1 : G, (M.op (σ (τ (M.op X0 X0))) X1) = X1 ∨ (k X0 (σ (τ X1))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9775 X0 X1
       have i₂ := eq286 X0
       grind)
    | exact superpose eq286 eq9775
    | (have j0 := eq9775 X0 X1
       grind)
    | exact resolve eq9775 eq286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286 eq9775
  have eq9856 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 ∨ (k X0 (σ (τ X1))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9796 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq9796
    | (have j0 := eq9796 X0 X1
       grind)
    | exact resolve eq9796 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9796
  have eq9869 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9856 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq9856
    | (have j0 := eq9856 X0 X1
       grind)
    | exact resolve eq9856 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9856
  have eq17799 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 (τ (σ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq9696 (σ X0) X1
       grind)
    | exact superpose eq9696 eq15
    | (have j1 := eq9696 (σ X0) X1
       grind)
    | exact resolve eq15 eq9696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9696
  have eq17811 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17799 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq17799
    | (have j0 := eq17799 X0 X1
       grind)
    | exact resolve eq17799 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17799
  have eq17858 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9793 X0 X1
       have i₂ := eq7457 X0 X1
       grind)
    | exact superpose eq7457 eq9793
    | (have j0 := eq9793 X0 X1
       have j1 := eq7457 X0 X1
       grind)
    | exact resolve eq9793 eq7457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9793
  have eq18057 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq17858 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17858
  have eq20044 : ∀ X0 X1 : G, (τ X1) = (M.op (τ X0) (τ (k X0 X1))) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq68 (τ X0) (τ X1)
       have i₂ := eq9597 X0 X1
       grind)
    | exact superpose eq9597 eq68
    | (have j1 := eq9597 X0 X1
       grind)
    | exact resolve eq68 eq9597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9597
  have eq21433 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17811 X0 X1
       have i₂ := eq7602 X0 X1
       grind)
    | exact superpose eq7602 eq17811
    | (have j0 := eq17811 X0 X1
       have j1 := eq7602 X0 X1
       grind)
    | exact resolve eq17811 eq7602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7602 eq17811
  have eq21500 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq21433 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21433
  have eq22867 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq18057 x y
       grind)
    | exact superpose eq18057 eq16
    | (have j1 := eq18057 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq18057 x y
       grind)
    | exact resolve eq16 eq18057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22912 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ (M.op X0 X1))) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq68 (σ X0) (σ X1)
       have i₂ := eq18057 X0 X1
       grind)
    | exact superpose eq18057 eq68
    | (have j1 := eq18057 X0 X1
       grind)
    | exact resolve eq68 eq18057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18057
  have eq23137 : x = (M.op y y) := by grind
  clear eq22867
  have eq23270 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (M.op X0 (σ x)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq316 y X0
       have i₂ := eq23137
       grind)
    | exact superpose eq23137 eq316
    | exact resolve eq316 eq23137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316
  have eq23300 : y = (M.op y x) := by
    first
    | (have i₁ := eq68 y y
       have i₂ := eq23137
       grind)
    | exact superpose eq23137 eq68
    | exact resolve eq68 eq23137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23305 : ∀ X0 : G, (M.op x X0) = (M.op (M.op X0 y) y) := by
    intro X0
    first
    | (have i₁ := eq78 y X0 y
       have i₂ := eq23137
       grind)
    | exact superpose eq23137 eq78
    | exact resolve eq78 eq23137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq23316 : ∀ X0 X1 : G, (M.op x (M.op X1 y)) = (M.op (M.op X0 y) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq133 y X0 X1 y
       have i₂ := eq23137
       grind)
    | exact superpose eq23137 eq133
    | exact resolve eq133 eq23137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq23331 : ∀ X0 X1 : G, (M.op X0 (M.op x X1)) = (M.op y (M.op (M.op X1 X0) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq1606 y X0 y X1
       have i₂ := eq23137
       grind)
    | exact superpose eq23137 eq1606
    | exact resolve eq1606 eq23137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1606
  have eq23356 : y = (k (M.op x x) y) := by
    first
    | (have i₁ := eq7956 y y
       have i₂ := eq23137
       grind)
    | exact superpose eq23137 eq7956
    | exact resolve eq7956 eq23137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7956
  have eq23444 : (σ x) = (M.op (σ (M.op y (M.op x y))) (σ x)) := by
    first
    | (have i₁ := eq2187 x y
       have i₂ := eq23300
       grind)
    | exact superpose eq23300 eq2187
    | exact resolve eq2187 eq23300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2187 eq23300
  have eq23496 : ∀ X0 : G, y = (k X0 y) ∨ (M.op X0 x) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq23356
       have i₂ := eq7457 X0 x
       grind)
    | (have i₁ := eq23356
       have i₂ := eq7457 (M.op x x) x
       grind)
    | exact superpose eq7457 eq23356
    | (have j1 := eq7457 X0 x
       grind)
    | exact resolve eq23356 eq7457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7457
  have eq23822 : ∀ X0 : G, (M.op y y) = (M.op x (M.op X0 X0)) ∨ (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq23305 (M.op X0 X0)
       have i₂ := eq9869 X0 y
       grind)
    | exact superpose eq9869 eq23305
    | (have j1 := eq9869 X0 y
       grind)
    | exact resolve eq23305 eq9869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9869
  have eq23989 : ∀ X0 : G, x = (M.op x (M.op X0 X0)) ∨ (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq23822 X0
       have i₂ := eq23137
       grind)
    | exact superpose eq23137 eq23822
    | (have j0 := eq23822 X0
       grind)
    | exact resolve eq23822 eq23137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23822
  have eq28294 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ (M.op y (M.op x y)))) := by
    first
    | (have i₁ := eq23270 (σ (M.op y (M.op x y)))
       have i₂ := eq23444
       grind)
    | exact superpose eq23444 eq23270
    | exact resolve eq23270 eq23444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23270 eq23444
  have eq45725 : ∀ X0 : G, (M.op X0 X0) = (M.op x x) ∨ (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq68 x (M.op X0 X0)
       have i₂ := eq23989 X0
       grind)
    | exact superpose eq23989 eq68
    | (have j1 := eq23989 X0
       grind)
    | exact resolve eq68 eq23989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23989
  have eq56439 : ∀ X0 : G, (M.op X0 (M.op x x)) = X0 ∨ (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq68 X0 X0
       have i₂ := eq45725 X0
       grind)
    | (have i₁ := eq68 x x
       have i₂ := eq45725 X0
       grind)
    | exact superpose eq45725 eq68
    | (have j1 := eq45725 X0
       grind)
    | exact resolve eq68 eq45725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45725
  have eq62996 : (M.op x y) = (M.op x (M.op x y)) ∨ (M.op (M.op x y) y) = (k (M.op x y) y) := by
    first
    | (have i₁ := eq23316 x x
       have i₂ := eq56439 (M.op x y)
       grind)
    | exact superpose eq56439 eq23316
    | (have j1 := eq56439 (M.op x y)
       grind)
    | exact resolve eq23316 eq56439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23316 eq56439
  have eq63099 : y = (M.op x y) ∨ (M.op (M.op x y) y) = (k (M.op x y) y) := by
    first
    | (have i₁ := eq62996
       have i₂ := eq68 x y
       grind)
    | exact superpose eq68 eq62996
    | exact resolve eq62996 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62996
  have eq63159 : (M.op x x) = (k (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq63099
       have i₂ := eq23305 x
       grind)
    | exact superpose eq23305 eq63099
    | exact resolve eq63099 eq23305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63099
  have eq71584 : ∀ X0 X1 : G, (τ (σ X1)) = (M.op (τ (σ X0)) (τ (σ (k X0 X1)))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq20044 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq20044
    | (have j0 := eq20044 (σ X0) (σ X1)
       grind)
    | exact resolve eq20044 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20044
  have eq72097 : ∀ X0 X1 : G, (τ (σ X1)) = (M.op (τ (σ X0)) (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq71584 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq71584
    | (have j0 := eq71584 X0 X1
       grind)
    | exact resolve eq71584 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71584
  have eq72164 : ∀ X0 X1 : G, (τ (σ X1)) = (M.op X0 (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq72097 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq72097
    | (have j0 := eq72097 X0 X1
       grind)
    | exact resolve eq72097 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72097
  have eq72184 : ∀ X0 X1 : G, (M.op X0 (k X0 X1)) = X1 ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq72164 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq72164
    | (have j0 := eq72164 X0 X1
       grind)
    | exact resolve eq72164 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72164
  have eq72193 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (M.op X0 (k X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq72184 X0 X1
       have i₂ := eq288 X1
       grind)
    | exact superpose eq288 eq72184
    | (have j0 := eq72184 X0 X1
       grind)
    | exact resolve eq72184 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72184
  have eq74267 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 X1) ∨ (M.op X0 (k X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq72193 X0 X1
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq72193 X0 X1
       grind)
    | exact superpose eq72193 eq10
    | (have j1 := eq72193 X0 X1
       grind)
    | exact resolve eq10 eq72193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72193
  have eq74465 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 (k X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq74267 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq74267
    | (have j0 := eq74267 X0 X1
       grind)
    | exact resolve eq74267 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74267
  have eq75314 : ∀ X0 : G, y = (M.op X0 (k X0 y)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq23137
       have i₂ := eq74465 X0 y
       grind)
    | (have i₁ := eq23137
       have i₂ := eq74465 (M.op y y) x
       grind)
    | exact superpose eq74465 eq23137
    | (have j1 := eq74465 X0 y
       grind)
    | exact resolve eq23137 eq74465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74465
  have eq75776 : ∀ X0 : G, (M.op y (M.op y y)) = (M.op (k X0 y) (M.op x X0)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq23331 (k X0 y) X0
       have i₂ := eq75314 X0
       grind)
    | exact superpose eq75314 eq23331
    | (have j1 := eq75314 X0
       grind)
    | exact resolve eq23331 eq75314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23331 eq75314
  have eq75845 : ∀ X0 : G, y = (M.op (k X0 y) (M.op x X0)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq75776 X0
       have i₂ := eq68 y y
       grind)
    | exact superpose eq68 eq75776
    | (have j0 := eq75776 X0
       grind)
    | exact resolve eq75776 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75776
  have eq78250 : ∀ X0 : G, y = (M.op (k (M.op x X0) y) X0) ∨ x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq75845 (M.op x X0)
       have i₂ := eq68 x X0
       grind)
    | exact superpose eq68 eq75845
    | (have j0 := eq75845 (M.op x X0)
       grind)
    | exact resolve eq75845 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75845
  have eq101140 : (M.op y y) = (M.op x (k (M.op x y) y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq23305 (k (M.op x y) y)
       have i₂ := eq78250 y
       grind)
    | exact superpose eq78250 eq23305
    | (have j1 := eq78250 y
       grind)
    | exact resolve eq23305 eq78250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78250
  have eq101175 : x = (M.op x (k (M.op x y) y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq101140
       have i₂ := eq23137
       grind)
    | exact superpose eq23137 eq101140
    | exact resolve eq101140 eq23137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101140
  have eq110062 : x = (M.op x y) ∨ x = (M.op x y) ∨ (M.op (M.op x y) x) = (k (M.op x y) x) := by
    first
    | (have i₁ := eq101175
       have i₂ := eq23496 (M.op x y)
       grind)
    | exact superpose eq23496 eq101175
    | (have j1 := eq23496 (M.op x y)
       grind)
    | exact resolve eq101175 eq23496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23496 eq101175
  have eq110207 : x = (M.op x y) ∨ (M.op (M.op x y) x) = (k (M.op x y) x) := by grind
  clear eq110062
  have eq118980 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ (M.op X0 X1))) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq68 (σ X0) (σ X1)
       have i₂ := eq21500 X0 X1
       grind)
    | exact superpose eq21500 eq68
    | (have j1 := eq21500 X0 X1
       grind)
    | exact resolve eq68 eq21500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq21500
  have eq152811 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq118980 y (M.op x y)
       have i₂ := eq28294
       grind)
    | exact superpose eq28294 eq118980
    | (have j0 := eq118980 y (M.op x y)
       grind)
    | exact resolve eq118980 eq28294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118980
  have eq152812 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq22912 y (M.op x y)
       have i₂ := eq28294
       grind)
    | exact superpose eq28294 eq22912
    | (have j0 := eq22912 y (M.op x y)
       grind)
    | exact resolve eq22912 eq28294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22912 eq28294
  have eq152849 : y = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq152812
       have r₂ := eq16
       grind)
    | exact resolve eq152812 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152812
  have eq152850 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have r₁ := eq152811
       have r₂ := eq16
       grind)
    | exact resolve eq152811 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152811
  have eq152866 : y = (M.op (M.op x x) (M.op y y)) := by
    first
    | (have i₁ := eq152849
       have i₂ := eq2352 x y y x
       grind)
    | (have i₁ := eq152849
       have i₂ := eq2352 y y x x
       grind)
    | exact superpose eq2352 eq152849
    | exact resolve eq152849 eq2352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2352 eq152849
  have eq152867 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq152850
       have i₂ := eq23305 x
       grind)
    | exact superpose eq23305 eq152850
    | exact resolve eq152850 eq23305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23305 eq152850
  have eq152878 : y = (M.op (M.op x x) x) := by
    first
    | (have i₁ := eq152866
       have i₂ := eq23137
       grind)
    | exact superpose eq23137 eq152866
    | exact resolve eq152866 eq23137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23137 eq152866
  have eq152879 : (M.op (σ x) (σ y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq152867
       grind)
    | exact superpose eq152867 eq16
    | exact resolve eq16 eq152867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153093 : y = (M.op x x) ∨ (M.op x x) = (k (M.op x y) y) := by
    first
    | (have i₁ := eq63159
       have i₂ := eq152867
       grind)
    | exact superpose eq152867 eq63159
    | exact resolve eq63159 eq152867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63159
  have eq153400 : x = (M.op x x) ∨ (M.op (M.op x y) x) = (k (M.op x y) x) := by
    first
    | (have i₁ := eq110207
       have i₂ := eq152867
       grind)
    | exact superpose eq152867 eq110207
    | exact resolve eq110207 eq152867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110207
  have eq153590 : (k (M.op x x) x) = (M.op (M.op x x) x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq153400
       have i₂ := eq152867
       grind)
    | exact superpose eq152867 eq153400
    | exact resolve eq153400 eq152867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153400
  have eq153640 : (M.op x x) = (k (M.op x x) y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq153093
       have i₂ := eq152867
       grind)
    | exact superpose eq152867 eq153093
    | exact resolve eq153093 eq152867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153093
  have eq153668 : y = (k (M.op x x) x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq153590
       have i₂ := eq152878
       grind)
    | exact superpose eq152878 eq153590
    | exact resolve eq153590 eq152878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152878 eq153590
  have eq153708 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq153640
       have i₂ := eq23356
       grind)
    | exact superpose eq23356 eq153640
    | exact resolve eq153640 eq23356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23356 eq153640
  have eq153709 : y = (M.op x x) := by grind
  clear eq153708
  have eq153727 : x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq153668
       have i₂ := eq362 x
       grind)
    | exact superpose eq362 eq153668
    | exact resolve eq153668 eq362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362 eq153668
  have eq155157 : y = (M.op x y) := by
    first
    | (have i₁ := eq152867
       have i₂ := eq153709
       grind)
    | exact superpose eq153709 eq152867
    | exact resolve eq152867 eq153709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152867
  have eq155159 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq152879
       have i₂ := eq153709
       grind)
    | exact superpose eq153709 eq152879
    | exact resolve eq152879 eq153709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152879
  have eq155564 : x = y ∨ x = y := by
    first
    | (have i₁ := eq153727
       have i₂ := eq153709
       grind)
    | exact superpose eq153709 eq153727
    | exact resolve eq153727 eq153709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153709 eq153727
  have eq155565 : x = y := by grind
  clear eq155564
  have eq170560 : x = (M.op x x) := by
    first
    | (have i₁ := eq155157
       have i₂ := eq155565
       grind)
    | exact superpose eq155565 eq155157
    | exact resolve eq155157 eq155565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155157
  have eq170561 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq155159
       have i₂ := eq155565
       grind)
    | exact superpose eq155565 eq155159
    | exact resolve eq155159 eq155565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155159 eq155565
  have eq171228 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq170561
       have i₂ := eq288 x
       grind)
    | exact superpose eq288 eq170561
    | exact resolve eq170561 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288 eq170561
  have eq177125 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq171228
       have i₂ := eq170560
       grind)
    | exact superpose eq170560 eq171228
    | exact resolve eq171228 eq170560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170560 eq171228
  have eq177126 : False := by grind
  exact eq177126

/-- `Equation1929`: `x = (y ◇ (y ◇ x)) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,Y) else if m(Y,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyy_y_pyy_pyy_pxy_Equation1929 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1929 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1929.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X1 X0)) (M.op X2 X2)) = X0 := by
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
  have eq30 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq20
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
  have eq38 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10
    | exact resolve eq10 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
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
  have eq50 : ∀ X0 : G, y = (M.op (M.op x (M.op x y)) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y x X0
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X2 X2) = (M.op (M.op (M.op X1 (M.op X1 X0)) X0) (M.op X3 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 X2) (M.op X1 (M.op X1 X0)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X0)) = (M.op X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X1 (M.op X1 X0)) (M.op X1 (M.op X1 X0)) X2
       have i₂ := eq14 X0 X1 (M.op X1 (M.op X1 X0))
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X1) (σ X1)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq82
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq82
    | exact resolve eq82 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq92 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq90
    | exact resolve eq90 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq93 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq92
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq92
    | exact resolve eq92 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq113 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
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
  have eq130 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq159 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq11 (σ X0) sF2
       grind)
    | exact superpose eq11 eq39
    | (have j1 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq39 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq205 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq11 (σ X0) sF1
       grind)
    | exact superpose eq11 eq41
    | (have j1 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq41 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq295 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 X1
       have i₂ := eq11 (τ X0) X1
       grind)
    | exact superpose eq11 eq34
    | (have j1 := eq11 X1 X1
       grind)
    | exact resolve eq34 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq298 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k (τ X0) X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq16
    | exact resolve eq16 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq321 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (M.op (τ X1) (τ X1)) ∨ (τ X1) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X1 X0
       have i₂ := eq11 X0 (τ X1)
       grind)
    | exact superpose eq11 eq38
    | (have j1 := eq11 (τ X1) (τ X1)
       grind)
    | exact resolve eq38 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq332 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq16
    | exact resolve eq16 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq333 : ∀ X0 X1 : G, (σ (k x (k X0 (τ X1)))) = (k (σ x) (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq35 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq35
    | exact resolve eq35 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq418 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X1 X0 x
       have i₂ := eq53 X1 X2 x
       grind)
    | (have i₁ := eq53 X0 X1 X0
       have i₂ := eq53 X0 X0 X2
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq419 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op X2 (M.op X2 X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 (M.op X2 (M.op X2 X0)) X1 x
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq420 : ∀ X0 : G, y = (M.op X0 (M.op X0 (M.op x (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq50 eq53
    | exact resolve eq53 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq421 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq425 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) ≠ (M.op X2 X0) ∨ (k X2 (M.op X2 X0)) = (M.op (M.op X2 X0) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op X2 X0)
       have i₂ := eq53 X0 X2 X1
       grind)
    | (have i₁ := eq13 X0 (M.op X2 X2)
       have i₂ := eq53 X0 X1 X2
       grind)
    | exact superpose eq53 eq13
    | (have j0 := eq13 X2 (M.op X2 X0)
       grind)
    | (have r₁ := eq13 (M.op X2 X2) (M.op (M.op X2 X2) (M.op X2 X2))
       have r₂ := eq53 (M.op X2 X2) (M.op X2 X2) X2
       grind)
    | exact resolve eq13 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq487 : ∀ X0 X1 X3 : G, (M.op X1 X1) = (M.op (M.op X0 X0) (M.op X3 X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq52 (M.op X0 X0) x X1 X3
       have i₂ := eq14 (M.op X0 X0) x X0
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq488 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X3) = (M.op (M.op X0 (M.op X0 (M.op X1 (M.op X1 (M.op X2 X2))))) (M.op X4 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 (M.op X2 X2) X1 X3 X4
       have i₂ := eq53 (M.op X1 (M.op X1 (M.op X2 X2))) X0 X2
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq491 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq52 x x X1 x
       have i₂ := eq52 x x X0 x
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq502 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 (M.op X0 X1)) X1) (M.op X2 X2)) ≠ X3 ∨ (M.op (M.op (M.op X0 (M.op X0 X1)) X1) (M.op X2 X2)) = (k X4 X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq113 X0 X2
       have i₂ := eq52 X0 X1 X2 X3
       grind)
    | exact superpose eq52 eq113
    | (have r₁ := eq113 X0 (M.op (M.op (M.op X1 (M.op X1 X0)) X0) (M.op X3 X3))
       have r₂ := eq52 X0 X1 (M.op (M.op (M.op X1 (M.op X1 X0)) X0) (M.op X3 X3)) X3
       grind)
    | exact resolve eq113 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq511 : ∀ X1 X2 X3 : G, (M.op X3 X3) = (M.op X1 (M.op X1 (M.op X2 X2))) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq488 x X1 X2 X3 x
       have i₂ := eq14 (M.op X1 (M.op X1 (M.op X2 X2))) x x
       grind)
    | exact superpose eq14 eq488
    | exact resolve eq488 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488
  have eq619 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op X0 X1)) X1) (M.op X2 X2)) = (σ (k X3 X3)) ∨ (M.op (M.op (M.op X0 (M.op X0 X1)) X1) (M.op X2 X2)) = (σ X3) ∨ (M.op (M.op (M.op X0 (M.op X0 X1)) X1) (M.op X2 X2)) = (σ X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq75 X0 X0
       have i₂ := eq52 X0 X1 (σ X0) X3
       grind)
    | exact superpose eq52 eq75
    | exact resolve eq75 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq623 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op X1 X2)) X2) (M.op X3 X3)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 X2 X1 (σ X0) X3
       have i₂ := eq75 X0 X0
       grind)
    | exact superpose eq75 eq52
    | (have j1 := eq75 X0 X0
       grind)
    | exact resolve eq52 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq633 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ (k X0 X1))) = (M.op (σ X1) (M.op X2 X2)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 (σ X1) (σ X0) X2
       have i₂ := eq75 X0 X1
       grind)
    | exact superpose eq75 eq53
    | (have j1 := eq75 X1 X1
       grind)
    | exact resolve eq53 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq636 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq75 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq637 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq75 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq638 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq636 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636
  have eq647 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op X1 X2)) X2) (M.op X3 X3)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq623 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623
  have eq651 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op X0 X1)) X1) (M.op X2 X2)) = (σ (k X3 X3)) ∨ (M.op (M.op (M.op X0 (M.op X0 X1)) X1) (M.op X2 X2)) = (σ X3) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq619 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619
  have eq671 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq298 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq298
    | exact resolve eq298 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq1052 : ∀ X0 : G, y = (M.op x (M.op X0 (M.op X0 (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq420 x
       have i₂ := eq418 x sF0 x
       grind)
    | (have i₁ := eq420 x
       have i₂ := eq418 X0 sF0 x
       grind)
    | exact superpose eq418 eq420
    | exact resolve eq420 eq418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420
  have eq1054 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op X0 (M.op X0 (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | (have i₁ := eq421 sF2
       have i₂ := eq418 sF2 sF4 x
       grind)
    | (have i₁ := eq421 sF2
       have i₂ := eq418 X0 sF4 sF2
       grind)
    | exact superpose eq418 eq421
    | exact resolve eq421 eq418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1446 : ∀ X0 X1 X2 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X2 (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq113 X0 X1
       have i₂ := eq487 X0 X1 x
       grind)
    | (have i₁ := eq113 X0 (M.op x x)
       have i₂ := eq487 x X1 x
       grind)
    | exact superpose eq487 eq113
    | (have r₁ := eq113 X0 (M.op (M.op X0 X0) (M.op x x))
       have r₂ := eq487 X0 (M.op (M.op X0 X0) (M.op x x)) x
       grind)
    | (have r₁ := eq113 X0 (M.op X1 X1)
       have r₂ := eq487 X1 X1 X1
       grind)
    | exact resolve eq113 eq487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq487
  have eq1471 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X2 (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1446 X0 X1 X2
       grind)
    | (have r₁ := eq1446 X0 X1 X2
       have r₂ := eq491 X0 X1
       grind)
    | (have r₁ := eq1446 X1 X0 X2
       have r₂ := eq491 X0 X1
       grind)
    | exact resolve eq1446 eq491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1446
  have eq1482 : ∀ X0 X1 X3 X4 : G, (k X0 (M.op X1 X1)) = (k X3 (M.op X4 X4)) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq1471 x X4 X3
       have i₂ := eq1471 x X1 X0
       grind)
    | exact superpose eq1471 eq1471
    | exact resolve eq1471 eq1471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1542 : ∀ X0 X1 X2 : G, (k X1 (σ (M.op X2 X2))) = (σ (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34 X1 (M.op X2 X2)
       have i₂ := eq1471 X0 X2 (τ X1)
       grind)
    | exact superpose eq1471 eq34
    | exact resolve eq34 eq1471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1543 : ∀ X0 X1 X2 : G, (k X1 (τ (M.op X2 X2))) = (τ (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq332 X1 (M.op X2 X2)
       have i₂ := eq1471 X0 X2 (σ X1)
       grind)
    | exact superpose eq1471 eq332
    | exact resolve eq332 eq1471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332
  have eq1646 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq419 X1 X1 X1
       have i₂ := eq511 X1 X1 X0
       grind)
    | exact superpose eq511 eq419
    | exact resolve eq419 eq511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419 eq511
  have eq1689 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1646 X1 X1
       have i₂ := eq418 X1 X1 X0
       grind)
    | (have i₁ := eq1646 X1 X1
       have i₂ := eq418 X0 X1 X1
       grind)
    | exact superpose eq418 eq1646
    | exact resolve eq1646 eq418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418
  have eq1696 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq421 eq1646
    | exact resolve eq1646 eq421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421
  have eq3049 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq638 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq638
    | (have j0 := eq638 (τ X0)
       grind)
    | exact resolve eq638 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq638
  have eq3057 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3049 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3049
    | (have j0 := eq3049 X0
       grind)
    | exact resolve eq3049 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3049
  have eq3063 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3057 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3057
    | (have j0 := eq3057 X0
       grind)
    | exact resolve eq3057 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3057
  have eq3338 : ∀ X0 X3 : G, (σ (M.op X0 X0)) = (σ (M.op X3 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq1542 X3 x x
       have i₂ := eq1542 X0 x x
       grind)
    | exact superpose eq1542 eq1542
    | exact resolve eq1542 eq1542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5120 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq159 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq159
    | (have j0 := eq159 x
       grind)
    | exact resolve eq159 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159
  have eq5132 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq5120
  have eq5142 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq5132
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq5132
    | exact resolve eq5132 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5132
  have eq5150 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq5142
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq5142 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5142
  have eq5157 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq5150 eq49
    | exact resolve eq49 eq5150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq5163 : ∀ X0 : G, (k x x) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq5157
       have i₂ := eq491 X0 sF2
       grind)
    | (have i₁ := eq5157
       have i₂ := eq491 sF2 x
       grind)
    | exact superpose eq491 eq5157
    | exact resolve eq5157 eq491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5157
  have eq5221 : ∀ X0 X1 : G, (k x x) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1543 x X0 X1
       have i₂ := eq5163 x
       grind)
    | exact superpose eq5163 eq1543
    | exact resolve eq1543 eq5163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5256 : ∀ X0 : G, (k x x) = (k X0 (k x x)) := by
    intro X0
    first
    | (have i₁ := eq5221 X0 x
       have i₂ := eq5163 x
       grind)
    | exact superpose eq5163 eq5221
    | exact resolve eq5221 eq5163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5221
  have eq5382 : (k x x) ≠ (k x x) ∨ (k x x) = (M.op (k x x) (k x x)) := by
    first
    | (have i₁ := eq3063 (k x x)
       have i₂ := eq5256 (k x x)
       grind)
    | exact superpose eq5256 eq3063
    | (have j0 := eq3063 (k x x)
       grind)
    | (have r₁ := eq3063 (k x x)
       have r₂ := eq5256 (k x x)
       grind)
    | exact resolve eq3063 eq5256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3063
  have eq5399 : (k x x) = (M.op (k x x) (k x x)) := by grind
  clear eq5382
  have eq5468 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq205
    | (have j0 := eq205 (M.op x y)
       grind)
    | exact resolve eq205 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq5478 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq5468
  have eq5486 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq130 eq5478
    | exact resolve eq5478 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5478
  have eq5498 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq5486
       have r₂ := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq5486 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5486
  have eq5915 : ∀ X0 : G, (k (σ x) (σ X0)) = (σ (M.op x X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | exact superpose eq28 eq295
    | (have j0 := eq295 X0 X0
       grind)
    | exact resolve eq295 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295
  have eq6019 : ∀ X0 : G, (σ (k x X0)) = (σ (M.op x X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | exact superpose eq35 eq5915
    | (have j0 := eq5915 X0
       grind)
    | exact resolve eq5915 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq5915
  have eq6159 : ∀ X0 : G, (k x x) = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq5399
       have i₂ := eq491 X0 (k x x)
       grind)
    | (have i₁ := eq5399
       have i₂ := eq491 (k x x) X0
       grind)
    | exact superpose eq491 eq5399
    | exact resolve eq5399 eq491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491
  have eq6162 : ∀ X0 X1 : G, (k x x) = (k X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5399
       have i₂ := eq1471 (k x x) X1 X0
       grind)
    | exact superpose eq1471 eq5399
    | exact resolve eq5399 eq1471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1471
  have eq6198 : ∀ X0 : G, (σ (k x x)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3338 X0 (k x x)
       have i₂ := eq5399
       grind)
    | exact superpose eq5399 eq3338
    | exact resolve eq3338 eq5399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5399
  have eq6245 : ∀ X0 : G, (k (σ x) (σ x)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq6198 X0
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq6198
    | exact resolve eq6198 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6198
  have eq6282 : ∀ X0 : G, (M.op (σ x) (σ x)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq5150 eq6245
    | exact resolve eq6245 eq5150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6245
  have eq6497 : ∀ X0 X2 : G, (M.op X2 X0) ≠ X0 ∨ (k X2 (M.op X2 X0)) = (M.op (M.op X2 X0) (M.op X2 X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq425 X0 x X2
       have i₂ := eq1646 x X0
       grind)
    | exact superpose eq1646 eq425
    | (have j0 := eq425 X0 x X2
       grind)
    | (have r₁ := eq425 (M.op X0 X0) x (M.op (M.op X0 X0) (M.op x x))
       have r₂ := eq1646 X0 (M.op (M.op X0 X0) (M.op x x))
       grind)
    | exact resolve eq425 eq1646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425
  have eq6498 : ∀ X0 X2 : G, (M.op X2 X0) ≠ X0 ∨ (k x x) = (k X2 (M.op X2 X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq6497 X0 X2
       have i₂ := eq6159 (M.op X2 X0)
       grind)
    | exact superpose eq6159 eq6497
    | (have j0 := eq6497 X0 X2
       grind)
    | (have r₁ := eq6497 (k x x) (k x x)
       have r₂ := eq6159 (k x x)
       grind)
    | exact resolve eq6497 eq6159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6497
  have eq6536 : ∀ X0 : G, y ≠ (M.op X0 (M.op X0 (M.op x y))) ∨ (k x x) = (k x y) := by
    intro X0
    first
    | exact superpose eq1052 eq6498
    | exact resolve eq6498 eq1052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6542 : ∀ X0 : G, (σ y) ≠ (M.op X0 (M.op X0 (M.op (σ x) (σ y)))) ∨ (k x x) = (k (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1054 eq6498
    | exact resolve eq6498 eq1054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1054 eq6498
  have eq6552 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k x x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq6542 x
       have i₂ := eq1689 x sF4
       grind)
    | exact superpose eq1689 eq6542
    | exact resolve eq6542 eq1689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6542
  have eq6555 : y ≠ (M.op x y) ∨ (k x x) = (k x y) := by
    first
    | (have i₁ := eq6536 x
       have i₂ := eq1689 x sF0
       grind)
    | exact superpose eq1689 eq6536
    | exact resolve eq6536 eq1689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6536
  have eq6753 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (k x x) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq637 X0 X1
       have i₂ := eq6159 (σ X1)
       grind)
    | exact superpose eq6159 eq637
    | (have j0 := eq637 X0 X1
       grind)
    | exact resolve eq637 eq6159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637
  have eq6813 : (σ (M.op x y)) ≠ (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k x x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq130 eq6753
    | (have j0 := eq6753 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq6753 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq6816 : (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k x x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq5498 eq6813
    | exact resolve eq6813 eq5498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5498 eq6813
  have eq6865 : (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k x x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq6816
    | exact resolve eq6816 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6816
  have eq6902 : (σ (M.op x y)) = (k x x) ∨ (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq6865
    | exact resolve eq6865 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6865
  have eq6938 : (σ (M.op x y)) = (k x x) ∨ (σ (M.op x y)) = (k x x) ∨ (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq6902
       have i₂ := eq6159 (σ sF0)
       grind)
    | exact superpose eq6159 eq6902
    | exact resolve eq6902 eq6159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6902
  have eq6973 : (σ (M.op x y)) = (k x x) ∨ (σ (M.op x y)) = (k x x) ∨ (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq6938
    | exact resolve eq6938 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6938
  have eq6974 : (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k x x) := by grind
  clear eq6973
  have eq7704 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X1 X2)) X2) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq647 X0 X1 X2 x
       have i₂ := eq1646 x (M.op (M.op X1 (M.op X1 X2)) X2)
       grind)
    | exact superpose eq1646 eq647
    | (have j0 := eq647 X0 X1 X2 x
       grind)
    | exact resolve eq647 eq1646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647
  have eq7705 : ∀ X0 X2 : G, (M.op X2 X2) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq7704 X0 x X2
       have i₂ := eq1689 x X2
       grind)
    | exact superpose eq1689 eq7704
    | (have j0 := eq7704 X0 x X2
       grind)
    | exact resolve eq7704 eq1689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7704
  have eq7706 : ∀ X0 X2 : G, (M.op X2 X2) = (σ (k X0 X0)) ∨ (σ X0) = (k x x) := by
    intro X0 X2
    first
    | (have i₁ := eq7705 X0 X2
       have i₂ := eq6159 (σ X0)
       grind)
    | exact superpose eq6159 eq7705
    | (have j0 := eq7705 X0 X2
       grind)
    | exact resolve eq7705 eq6159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7705
  have eq7842 : ∀ X0 X1 : G, (σ X1) ≠ (M.op X0 X0) ∨ (σ X1) = (k x x) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (k x x) := by
    intro X0 X1
    first
    | (have i₁ := eq6753 X1 X1
       have i₂ := eq7706 X1 X0
       grind)
    | exact superpose eq7706 eq6753
    | (have j0 := eq6753 X1 X1
       have j1 := eq7706 X1 x
       grind)
    | exact resolve eq6753 eq7706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6753 eq7706
  have eq7878 : ∀ X0 X1 : G, (σ X1) ≠ (M.op X0 X0) ∨ (σ X1) = (k x x) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq7842 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7842
  have eq7894 : ∀ X0 X1 : G, (σ X1) = (k x x) ∨ (σ X1) ≠ (M.op X0 X0) ∨ (σ X1) = (k x x) := by
    intro X0 X1
    first
    | (have i₁ := eq7878 X0 X1
       have i₂ := eq6159 (σ X1)
       grind)
    | exact superpose eq6159 eq7878
    | (have j0 := eq7878 X0 X1
       grind)
    | exact resolve eq7878 eq6159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7878
  have eq7895 : ∀ X0 X1 : G, (σ X1) ≠ (M.op X0 X0) ∨ (σ X1) = (k x x) := by
    intro X0 X1
    first
    | (have j0 := eq7894 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7894
  have eq8004 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k x x) = (τ X1) ∨ (τ X1) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq321 X0 X1
       have i₂ := eq6159 (τ X1)
       grind)
    | exact superpose eq6159 eq321
    | (have j0 := eq321 X0 X1
       grind)
    | exact resolve eq321 eq6159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321
  have eq8029 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (M.op X0 y)) ∨ y = (k x x) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | exact superpose eq29 eq8004
    | exact resolve eq8004 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8004
  have eq8113 : ∀ X0 : G, (σ (k X0 y)) = (σ (M.op X0 y)) ∨ y = (k x x) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | exact superpose eq40 eq8029
    | (have j0 := eq8029 X0
       grind)
    | exact resolve eq8029 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq8029
  have eq8210 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X0 X1)) X1) ≠ X3 ∨ (M.op (M.op (M.op X0 (M.op X0 X1)) X1) (M.op X2 X2)) = (k X4 X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq502 X0 X1 X2 X3 X4
       have i₂ := eq1646 X2 (M.op (M.op X0 (M.op X0 X1)) X1)
       grind)
    | exact superpose eq1646 eq502
    | (have j0 := eq502 X0 X1 X2 X3 X4
       grind)
    | (have r₁ := eq502 X0 X1 X0 (M.op (M.op X0 (M.op X0 X1)) X1) X4
       have r₂ := eq1646 X0 (M.op (M.op X0 (M.op X0 X1)) X1)
       grind)
    | (have r₁ := eq502 X0 X1 X2 (M.op (M.op (M.op (M.op X0 (M.op X0 X1)) X1) (M.op X2 X2)) (M.op X0 X0)) X4
       have r₂ := eq1646 X0 (M.op (M.op (M.op X0 (M.op X0 X1)) X1) (M.op X2 X2))
       grind)
    | exact resolve eq502 eq1646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502
  have eq8211 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X1) ≠ X3 ∨ (M.op (M.op (M.op X0 (M.op X0 X1)) X1) (M.op X2 X2)) = (k X4 X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8210 X0 X1 X2 X3 X4
       have i₂ := eq1689 X0 X1
       grind)
    | exact superpose eq1689 eq8210
    | (have j0 := eq8210 X0 X1 X2 X3 X4
       grind)
    | (have r₁ := eq8210 X0 X1 X2 (M.op X0 (M.op X0 (M.op (M.op X0 (M.op X0 X1)) X1))) X4
       have r₂ := eq1689 X0 (M.op (M.op X0 (M.op X0 X1)) X1)
       grind)
    | exact resolve eq8210 eq1689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8210
  have eq8212 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X0 (M.op X0 X1)) X1) = (k X4 X3) ∨ (M.op X1 X1) ≠ X3 := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq8211 X0 X1 x X3 X4
       have i₂ := eq1646 x (M.op (M.op X0 (M.op X0 X1)) X1)
       grind)
    | exact superpose eq1646 eq8211
    | (have j0 := eq8211 X0 X1 x X3 X4
       grind)
    | (have r₁ := eq8211 X0 (M.op X0 X0) x (M.op X0 X0) X4
       have r₂ := eq1646 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq8211 X0 X1 x (M.op (M.op X1 X1) (M.op X0 X0)) X4
       have r₂ := eq1646 X0 (M.op X1 X1)
       grind)
    | exact resolve eq8211 eq1646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8211
  have eq8213 : ∀ X1 X3 X4 : G, (M.op X1 X1) ≠ X3 ∨ (M.op X1 X1) = (k X4 X3) := by
    intro X1 X3 X4
    first
    | (have i₁ := eq8212 x X1 X3 X4
       have i₂ := eq1689 x X1
       grind)
    | exact superpose eq1689 eq8212
    | (have j0 := eq8212 x X1 X3 X4
       grind)
    | (have r₁ := eq8212 x X1 (M.op x (M.op x (M.op X1 X1))) X4
       have r₂ := eq1689 x (M.op X1 X1)
       grind)
    | exact resolve eq8212 eq1689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8212
  have eq8408 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq633 X0 X1 x
       have i₂ := eq1646 x (σ X1)
       grind)
    | exact superpose eq1646 eq633
    | (have j0 := eq633 X1 X1 x
       grind)
    | exact resolve eq633 eq1646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633
  have eq8409 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ (k X0 X1))) ∨ (σ X1) = (k x x) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8408 X0 X1
       have i₂ := eq6159 (σ X1)
       grind)
    | exact superpose eq6159 eq8408
    | (have j0 := eq8408 X0 X1
       grind)
    | exact resolve eq8408 eq6159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6159 eq8408
  have eq8783 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X0 X1)) X1) = (σ (k X3 X3)) ∨ (M.op (M.op (M.op X0 (M.op X0 X1)) X1) (M.op X2 X2)) = (σ X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq651 X0 X1 X2 X3
       have i₂ := eq1646 X2 (M.op (M.op X0 (M.op X0 X1)) X1)
       grind)
    | exact superpose eq1646 eq651
    | (have j0 := eq651 X0 X1 X2 X3
       grind)
    | exact resolve eq651 eq1646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651
  have eq8784 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (σ (k X3 X3)) ∨ (M.op (M.op (M.op X0 (M.op X0 X1)) X1) (M.op X2 X2)) = (σ X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8783 X0 X1 X2 X3
       have i₂ := eq1689 X0 X1
       grind)
    | exact superpose eq1689 eq8783
    | (have j0 := eq8783 X0 X1 X2 X3
       grind)
    | exact resolve eq8783 eq1689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8783
  have eq8785 : ∀ X0 X1 X3 : G, (M.op (M.op X0 (M.op X0 X1)) X1) = (σ X3) ∨ (M.op X1 X1) = (σ (k X3 X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq8784 X0 X1 x X3
       have i₂ := eq1646 x (M.op (M.op X0 (M.op X0 X1)) X1)
       grind)
    | exact superpose eq1646 eq8784
    | (have j0 := eq8784 X0 X1 x X3
       grind)
    | exact resolve eq8784 eq1646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8784
  have eq8786 : ∀ X1 X3 : G, (M.op X1 X1) = (σ (k X3 X3)) ∨ (M.op X1 X1) = (σ X3) := by
    intro X1 X3
    first
    | (have i₁ := eq8785 x X1 X3
       have i₂ := eq1689 x X1
       grind)
    | exact superpose eq1689 eq8785
    | (have j0 := eq8785 x X1 X3
       grind)
    | exact resolve eq8785 eq1689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8785
  have eq8936 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (σ (τ X1))) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X1 (τ X1)
       have i₂ := eq8786 X0 (τ X1)
       grind)
    | exact superpose eq8786 eq34
    | (have j1 := eq8786 X0 (τ X1)
       grind)
    | exact resolve eq34 eq8786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq8786
  have eq8990 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq8936 X0 X1
       have j1 := eq8213 X0 (σ (τ X1)) X1
       grind)
    | (have r₁ := eq8936 X1 X1
       have r₂ := eq8213 X1 (k X1 (σ (τ X1))) x
       grind)
    | (have r₁ := eq8936 X1 X1
       have r₂ := eq8213 X1 (σ (τ X1)) x
       grind)
    | exact resolve eq8936 eq8213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8213 eq8936
  have eq9094 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8990 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq8990
    | exact resolve eq8990 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8990
  have eq9179 : ∀ X0 X2 : G, (k X0 X0) = (k X2 X2) := by
    intro X0 X2
    first
    | (have i₁ := eq9094 x X2
       have i₂ := eq9094 x X0
       grind)
    | exact superpose eq9094 eq9094
    | exact resolve eq9094 eq9094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9196 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9094 X1 (τ X0)
       have i₂ := eq671 X0 X0
       grind)
    | exact superpose eq671 eq9094
    | exact resolve eq9094 eq671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671
  have eq9233 : ∀ X0 X1 X2 X3 : G, (k X1 (M.op X2 X2)) = (k X3 (k X0 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1482 X1 X2 X3 x
       have i₂ := eq9094 x X0
       grind)
    | exact superpose eq9094 eq1482
    | exact resolve eq1482 eq9094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1482
  have eq9237 : ∀ X0 X1 X2 : G, (σ (k X0 X0)) = (k X1 (σ (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1542 x X1 X2
       have i₂ := eq9094 x X0
       grind)
    | exact superpose eq9094 eq1542
    | exact resolve eq1542 eq9094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1542
  have eq9239 : ∀ X0 X1 X2 : G, (k X1 (τ (M.op X2 X2))) = (τ (k X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1543 x X1 X2
       have i₂ := eq9094 x X0
       grind)
    | exact superpose eq9094 eq1543
    | exact resolve eq1543 eq9094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1543
  have eq9240 : ∀ X0 X1 : G, (M.op X1 (k X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1646 x X1
       have i₂ := eq9094 x X0
       grind)
    | exact superpose eq9094 eq1646
    | exact resolve eq1646 eq9094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9094
  have eq9443 : ∀ X0 X1 : G, (τ (k X0 X0)) = (k X1 (k x x)) := by
    intro X0 X1
    first
    | (have i₁ := eq9239 X0 X1 x
       have i₂ := eq5163 x
       grind)
    | exact superpose eq5163 eq9239
    | exact resolve eq9239 eq5163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9239
  have eq9445 : ∀ X0 X1 : G, (σ (k X0 X0)) = (k X1 (M.op (σ x) (σ x))) := by
    intro X0 X1
    first
    | (have i₁ := eq9237 X0 X1 x
       have i₂ := eq6282 x
       grind)
    | exact superpose eq6282 eq9237
    | exact resolve eq9237 eq6282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9237
  have eq9448 : ∀ X0 X3 : G, (k x x) = (k X3 (k X0 X0)) := by
    intro X0 X3
    first
    | (have i₁ := eq9233 X0 x x X3
       have i₂ := eq6162 x x
       grind)
    | exact superpose eq6162 eq9233
    | exact resolve eq9233 eq6162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9233
  have eq9500 : ∀ X0 : G, (k x x) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq9443 X0 x
       have i₂ := eq5256 x
       grind)
    | exact superpose eq5256 eq9443
    | exact resolve eq9443 eq5256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5256 eq9443
  have eq9501 : ∀ X0 : G, (k x x) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq9445 X0 X0
       have i₂ := eq6162 X0 sF2
       grind)
    | exact superpose eq6162 eq9445
    | exact resolve eq9445 eq6162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6162 eq9445
  have eq16413 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k x x) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7895 X0 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq7895
    | (have r₁ := eq7895 X0 (τ (M.op X0 X0))
       have r₂ := eq15 (M.op X0 X0)
       grind)
    | exact resolve eq7895 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7895
  have eq17644 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq93 eq11
    | (have j0 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq11 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq17645 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq17644
    | exact resolve eq17644 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17644
  have eq17651 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq17645
       have r₂ := eq27
       grind)
    | exact resolve eq17645 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17645
  have eq17653 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq17651
    | exact resolve eq17651 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17651
  have eq17700 : (τ (σ y)) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq17653 eq5163
    | exact resolve eq5163 eq17653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5163 eq17653
  have eq17738 : y = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq17700
    | exact resolve eq17700 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17700
  have eq17774 : y = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq16413 y x
       grind)
    | (have r₁ := eq17738
       have r₂ := eq16413 y y
       grind)
    | exact resolve eq17738 eq16413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16413 eq17738
  have eq17787 : ∀ X0 : G, y = (k X0 X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq17774
       have i₂ := eq9179 x X0
       grind)
    | (have i₁ := eq17774
       have i₂ := eq9179 X0 x
       grind)
    | exact superpose eq9179 eq17774
    | exact resolve eq17774 eq9179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9179 eq17774
  have eq18301 : ∀ X0 : G, (σ (k x y)) = (k (σ x) (k (σ (τ X0)) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq333 (τ X0) X0
       have i₂ := eq17787 (τ X0)
       grind)
    | exact superpose eq17787 eq333
    | exact resolve eq333 eq17787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333 eq17787
  have eq18359 : ∀ X0 : G, (σ (k x y)) = (k (σ x) (k X0 X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq18301 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq18301
    | exact resolve eq18301 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18301
  have eq18416 : (k x x) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18359 x
       have i₂ := eq9448 x sF2
       grind)
    | exact superpose eq9448 eq18359
    | exact resolve eq18359 eq9448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9448 eq18359
  have eq18439 : (k x x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18416
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq18416
    | exact resolve eq18416 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18416
  have eq18446 : (k x x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq18439
       have r₂ := eq6552
       grind)
    | exact resolve eq18439 eq6552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6552 eq18439
  have eq18458 : (k x y) = (τ (k x x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18446 eq57
    | exact resolve eq57 eq18446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq18446
  have eq18471 : (k x x) = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18458
       have i₂ := eq9500 x
       grind)
    | exact superpose eq9500 eq18458
    | exact resolve eq18458 eq9500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9500 eq18458
  have eq18477 : (k x x) = (k x y) := by
    first
    | (have r₁ := eq18471
       have r₂ := eq6555
       grind)
    | exact resolve eq18471 eq6555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6555 eq18471
  have eq18480 : (σ (k x x)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq18477
       grind)
    | exact superpose eq18477 eq44
    | exact resolve eq44 eq18477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18488 : (σ y) = (M.op (σ x) (σ (k x x))) ∨ (σ y) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8409 x y
       have i₂ := eq18477
       grind)
    | exact superpose eq18477 eq8409
    | (have j0 := eq8409 x y
       grind)
    | exact resolve eq8409 eq18477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8409 eq18477
  have eq18494 : (σ y) = (M.op (σ x) (k (σ x) (σ x))) ∨ (σ y) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18488
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq18488
    | exact resolve eq18488 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18488
  have eq18502 : (k (σ x) (σ x)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq18480
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq18480
    | exact resolve eq18480 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq18480
  have eq18505 : (σ x) = (σ y) ∨ (σ y) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18494
       have i₂ := eq9240 sF2 (σ x)
       grind)
    | exact superpose eq9240 eq18494
    | exact resolve eq18494 eq9240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9240 eq18494
  have eq18513 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq5150 eq18502
    | exact resolve eq18502 eq5150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5150 eq18502
  have eq18515 : (σ x) = (σ y) ∨ (σ y) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18505
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq18505
    | exact resolve eq18505 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18505
  have eq18520 : (σ x) = (σ y) ∨ (σ y) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18515
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18515
    | exact resolve eq18515 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18515
  have eq18522 : (σ y) = (k x x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18520
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq18520
    | exact resolve eq18520 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18520
  have eq18524 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18522
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq18522
    | exact resolve eq18522 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18522
  have eq18526 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18524
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18524
    | exact resolve eq18524 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18524
  have eq18528 : (σ y) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq18526
    | exact resolve eq18526 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18526
  have eq24170 : ∀ X0 : G, (τ (σ y)) = (M.op X0 X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq9196 x X0
       have i₂ := eq18528
       grind)
    | exact superpose eq18528 eq9196
    | exact resolve eq9196 eq18528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18528
  have eq24203 : ∀ X0 : G, y = (M.op X0 X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq29 eq24170
    | exact resolve eq24170 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq24170
  have eq25271 : ∀ X0 : G, (M.op X0 y) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq1646 x X0
       have i₂ := eq24203 x
       grind)
    | exact superpose eq24203 eq1646
    | exact resolve eq1646 eq24203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24203
  have eq26188 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq25271 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq25271
    | (have j0 := eq25271 x
       grind)
    | exact resolve eq25271 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25271
  have eq26312 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26188 eq27
    | exact resolve eq27 eq26188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26188
  have eq205333 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq6019 y
       grind)
    | exact superpose eq6019 eq44
    | (have j1 := eq6019 y
       grind)
    | exact resolve eq44 eq6019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6019
  have eq205684 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18513 eq205333
    | exact resolve eq205333 eq18513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205333
  have eq205809 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq205684
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq205684
    | exact resolve eq205684 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205684
  have eq205853 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq205809
    | exact resolve eq205809 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205809
  have eq205869 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq205853
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq205853
    | exact resolve eq205853 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205853
  have eq208758 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq8113 x
       grind)
    | exact superpose eq8113 eq44
    | (have j1 := eq8113 x
       grind)
    | exact resolve eq44 eq8113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq8113
  have eq208984 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (k x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18513 eq208758
    | exact resolve eq208758 eq18513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18513 eq208758
  have eq209044 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (k x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq208984
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq208984
    | exact resolve eq208984 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208984
  have eq209082 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (k x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq209044
    | exact resolve eq209044 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209044
  have eq209096 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (k x x) := by
    first
    | (have i₁ := eq209082
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq209082
    | exact resolve eq209082 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209082
  have eq250741 : ∀ X0 : G, y = (M.op y y) ∨ y = (M.op x y) ∨ (M.op X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq205869 eq1646
    | exact resolve eq1646 eq205869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205869
  have eq251175 : ∀ X0 : G, y = (k x x) ∨ y = (M.op x y) ∨ (M.op X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq209096 eq1646
    | exact resolve eq1646 eq209096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209096
  have eq252117 : ∀ X0 X1 : G, (σ y) = (σ (M.op X0 X0)) ∨ y = (M.op x y) ∨ (M.op X1 (σ (M.op x y))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3338 X0 y
       have i₂ := eq250741 X1
       grind)
    | exact superpose eq250741 eq3338
    | (have j1 := eq250741 X1
       grind)
    | exact resolve eq3338 eq250741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3338 eq250741
  have eq252227 : ∀ X1 : G, (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (M.op X1 (σ (M.op x y))) = X1 := by
    intro X1
    first
    | (have i₁ := eq252117 x X1
       have i₂ := eq6282 x
       grind)
    | exact superpose eq6282 eq252117
    | (have j0 := eq252117 x X1
       grind)
    | exact resolve eq252117 eq6282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252117
  have eq252253 : ∀ X1 : G, (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (M.op X1 (σ (M.op x y))) = X1 := by
    intro X1
    first
    | (have i₁ := eq252227 X1
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq252227
    | (have j0 := eq252227 X1
       grind)
    | exact resolve eq252227 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252227
  have eq302964 : ∀ X0 : G, y = (σ y) ∨ y = (M.op x y) ∨ (M.op X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9501 x
       have i₂ := eq251175 X0
       grind)
    | exact superpose eq251175 eq9501
    | (have j1 := eq251175 X0
       grind)
    | exact resolve eq9501 eq251175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9501 eq251175
  have eq303062 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = X0 ∨ y = (M.op x y) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq302964 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq302964
    | (have j0 := eq302964 X0
       grind)
    | exact resolve eq302964 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302964
  have eq303310 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (k x x) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | exact superpose eq303062 eq6974
    | (have r₁ := eq6974
       have r₂ := eq303062 (σ (M.op x y))
       grind)
    | exact resolve eq6974 eq303062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303062
  have eq303311 : (σ (M.op x y)) = (k x x) ∨ y = (M.op x y) ∨ y = (σ y) := by grind
  clear eq303310
  have eq308259 : ∀ X0 : G, (τ (σ (M.op x y))) = (M.op X0 X0) ∨ y = (M.op x y) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq9196 x X0
       have i₂ := eq303311
       grind)
    | exact superpose eq303311 eq9196
    | exact resolve eq9196 eq303311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303311
  have eq308400 : ∀ X0 : G, (M.op x y) = (M.op X0 X0) ∨ y = (M.op x y) ∨ y = (σ y) := by
    intro X0
    first
    | exact superpose eq30 eq308259
    | exact resolve eq308259 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308259
  have eq333818 : y = (M.op x (M.op (M.op x y) (M.op x y))) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq1052 sF0
       have i₂ := eq308400 sF0
       grind)
    | exact superpose eq308400 eq1052
    | exact resolve eq1052 eq308400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308400
  have eq334031 : y = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq333818
       have i₂ := eq1646 sF0 x
       grind)
    | exact superpose eq1646 eq333818
    | exact resolve eq333818 eq1646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333818
  have eq440432 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1689 X0 x
       have i₂ := eq252253 (M.op X0 x)
       grind)
    | exact superpose eq252253 eq1689
    | (have j1 := eq252253 X0
       grind)
    | exact resolve eq1689 eq252253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1689 eq252253
  have eq440498 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = X0 ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq440432
    | (have j0 := eq440432 X0
       grind)
    | exact resolve eq440432 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440432
  have eq440745 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (k x x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq440498 eq6974
    | (have r₁ := eq6974
       have r₂ := eq440498 (σ (M.op x y))
       grind)
    | exact resolve eq6974 eq440498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6974 eq440498
  have eq440754 : (σ (M.op x y)) = (k x x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq440745
  have eq442039 : ∀ X0 : G, (τ (σ (M.op x y))) = (M.op X0 X0) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq9196 x X0
       have i₂ := eq440754
       grind)
    | exact superpose eq440754 eq9196
    | exact resolve eq9196 eq440754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9196 eq440754
  have eq442190 : ∀ X0 : G, (M.op x y) = (M.op X0 X0) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq30 eq442039
    | exact resolve eq442039 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442039
  have eq450452 : y = (M.op x (M.op (M.op x y) (M.op x y))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1052 sF0
       have i₂ := eq442190 sF0
       grind)
    | exact superpose eq442190 eq1052
    | exact resolve eq1052 eq442190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1052 eq442190
  have eq450715 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq450452
       have i₂ := eq1646 sF0 x
       grind)
    | exact superpose eq1646 eq450452
    | exact resolve eq450452 eq1646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450452
  have eq450900 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq450715 eq27
    | exact resolve eq27 eq450715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq450906 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq450715 eq1696
    | exact resolve eq1696 eq450715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1696 eq450715
  have eq466851 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq450906 eq1646
    | exact resolve eq1646 eq450906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1646 eq450906
  have eq468084 : ∀ X0 : G, (M.op X0 y) = X0 ∨ y = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq334031 eq466851
    | exact resolve eq466851 eq334031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334031 eq466851
  have eq468339 : ∀ X0 : G, (M.op X0 y) = X0 ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq468084 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468084
  have eq476625 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq468339 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq468339
    | (have j0 := eq468339 x
       grind)
    | exact resolve eq468339 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468339
  have eq476859 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq476625 eq20
    | exact resolve eq20 eq476625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476625
  have eq477187 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq476859
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq476859
    | exact resolve eq476859 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476859
  have eq478672 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq477187 eq26312
    | (have r₁ := eq26312
       have r₂ := eq477187
       grind)
    | exact resolve eq26312 eq477187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26312 eq477187
  have eq478733 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq478672
  have eq478734 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq478733
  have eq478807 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq478734 eq28
    | exact resolve eq28 eq478734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq478734
  have eq478990 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq478807
    | exact resolve eq478807 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq478807
  have eq478991 : x = (M.op x y) ∨ x = y := by grind
  clear eq478990
  have eq479006 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq478991 eq20
    | exact resolve eq20 eq478991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq479370 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq479006
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq479006
    | exact resolve eq479006 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479006
  have eq479583 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq479370 eq450900
    | (have r₁ := eq450900
       have r₂ := eq479370
       grind)
    | exact resolve eq450900 eq479370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450900 eq479370
  have eq479589 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq479583
  have eq479590 : y = (M.op x y) ∨ x = y := by grind
  clear eq479589
  have eq479824 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq479590 eq478991
    | exact resolve eq478991 eq479590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478991 eq479590
  have eq479825 : x = y := by grind
  clear eq479824
  have eq480051 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq479825
       grind)
    | exact superpose eq479825 eq18
    | exact resolve eq18 eq479825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq480052 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq479825
       grind)
    | exact superpose eq479825 eq24
    | exact resolve eq24 eq479825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq479825
  have eq480407 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq480052
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq480052
    | exact resolve eq480052 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq480052
  have eq480445 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq480407 eq26
    | exact resolve eq26 eq480407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq480407
  have eq480811 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq6282 x
       have i₂ := eq480051
       grind)
    | exact superpose eq480051 eq6282
    | exact resolve eq6282 eq480051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6282 eq480051
  have eq480943 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq20 eq480811
    | exact resolve eq480811 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq480811
  have eq490577 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq480445 eq480943
    | exact resolve eq480943 eq480445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480445 eq480943
  have eq490578 : False := by grind
  exact eq490578

/-- `Equation2046`: `x = ((x ◇ x) ◇ y) ◇ (z ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,Y) else if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_x_pxy_y_pxy_Equation2046 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2046 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2046.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X2 X0)) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 (M.op X0 X0)
       have r₂ := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq11 X1 X0
       have r₂ := eq13 X0 X1
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
  have eq37 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
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
  have eq39 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq10
    | exact resolve eq10 eq14
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
  have eq48 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq99 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq45 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq45
    | (have j0 := eq45 y
       grind)
    | exact resolve eq45 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq116 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq48 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq48
    | (have j0 := eq48 y
       grind)
    | exact resolve eq48 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq125 : ∀ X0 : G, (k (M.op x y) (τ X0)) = (τ (k (σ (M.op x y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq51 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq175 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X1) (M.op X2 (M.op (M.op X0 X0) X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op (M.op X0 X0) X0) X1 X2
       have i₂ := eq16 X0 X0 (M.op X0 X0)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X2 : G, (M.op X0 X0) = (M.op X0 (M.op X2 (M.op X0 X0))) := by
    intro X0 X2
    first
    | (have i₁ := eq16 (M.op X0 X0) (M.op x X0) X2
       have i₂ := eq16 X0 (M.op X0 X0) x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 : G, y = (M.op (M.op (M.op y y) X0) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq16 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 y X0 x
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ y) (σ y)) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) X0 (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X0)) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X1 X0) X2 (M.op (M.op X0 X0) x)
       have i₂ := eq16 X0 x X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op (M.op x y) (M.op x y)) X0) y) := by
    intro X0
    first
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq548 : ∀ X0 : G, (k (M.op (M.op X0 X0) X0) X0) = (M.op (M.op (M.op X0 X0) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq181 (M.op (M.op X0 X0) X0)
       have i₂ := eq16 X0 X0 (M.op X0 X0)
       grind)
    | exact superpose eq16 eq181
    | exact resolve eq181 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq549 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq176 X0 X0
       have i₂ := eq181 X0
       grind)
    | exact superpose eq181 eq176
    | exact resolve eq176 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq577 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (k X0 X1)) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X2 X0
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq585 : ∀ X0 X1 X2 : G, (M.op (k (M.op X0 X0) X1) (M.op X2 X0)) = X0 ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 X2
       have i₂ := eq28 (M.op X0 X0) X1
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 (M.op X1 X1) X0
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq591 : (M.op x y) = (k x y) ∨ x = (M.op y y) := by
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
  have eq594 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
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
  have eq597 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq599 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq591
       grind)
    | exact superpose eq591 eq41
    | exact resolve eq41 eq591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591
  have eq600 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq599
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq599
    | exact resolve eq599 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599
  have eq602 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq600
    | exact resolve eq600 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600
  have eq609 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq597 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq597
    | (have j0 := eq597 (σ X0)
       grind)
    | exact resolve eq597 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq612 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq602 eq594
    | exact resolve eq594 eq602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq619 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq612
       have r₂ := eq27
       grind)
    | exact resolve eq612 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612
  have eq630 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq619 eq28
    | (have j0 := eq28 x y
       grind)
    | exact resolve eq28 eq619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq661 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq679 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq179 X0 (M.op X0 X0) X1
       have i₂ := eq16 X0 X0 (M.op X0 X0)
       grind)
    | exact superpose eq16 eq179
    | exact resolve eq179 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq770 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq630 eq116
    | exact resolve eq116 eq630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq630
  have eq776 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30 eq770
    | exact resolve eq770 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770
  have eq1777 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq619 eq661
    | exact resolve eq661 eq619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619
  have eq1788 : ∀ X0 X1 : G, (k (M.op X0 X0) X0) = X0 ∨ (M.op X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 (M.op X0 X0) X1
       have i₂ := eq661 X0
       grind)
    | exact superpose eq661 eq16
    | (have j1 := eq661 X0
       grind)
    | exact resolve eq16 eq661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1800 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op X0 X0) X1 (M.op X0 X0)
       have i₂ := eq661 X0
       grind)
    | exact superpose eq661 eq16
    | (have j1 := eq661 X0
       grind)
    | exact resolve eq16 eq661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1807 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq602 eq1777
    | exact resolve eq1777 eq602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1777
  have eq1988 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1807 eq181
    | exact resolve eq181 eq1807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1807
  have eq2019 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq26 eq1988
    | exact resolve eq1988 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1988
  have eq2027 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq602 eq2019
    | exact resolve eq2019 eq602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602 eq2019
  have eq2028 : x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq2027
       have r₂ := eq27
       grind)
    | exact resolve eq2027 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2027
  have eq2030 : ∀ X0 : G, y = (M.op (M.op x X0) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq177 X0
       have i₂ := eq2028
       grind)
    | exact superpose eq2028 eq177
    | exact resolve eq177 eq2028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq2035 : ∀ X0 : G, x = (M.op y (M.op X0 x)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq176 y x
       have i₂ := eq2028
       grind)
    | exact superpose eq2028 eq176
    | exact resolve eq176 eq2028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2036 : (k y x) = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq181 y
       have i₂ := eq2028
       grind)
    | exact superpose eq2028 eq181
    | exact resolve eq181 eq2028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2039 : y = (k x y) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq661 y
       have i₂ := eq2028
       grind)
    | exact superpose eq2028 eq661
    | exact resolve eq661 eq2028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2040 : ∀ X0 : G, (M.op x y) = (M.op x (M.op X0 (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq175 y y x
       have i₂ := eq2028
       grind)
    | exact superpose eq2028 eq175
    | exact resolve eq175 eq2028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq2043 : x = (k y y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq28 y y
       have i₂ := eq2028
       grind)
    | exact superpose eq2028 eq28
    | exact resolve eq28 eq2028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2044 : ∀ X0 : G, y = (M.op (M.op x X0) x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq16 y x y
       have i₂ := eq2028
       grind)
    | exact superpose eq2028 eq16
    | exact resolve eq16 eq2028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2046 : ∀ X0 : G, (M.op x y) = (M.op x (M.op X0 (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq2040 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2040
    | (have j0 := eq2040 X0
       grind)
    | exact resolve eq2040 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2040
  have eq2049 : y = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq2030 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2030
    | (have j0 := eq2030 y
       grind)
    | exact resolve eq2030 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2030
  have eq2062 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq2049
       have i₂ := eq28 sF0 sF0
       grind)
    | exact superpose eq28 eq2049
    | (have j1 := eq28 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq2049 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2065 : ∀ X0 : G, y ≠ X0 ∨ (k (M.op x y) X0) = (M.op (M.op x y) X0) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq2049 eq13
    | (have j0 := eq13 (M.op x y) X0
       grind)
    | (have r₁ := eq13 (M.op x y) y
       have r₂ := eq2049
       grind)
    | exact resolve eq13 eq2049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2069 : (k (M.op x y) y) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2049 eq181
    | exact resolve eq181 eq2049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2077 : ∀ X0 : G, (M.op x y) = (M.op (M.op y X0) y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq2049 eq16
    | exact resolve eq16 eq2049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2119 : y = (M.op (M.op x y) x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq2044 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2044
    | (have j0 := eq2044 y
       grind)
    | exact resolve eq2044 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2141 : (M.op x y) = (M.op x x) ∨ y = (k (M.op x y) x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2119 eq28
    | (have j0 := eq28 (M.op x y) x
       grind)
    | exact resolve eq28 eq2119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2184 : ∀ X0 : G, y = (M.op (M.op (M.op y y) X0) (k (M.op x y) y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq2069 eq16
    | exact resolve eq16 eq2069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2069
  have eq2186 : ∀ X0 : G, y = (M.op (M.op x X0) (k (M.op x y) y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq2028 eq2184
    | exact resolve eq2184 eq2028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2184
  have eq2215 : ∀ X0 : G, (M.op x y) = (k (M.op y X0) y) ∨ (M.op y y) = (M.op y X0) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq28 (M.op y X0) y
       have i₂ := eq2077 X0
       grind)
    | exact superpose eq2077 eq28
    | (have j0 := eq28 (M.op y X0) y
       grind)
    | exact resolve eq28 eq2077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2222 : ∀ X0 : G, (M.op x y) = (k (M.op y X0) y) ∨ x = (M.op y X0) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq2028 eq2215
    | (have j0 := eq2215 X0
       grind)
    | exact resolve eq2215 eq2028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2215
  have eq2237 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq2043
       grind)
    | exact superpose eq2043 eq41
    | exact resolve eq41 eq2043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2043
  have eq2243 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq2237
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2237
    | exact resolve eq2237 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2237
  have eq2247 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq2243
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2243
    | exact resolve eq2243 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2243
  have eq2757 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq2039
       grind)
    | exact superpose eq2039 eq36
    | exact resolve eq36 eq2039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq2039
  have eq2761 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq2757
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2757
    | exact resolve eq2757 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2757
  have eq2801 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2761 eq594
    | exact resolve eq594 eq2761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594 eq2761
  have eq2844 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq2062 eq181
    | exact resolve eq181 eq2062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2062
  have eq2861 : y = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq2049 eq2844
    | exact resolve eq2844 eq2049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2844
  have eq2862 : y = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq2861
  have eq2871 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2862 eq42
    | exact resolve eq42 eq2862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2862
  have eq2877 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq2871
    | exact resolve eq2871 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2871
  have eq2879 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq2877
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2877
    | exact resolve eq2877 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2877
  have eq2887 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq2879 eq577
    | (have j0 := eq577 (σ (M.op x y)) (σ (M.op x y)) x
       grind)
    | exact resolve eq577 eq2879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2888 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (k (σ (M.op x y)) (σ (M.op x y))) X0) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq28 eq2887
    | (have j1 := eq28 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq2887 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2887
  have eq2892 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ y) X0) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq2879 eq2888
    | exact resolve eq2888 eq2879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2888
  have eq2911 : x = (M.op y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (k (M.op x y) x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq2035 x
       have i₂ := eq2141
       grind)
    | exact superpose eq2141 eq2035
    | exact resolve eq2035 eq2141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2035 eq2141
  have eq2928 : y = (k (M.op x y) x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y (M.op x y)) := by grind
  clear eq2911
  have eq2991 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq2928 eq40
    | exact resolve eq40 eq2928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq2928
  have eq2993 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq20 eq2991
    | exact resolve eq2991 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2991
  have eq2995 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq2993
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2993
    | exact resolve eq2993 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2993
  have eq3985 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op y X0)) (σ y)) ∨ x = (M.op y X0) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq41 (M.op y X0)
       have i₂ := eq2222 X0
       grind)
    | exact superpose eq2222 eq41
    | (have j1 := eq2222 X0
       grind)
    | exact resolve eq41 eq2222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2222
  have eq3991 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op y X0)) (σ y)) ∨ x = (M.op y X0) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq20 eq3985
    | (have j0 := eq3985 X0
       grind)
    | exact resolve eq3985 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3985
  have eq4715 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2892 eq178
    | exact resolve eq178 eq2892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4720 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x y)) (M.op X0 (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq2892 eq16
    | exact resolve eq16 eq2892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4777 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2892 eq4720
    | exact resolve eq4720 eq2892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4720
  have eq4796 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq4777
  have eq4806 : (k (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq4796 eq181
    | exact resolve eq181 eq4796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4812 : ∀ X0 : G, (M.op (σ y) (σ (M.op x y))) = (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq4796 eq679
    | exact resolve eq679 eq4796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5018 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2801 eq2892
    | exact resolve eq2892 eq2801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2801
  have eq5049 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq5018
  have eq5055 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26 eq5049
    | exact resolve eq5049 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5049
  have eq5057 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq5055
       have r₂ := eq27
       grind)
    | exact resolve eq5055 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5055
  have eq5337 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq5057 eq181
    | exact resolve eq181 eq5057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5355 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq2879 eq5337
    | exact resolve eq5337 eq2879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5337
  have eq5506 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq5355 eq5057
    | exact resolve eq5057 eq5355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5057 eq5355
  have eq5528 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq5506
  have eq5552 : y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq2044 x
       have i₂ := eq5528
       grind)
    | exact superpose eq5528 eq2044
    | exact resolve eq2044 eq5528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5560 : (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq181 x
       have i₂ := eq5528
       grind)
    | exact superpose eq5528 eq181
    | exact resolve eq181 eq5528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5566 : ∀ X0 : G, (M.op y x) = (M.op (M.op x X0) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq679 x X0
       have i₂ := eq5528
       grind)
    | exact superpose eq5528 eq679
    | exact resolve eq679 eq5528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5567 : ∀ X0 : G, x = (M.op (M.op y X0) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq16 x x x
       have i₂ := eq5528
       grind)
    | exact superpose eq5528 eq16
    | exact resolve eq16 eq5528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5528
  have eq5576 : y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq5552
  have eq5594 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2077 eq5567
    | exact resolve eq5567 eq2077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5567
  have eq5595 : ∀ X0 : G, (k y x) = (M.op (M.op x X0) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq2036 eq5566
    | exact resolve eq5566 eq2036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5566
  have eq5596 : (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq5560
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq5560
    | exact resolve eq5560 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5560
  have eq5601 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2044 eq5595
    | exact resolve eq5595 eq2044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5595
  have eq5602 : (M.op x y) = (k (M.op x y) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq5594 eq5596
    | exact resolve eq5596 eq5594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5596
  have eq5604 : y = (k y (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq5594 eq5601
    | exact resolve eq5601 eq5594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5601
  have eq5657 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3991 x
       have i₂ := eq5576
       grind)
    | exact superpose eq5576 eq3991
    | exact resolve eq3991 eq5576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3991 eq5576
  have eq5667 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq5657
  have eq5679 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5667
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq5667
    | exact resolve eq5667 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5667
  have eq5686 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2247 eq5679
    | exact resolve eq5679 eq2247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5679
  have eq5689 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq5594 eq5686
    | exact resolve eq5686 eq5594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5686
  have eq5765 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq5602 eq41
    | exact resolve eq41 eq5602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5776 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq5765
    | exact resolve eq5765 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5765
  have eq5788 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq5604 eq42
    | exact resolve eq42 eq5604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5604
  have eq5793 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq5788
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq5788
    | exact resolve eq5788 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5788
  have eq10563 : (M.op (σ y) (σ (M.op x y))) = (M.op (k (σ (M.op x y)) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq4806 eq4812
    | exact resolve eq4812 eq4806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4812
  have eq10588 : (M.op (σ y) (σ (M.op x y))) = (M.op (k (σ (M.op x y)) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq10563
  have eq10682 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq5776 eq10588
    | exact resolve eq10588 eq5776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10588
  have eq10694 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq10682
  have eq10697 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq10694
    | (have j1 := eq28 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq10694 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10694
  have eq10699 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2879 eq10697
    | exact resolve eq10697 eq2879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10697
  have eq10711 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10699 eq2892
    | exact resolve eq2892 eq10699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10699
  have eq10725 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq10711
  have eq10765 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10725 eq2892
    | exact resolve eq2892 eq10725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2892
  have eq10779 : (k (σ y) (σ (M.op x y))) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10725 eq181
    | exact resolve eq181 eq10725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10788 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10725 eq28
    | (have j0 := eq28 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq28 eq10725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10725
  have eq10795 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq10788
  have eq10802 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq10765
  have eq10819 : (k (σ y) (σ (M.op x y))) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq10779
    | (have j1 := eq28 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq10779 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10779
  have eq10820 : (k (σ y) (σ (M.op x y))) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq10819
  have eq10826 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5793 eq10820
    | exact resolve eq10820 eq5793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5793 eq10820
  have eq10842 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq10826 eq16
    | exact resolve eq16 eq10826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10849 : (M.op (σ y) (σ y)) = (M.op (M.op (σ y) (σ y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10826 eq679
    | exact resolve eq679 eq10826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10868 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) := by
    first
    | (have i₁ := eq10842 (M.op sF1 sF1)
       have i₂ := eq661 sF1
       grind)
    | exact superpose eq661 eq10842
    | (have j1 := eq661 (σ (M.op x y))
       grind)
    | exact resolve eq10842 eq661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661
  have eq10872 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10842 sF1
       have i₂ := eq679 sF1 x
       grind)
    | (have i₁ := eq10842 sF1
       have i₂ := eq679 sF1 sF1
       grind)
    | exact superpose eq679 eq10842
    | exact resolve eq10842 eq679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10842
  have eq10908 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq10802 eq10868
    | exact resolve eq10868 eq10802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10802 eq10868
  have eq10910 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2879 eq10908
    | exact resolve eq10908 eq2879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10908
  have eq10911 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq10910
  have eq11009 : (σ y) = (M.op (M.op (σ y) (σ y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10849 eq178
    | exact resolve eq178 eq10849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq11013 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (σ y)) (M.op X0 (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq10849 eq16
    | exact resolve eq16 eq10849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11269 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10911 eq10872
    | exact resolve eq10872 eq10911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10872 eq10911
  have eq11316 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq11269
  have eq11342 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op X0 (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq11316 eq16
    | exact resolve eq16 eq11316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11316
  have eq11405 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11342 eq679
    | exact resolve eq679 eq11342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11342
  have eq11737 : (M.op (M.op (σ y) (σ y)) (σ y)) = (k (M.op (σ y) (σ y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11013 eq181
    | exact resolve eq181 eq11013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11738 : (σ y) = (M.op (M.op (σ y) (σ y)) (k (M.op (σ y) (σ y)) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11013 eq549
    | exact resolve eq549 eq11013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549 eq11013
  have eq11783 : (M.op (σ y) (σ y)) = (k (M.op (σ y) (σ y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10849 eq11737
    | exact resolve eq11737 eq10849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10849 eq11737
  have eq11821 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op X0 (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq11405 eq16
    | exact resolve eq16 eq11405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11974 : (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) = (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11821 eq181
    | exact resolve eq181 eq11821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12020 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11405 eq11974
    | exact resolve eq11974 eq11405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11405 eq11974
  have eq12048 : (τ (σ (M.op x y))) = (k y y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10795 eq116
    | exact resolve eq116 eq10795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq10795
  have eq12073 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29 eq12048
    | exact resolve eq12048 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12048
  have eq12169 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12073 eq12020
    | exact resolve eq12020 eq12073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12020 eq12073
  have eq12197 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y y) := by grind
  clear eq12169
  have eq12214 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y y) := by
    first
    | exact superpose eq2879 eq12197
    | exact resolve eq12197 eq2879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12197
  have eq12215 : (M.op x y) = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq12214
  have eq12237 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq12215
       grind)
    | exact superpose eq12215 eq41
    | exact resolve eq41 eq12215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12215
  have eq12255 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq12237
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12237
    | exact resolve eq12237 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12237
  have eq12258 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq12255
    | exact resolve eq12255 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12255
  have eq12586 : (σ y) = (M.op (k (σ y) (σ y)) (k (k (σ y) (σ y)) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq11738
       have i₂ := eq28 sF3 sF3
       grind)
    | exact superpose eq28 eq11738
    | (have j1 := eq28 (σ y) (σ y)
       grind)
    | exact resolve eq11738 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11738
  have eq12625 : (σ y) = (M.op (σ (M.op x y)) (k (σ (M.op x y)) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq12258 eq12586
    | exact resolve eq12586 eq12258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12586
  have eq12631 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq5776 eq12625
    | exact resolve eq12625 eq5776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5776 eq12625
  have eq12658 : (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq12631 eq11783
    | exact resolve eq11783 eq12631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11783 eq12631
  have eq12715 : (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq12658
  have eq12737 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq12258 eq12715
    | exact resolve eq12715 eq12258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12258 eq12715
  have eq12738 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq12737
  have eq12764 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq12738 eq11821
    | exact resolve eq11821 eq12738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11821
  have eq12771 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x y)) (M.op X0 (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq12738 eq176
    | exact resolve eq176 eq12738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq12778 : ∀ X0 : G, (M.op (σ y) (σ (M.op x y))) = (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq12738 eq679
    | exact resolve eq679 eq12738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12738
  have eq12792 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq12764
  have eq12813 : ∀ X0 : G, (σ y) = (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq10826 eq12778
    | exact resolve eq12778 eq10826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10826 eq12778
  have eq12835 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12792 eq11009
    | exact resolve eq11009 eq12792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11009
  have eq12910 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq12835
  have eq12937 : (σ y) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12910 eq28
    | (have j0 := eq28 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq28 eq12910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12910
  have eq12951 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x y)) (k X0 (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op (σ y) (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq12771 X0
       have i₂ := eq28 X0 sF3
       grind)
    | exact superpose eq28 eq12771
    | (have j1 := eq28 X0 (σ y)
       grind)
    | exact resolve eq12771 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12771
  have eq13025 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x y)) (k X0 (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq12792 eq12951
    | (have j0 := eq12951 X0
       grind)
    | exact resolve eq12951 eq12792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12792 eq12951
  have eq13845 : (σ y) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2247 eq13025
    | (have j0 := eq13025 (σ y)
       grind)
    | exact resolve eq13025 eq2247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13025
  have eq13873 : (σ y) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq13845
  have eq13889 : (σ y) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5594 eq13873
    | exact resolve eq13873 eq5594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13873
  have eq13892 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5689 eq13889
    | exact resolve eq13889 eq5689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5689 eq13889
  have eq13923 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13892 eq181
    | exact resolve eq181 eq13892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13892
  have eq13946 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq13923
    | exact resolve eq13923 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13923
  have eq13955 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13946 eq99
    | exact resolve eq99 eq13946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13946
  have eq13969 : (k (M.op x y) y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5594 eq13955
    | exact resolve eq13955 eq5594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5594 eq13955
  have eq13972 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5602 eq13969
    | exact resolve eq13969 eq5602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5602 eq13969
  have eq13981 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13972 eq14
    | exact resolve eq14 eq13972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13972
  have eq13982 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq13981
    | exact resolve eq13981 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13981
  have eq13985 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq13982
       have r₂ := eq27
       grind)
    | exact resolve eq13982 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13982
  have eq14268 : (τ (σ y)) = (k (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12937 eq125
    | exact resolve eq125 eq12937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14277 : y = (k (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32 eq14268
    | exact resolve eq14268 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14268
  have eq14278 : (M.op x y) = (k (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13985 eq14277
    | exact resolve eq14277 eq13985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13985 eq14277
  have eq15054 : ∀ X0 : G, y = (M.op y (M.op X0 y)) ∨ y = (k x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq1788 y X0
       have i₂ := eq2028
       grind)
    | exact superpose eq2028 eq1788
    | (have j0 := eq1788 y X0
       grind)
    | exact resolve eq1788 eq2028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2028
  have eq15057 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op X0 (M.op x y))) ∨ (M.op x y) = (k y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq2049 eq1788
    | (have j0 := eq1788 (M.op x y) X0
       grind)
    | exact resolve eq1788 eq2049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1788
  have eq15184 : y = (k y (M.op y y)) ∨ y = (k x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq15054 y
       have i₂ := eq181 y
       grind)
    | exact superpose eq181 eq15054
    | exact resolve eq15054 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15188 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (k x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq2077 (M.op x y)
       have i₂ := eq15054 x
       grind)
    | exact superpose eq15054 eq2077
    | exact resolve eq2077 eq15054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2077 eq15054
  have eq15215 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (k x y) := by grind
  clear eq15188
  have eq15243 : y = (k y (M.op x y)) ∨ y = (k x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq15215 eq15184
    | exact resolve eq15184 eq15215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15184 eq15215
  have eq15450 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ y = (k x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq15243 eq42
    | exact resolve eq42 eq15243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq15243
  have eq15457 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ y = (k x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq15450
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15450
    | exact resolve eq15450 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15450
  have eq16162 : (M.op x y) = (k (M.op x y) (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (k y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq15057 eq181
    | exact resolve eq181 eq15057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15057
  have eq16216 : (M.op x y) = (k (M.op x y) y) ∨ (M.op x y) = (k y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2049 eq16162
    | exact resolve eq16162 eq2049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2049 eq16162
  have eq16288 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (M.op x y) = (k y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq16216 eq41
    | exact resolve eq41 eq16216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16216
  have eq16313 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (M.op x y) = (k y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq16288
    | exact resolve eq16288 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16288
  have eq19261 : (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14278 eq39
    | exact resolve eq39 eq14278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq14278
  have eq19267 : (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq19261
    | exact resolve eq19261 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19261
  have eq19272 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12937 eq19267
    | exact resolve eq19267 eq12937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12937 eq19267
  have eq19273 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq19272
  have eq19302 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq19273 eq16
    | exact resolve eq16 eq19273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19273
  have eq19320 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12813 eq19302
    | exact resolve eq19302 eq12813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12813 eq19302
  have eq19321 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq19320
  have eq19377 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq19321 eq4715
    | exact resolve eq4715 eq19321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4715 eq19321
  have eq19389 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq19377
  have eq20434 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq19389 eq4806
    | exact resolve eq4806 eq19389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4806 eq19389
  have eq20488 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq20434
  have eq20502 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (k y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20488 eq16313
    | exact resolve eq16313 eq20488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16313
  have eq20503 : (τ (σ y)) = (k (M.op x y) (τ (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20488 eq125
    | exact resolve eq125 eq20488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq20488
  have eq20508 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (k y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq20502
  have eq20514 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (k (M.op x y) y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq32 eq20503
    | exact resolve eq20503 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20503
  have eq20553 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (k y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20508 eq181
    | exact resolve eq181 eq20508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20604 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (k y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20508 eq20553
    | exact resolve eq20553 eq20508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20508 eq20553
  have eq20606 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (k y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2879 eq20604
    | exact resolve eq20604 eq2879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20604
  have eq20607 : (M.op x y) = (k y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq20606
  have eq20616 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20607 eq37
    | exact resolve eq37 eq20607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq20607
  have eq20628 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq20616
    | exact resolve eq20616 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20616
  have eq20636 : (σ (M.op x y)) = (σ y) ∨ y = (k x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20628 eq15457
    | exact resolve eq15457 eq20628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15457
  have eq20640 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) (σ (M.op x y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq20628 eq577
    | (have j0 := eq577 (σ y) (σ (M.op x y)) x
       grind)
    | exact resolve eq577 eq20628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq577 eq20628
  have eq20641 : y = (k x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq20636
  have eq20645 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq4796 eq20640
    | exact resolve eq20640 eq4796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20640
  have eq20738 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (k (M.op x y) y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20514 eq181
    | exact resolve eq181 eq20514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20789 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (k (M.op x y) y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20514 eq20738
    | exact resolve eq20738 eq20514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20514 eq20738
  have eq20791 : (σ (M.op x y)) = (σ y) ∨ y = (k (M.op x y) y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2879 eq20789
    | exact resolve eq20789 eq2879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20789
  have eq20792 : y = (k (M.op x y) y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq20791
  have eq20796 : ∀ X0 : G, y = (M.op (M.op x X0) y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq20792 eq2186
    | exact resolve eq2186 eq20792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2186 eq20792
  have eq20834 : ∀ X0 : G, y = (M.op (M.op x X0) y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq20796 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20796
  have eq21076 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) X0) X0) = (M.op (M.op (M.op X0 X1) X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq548 X0
       have i₂ := eq679 X0 X1
       grind)
    | (have i₁ := eq548 X1
       have i₂ := eq679 X1 X1
       grind)
    | exact superpose eq679 eq548
    | exact resolve eq548 eq679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22636 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20645 eq548
    | exact resolve eq548 eq20645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20645
  have eq22716 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq4796 eq22636
    | exact resolve eq22636 eq4796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4796 eq22636
  have eq22722 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2879 eq22716
    | exact resolve eq22716 eq2879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2879 eq22716
  have eq22723 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq22722
  have eq22784 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ y) X0) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq22723 eq16
    | exact resolve eq16 eq22723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22789 : ∀ X0 : G, (σ (M.op x y)) = (M.op (k (σ y) X0) (σ y)) ∨ (M.op X0 X0) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq22723 eq585
    | exact resolve eq585 eq22723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585
  have eq24286 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2247 eq22789
    | (have j0 := eq22789 (σ y)
       grind)
    | exact resolve eq22789 eq2247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2247 eq22789
  have eq24345 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq24286
  have eq24360 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq26 eq24345
    | exact resolve eq24345 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24345
  have eq24362 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq24360
       have r₂ := eq27
       grind)
    | exact resolve eq24360 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24360
  have eq24423 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq24362 eq22784
    | exact resolve eq22784 eq24362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22784
  have eq24473 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq24423
  have eq24529 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq24362 eq24473
    | exact resolve eq24473 eq24362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24362 eq24473
  have eq24530 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq24529
  have eq24546 : (M.op x y) = (τ (σ y)) ∨ x = y := by
    first
    | exact superpose eq24530 eq29
    | exact resolve eq29 eq24530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24573 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq32 eq24546
    | exact resolve eq24546 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24546
  have eq24594 : (k (M.op x y) x) = (M.op (M.op x y) x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2036
       have i₂ := eq24573
       grind)
    | exact superpose eq24573 eq2036
    | exact resolve eq2036 eq24573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2036 eq24573
  have eq24733 : (k (M.op x y) x) = (M.op (M.op x y) x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have j1 := eq2065 x
       grind)
    | (have r₁ := eq24594
       have r₂ := eq2065 x
       grind)
    | exact resolve eq24594 eq2065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2065 eq24594
  have eq24738 : y = (k (M.op x y) x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2119 eq24733
    | exact resolve eq24733 eq2119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2119 eq24733
  have eq24739 : x = (k (M.op x y) x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq24530 eq24738
    | exact resolve eq24738 eq24530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24738
  have eq24787 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq24739 eq38
    | exact resolve eq38 eq24739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq24739
  have eq24803 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24787
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq24787
    | exact resolve eq24787 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24787
  have eq24810 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq24803 eq2995
    | exact resolve eq2995 eq24803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2995 eq24803
  have eq24821 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y (M.op x y)) := by grind
  clear eq24810
  have eq24828 : x = (M.op x (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq24530 eq24821
    | exact resolve eq24821 eq24530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24821
  have eq25634 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq24828 eq2044
    | exact resolve eq2044 eq24828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2044
  have eq25643 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq24828 eq2046
    | exact resolve eq2046 eq24828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2046
  have eq25679 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq25643
  have eq25688 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq25634
  have eq25711 : x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq24530 eq25688
    | exact resolve eq25688 eq24530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25688
  have eq25725 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq25679 eq25711
    | exact resolve eq25711 eq25679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25711
  have eq26504 : (k x (M.op x y)) = (M.op x (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq181 x
       have i₂ := eq25679
       grind)
    | exact superpose eq25679 eq181
    | exact resolve eq181 eq25679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq25679
  have eq26571 : x = (k x (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq24828 eq26504
    | exact resolve eq26504 eq24828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24828 eq26504
  have eq26591 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq25725 eq26571
    | exact resolve eq26571 eq25725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25725 eq26571
  have eq26951 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26591 eq609
    | (have j0 := eq609 (M.op x y)
       grind)
    | exact resolve eq609 eq26591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609 eq26591
  have eq26958 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq26951
  have eq26970 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq26958
    | exact resolve eq26958 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26958
  have eq26973 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq22723 eq26970
    | exact resolve eq26970 eq22723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22723 eq26970
  have eq26974 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq26973
  have eq26987 : (k x y) = (τ (k (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26974 eq99
    | exact resolve eq99 eq26974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq26974
  have eq27261 : (k x x) = (k x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq98 eq26987
    | exact resolve eq26987 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq26987
  have eq27294 : y = (k x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20641 eq27261
    | exact resolve eq27261 eq20641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20641 eq27261
  have eq27305 : x = (k x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq24530 eq27294
    | exact resolve eq27294 eq24530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24530 eq27294
  have eq27451 : x ≠ x ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq597 x
       have i₂ := eq27305
       grind)
    | exact superpose eq27305 eq597
    | (have j0 := eq597 x
       grind)
    | (have r₁ := eq597 x
       have r₂ := eq27305
       grind)
    | exact resolve eq597 eq27305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27305
  have eq27453 : x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq27451
  have eq27565 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq20834 x
       have i₂ := eq27453
       grind)
    | exact superpose eq27453 eq20834
    | exact resolve eq20834 eq27453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20834 eq27453
  have eq27597 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq27565
  have eq27642 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq27597
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq27597
    | exact resolve eq27597 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27597
  have eq27684 : (M.op x y) = (τ (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27642 eq29
    | exact resolve eq29 eq27642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq27642
  have eq27711 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32 eq27684
    | exact resolve eq27684 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq27684
  have eq27712 : y = (M.op x y) := by grind
  clear eq27711
  have eq27726 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq27712
       grind)
    | exact superpose eq27712 eq18
    | exact resolve eq18 eq27712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq27727 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq27712
       grind)
    | exact superpose eq27712 eq24
    | exact resolve eq24 eq27712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq27729 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (k X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq27712
       grind)
    | exact superpose eq27712 eq41
    | exact resolve eq41 eq27712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq27731 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op (M.op x y) (M.op x y)) X0) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq183 X0
       have i₂ := eq27712
       grind)
    | exact superpose eq27712 eq183
    | exact resolve eq183 eq27712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq27735 : x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq776
       have i₂ := eq27712
       grind)
    | exact superpose eq27712 eq776
    | exact resolve eq776 eq27712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776 eq27712
  have eq27985 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq27727 eq20
    | exact resolve eq20 eq27727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27988 : (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq27727 eq15
    | exact resolve eq15 eq27727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28807 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op (M.op x y) X0) (M.op x y)) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq27731 sF0
       have i₂ := eq679 sF0 x
       grind)
    | (have i₁ := eq27731 sF0
       have i₂ := eq679 sF0 sF0
       grind)
    | exact superpose eq679 eq27731
    | exact resolve eq27731 eq679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679
  have eq28816 : (M.op x y) = (k (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq27731 eq548
    | exact resolve eq548 eq27731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27731
  have eq28841 : ∀ X0 : G, (M.op x y) = (k (M.op (M.op (M.op x y) X0) (M.op x y)) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq28807 x
       have i₂ := eq21076 sF0 x
       grind)
    | exact superpose eq21076 eq28807
    | exact resolve eq28807 eq21076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21076 eq28807
  have eq29093 : (M.op x y) = (k (M.op (k (M.op x y) (M.op x y)) (M.op x y)) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq28816
       have i₂ := eq28 sF0 sF0
       grind)
    | exact superpose eq28 eq28816
    | (have j1 := eq28 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq28816 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34261 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq27735 eq27729
    | exact resolve eq27729 eq27735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34277 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq20 eq34261
    | exact resolve eq34261 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34261
  have eq34285 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq27985 eq34277
    | exact resolve eq34277 eq27985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34277
  have eq34291 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq34285
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq34285
    | exact resolve eq34285 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34285
  have eq38996 : (M.op x y) = (k (M.op (M.op x y) (M.op x y)) (M.op x y)) ∨ (M.op x y) = (k (M.op (M.op x y) (M.op x y)) (M.op x y)) := by
    first
    | (have i₁ := eq28816
       have i₂ := eq1800 sF0 sF0
       grind)
    | exact superpose eq1800 eq28816
    | (have j1 := eq1800 (M.op x y) x
       grind)
    | exact resolve eq28816 eq1800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1800 eq28816
  have eq39130 : (M.op x y) = (k (M.op (M.op x y) (M.op x y)) (M.op x y)) := by grind
  clear eq38996
  have eq39450 : (σ (M.op x y)) = (k (σ (M.op (M.op x y) (M.op x y))) (σ y)) := by
    first
    | exact superpose eq39130 eq27729
    | exact resolve eq27729 eq39130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27729 eq39130
  have eq39453 : (σ (M.op x y)) = (k (σ (M.op (M.op x y) (M.op x y))) (σ y)) := by
    first
    | exact superpose eq20 eq39450
    | exact resolve eq39450 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39450
  have eq39456 : (σ y) = (k (σ (M.op (M.op x y) (M.op x y))) (σ y)) := by
    first
    | exact superpose eq27985 eq39453
    | exact resolve eq39453 eq27985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39453
  have eq41051 : (M.op x y) = (k (M.op x (M.op x y)) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq27735 eq29093
    | exact resolve eq29093 eq27735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27735 eq29093
  have eq41073 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq27726 eq41051
    | exact resolve eq41051 eq27726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41051
  have eq41077 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have j1 := eq597 (M.op x y)
       grind)
    | (have r₁ := eq41073
       have r₂ := eq597 (M.op x y)
       grind)
    | exact resolve eq41073 eq597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597 eq41073
  have eq41093 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq41077 eq39456
    | exact resolve eq39456 eq41077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41077
  have eq41172 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq20 eq41093
    | exact resolve eq41093 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41093
  have eq41175 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq27985 eq41172
    | exact resolve eq41172 eq27985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41172
  have eq41176 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq34291 eq41175
    | exact resolve eq41175 eq34291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34291 eq41175
  have eq41177 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) := by grind
  clear eq41176
  have eq41230 : (M.op x y) = (k (M.op x (M.op x y)) (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq41177 eq28841
    | exact resolve eq28841 eq41177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28841
  have eq41256 : (M.op (M.op x (M.op x y)) (M.op x y)) = (k (M.op x (M.op x y)) (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq41177 eq548
    | exact resolve eq548 eq41177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548
  have eq41288 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27726 eq41256
    | exact resolve eq41256 eq27726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41256
  have eq41291 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27726 eq41230
    | exact resolve eq41230 eq27726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41230
  have eq41297 : x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq41177 eq41288
    | exact resolve eq41288 eq41177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41177 eq41288
  have eq41300 : (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq41291 eq41297
    | exact resolve eq41297 eq41291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41291 eq41297
  have eq41510 : (M.op x y) = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq41300 eq27988
    | exact resolve eq27988 eq41300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27988 eq41300
  have eq41557 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq41510
    | exact resolve eq41510 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq41510
  have eq41558 : x = (M.op x y) := by grind
  clear eq41557
  have eq41766 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq41558
       grind)
    | exact superpose eq41558 eq22
    | exact resolve eq22 eq41558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq41886 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq27726
       have i₂ := eq41558
       grind)
    | exact superpose eq41558 eq27726
    | exact resolve eq27726 eq41558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27726 eq41558
  have eq41911 : (σ x) = (σ y) := by
    first
    | exact superpose eq41766 eq27727
    | exact resolve eq27727 eq41766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27727
  have eq41912 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq41766 eq20
    | exact resolve eq20 eq41766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41766
  have eq42042 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq41911 eq26
    | exact resolve eq26 eq41911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq42263 : (σ x) = (k (σ (M.op (M.op x y) (M.op x y))) (σ x)) := by
    first
    | exact superpose eq41911 eq39456
    | exact resolve eq39456 eq41911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39456
  have eq42278 : (σ x) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq41886 eq42263
    | exact resolve eq42263 eq41886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41886 eq42263
  have eq42344 : (σ x) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq20 eq42278
    | exact resolve eq42278 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq42278
  have eq42401 : (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27985 eq42344
    | exact resolve eq42344 eq27985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27985 eq42344
  have eq42405 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq41911 eq42401
    | exact resolve eq42401 eq41911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41911 eq42401
  have eq43586 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq42042 eq28
    | exact resolve eq28 eq42042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq42042
  have eq43601 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq42405 eq43586
    | exact resolve eq43586 eq42405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42405 eq43586
  have eq43602 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq43601
  have eq43644 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq43602 eq27
    | exact resolve eq27 eq43602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq43602
  have eq43768 : False := by grind
  exact eq43768

/-- `Equation2065`: `x = ((x ◇ y) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(Y,Y) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pyx_pyx_pxy_Equation2065 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2065 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2065.models_iff G M).mp hM
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
  have eq756 : (M.op x y) = (k x y) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
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
  have eq762 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
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
  have eq769 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq770 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq769 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769
  have eq799 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq770 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq770
    | (have j0 := eq770 (σ X0)
       grind)
    | exact resolve eq770 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1724 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq756
       grind)
    | exact superpose eq756 eq41
    | exact resolve eq41 eq756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq756
  have eq1725 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1724
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1724
    | exact resolve eq1724 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1724
  have eq1727 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq1725
    | exact resolve eq1725 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1725
  have eq22826 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1727 eq762
    | exact resolve eq762 eq1727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762 eq1727
  have eq22835 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq22826
       have r₂ := eq27
       grind)
    | exact resolve eq22826 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22826
  have eq22844 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq22835 eq13
    | (have j0 := eq13 (σ y) X0
       grind)
    | (have r₁ := eq13 (σ y) x
       have r₂ := eq22835
       grind)
    | (have r₁ := eq13 (σ x) x
       have r₂ := eq22835
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq22835
       grind)
    | exact resolve eq13 eq22835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22854 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq22844 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22844
  have eq22952 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq22854 eq22835
    | exact resolve eq22835 eq22854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22835 eq22854
  have eq22977 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq22952
  have eq23048 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq22977 eq153
    | exact resolve eq153 eq22977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq22977
  have eq23061 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq32 eq23048
    | exact resolve eq23048 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq23048
  have eq23066 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq770 (σ x)
       grind)
    | (have r₁ := eq23061
       have r₂ := eq770 y
       grind)
    | exact resolve eq23061 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23061
  have eq23081 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op X0 (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq23066 eq13
    | (have j0 := eq13 (σ x) X0
       grind)
    | (have r₁ := eq13 (σ x) x
       have r₂ := eq23066
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq23066
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq23066
       grind)
    | exact resolve eq13 eq23066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23091 : ∀ X0 : G, (k (σ x) X0) = (M.op X0 (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq23081 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23081
  have eq23309 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq23091 eq23066
    | exact resolve eq23066 eq23091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23066 eq23091
  have eq23329 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq23309
  have eq23479 : (τ (σ x)) = (k (τ (σ x)) x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq23329 eq142
    | exact resolve eq142 eq23329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq23329
  have eq23492 : x = (k x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq30 eq23479
    | exact resolve eq23479 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq23479
  have eq23497 : y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq770 y
       grind)
    | (have r₁ := eq23492
       have r₂ := eq770 x
       grind)
    | exact resolve eq23492 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770 eq23492
  have eq23503 : ∀ X0 : G, y ≠ y ∨ (k y X0) = (M.op X0 y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq23497
       grind)
    | exact superpose eq23497 eq13
    | (have j0 := eq13 y X0
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq23497
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq23497
       grind)
    | exact resolve eq13 eq23497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23513 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq23503 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23503
  have eq23584 : (M.op x y) = (k y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq23513 x
       grind)
    | exact superpose eq23513 eq18
    | (have j1 := eq23513 x
       grind)
    | exact resolve eq18 eq23513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23591 : y = (k y y) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq23497
       have i₂ := eq23513 y
       grind)
    | exact superpose eq23513 eq23497
    | exact resolve eq23497 eq23513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23497 eq23513
  have eq23636 : y = (k y y) ∨ x = (M.op x x) := by grind
  clear eq23591
  have eq23693 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq23584
       grind)
    | exact superpose eq23584 eq40
    | exact resolve eq40 eq23584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23584
  have eq23698 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq23693
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq23693
    | exact resolve eq23693 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23693
  have eq23702 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq23698
    | exact resolve eq23698 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23698
  have eq23708 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq799 y
       have i₂ := eq23636
       grind)
    | exact superpose eq23636 eq799
    | (have j0 := eq799 y
       grind)
    | exact resolve eq799 eq23636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23636
  have eq23719 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq23708
  have eq23720 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq23719
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq23719
    | exact resolve eq23719 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23719
  have eq24155 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq23720 eq13
    | (have j0 := eq13 (σ y) X0
       grind)
    | (have r₁ := eq13 (σ y) x
       have r₂ := eq23720
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq23720
       grind)
    | exact resolve eq13 eq23720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23720
  have eq24165 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq24155 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24155
  have eq24689 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq24165 eq26
    | (have j1 := eq24165 (σ x)
       grind)
    | exact resolve eq26 eq24165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24165
  have eq24743 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq23702 eq24689
    | exact resolve eq24689 eq23702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23702 eq24689
  have eq24788 : x = (M.op x x) := by
    first
    | (have r₁ := eq24743
       have r₂ := eq27
       grind)
    | exact resolve eq24743 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24743
  have eq24826 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq28 X0 x
       have i₂ := eq24788
       grind)
    | exact superpose eq24788 eq28
    | (have j0 := eq28 X0 x
       grind)
    | (have r₁ := eq28 X0 x
       have r₂ := eq24788
       grind)
    | exact resolve eq28 eq24788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24827 : ∀ X0 : G, x ≠ x ∨ (k x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq13 x X0
       have i₂ := eq24788
       grind)
    | exact superpose eq24788 eq13
    | (have j0 := eq13 x X0
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq24788
       grind)
    | exact resolve eq13 eq24788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24837 : ∀ X0 : G, (k x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq24827 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24827
  have eq24838 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq24826 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24826
  have eq24985 : x = (k x x) := by
    first
    | (have i₁ := eq24788
       have i₂ := eq24837 x
       grind)
    | exact superpose eq24837 eq24788
    | exact resolve eq24788 eq24837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24788 eq24837
  have eq25206 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq799 x
       have i₂ := eq24985
       grind)
    | exact superpose eq24985 eq799
    | (have j0 := eq799 x
       grind)
    | exact resolve eq799 eq24985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq799 eq24985
  have eq25217 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq25206
  have eq25218 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq25217
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq25217
    | exact resolve eq25217 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq25217
  have eq25236 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq25218 eq28
    | (have j0 := eq28 X0 (σ x)
       grind)
    | (have r₁ := eq28 X0 (σ x)
       have r₂ := eq25218
       grind)
    | exact resolve eq28 eq25218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq25218
  have eq25248 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq25236 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25236
  have eq25396 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq24838 y
       grind)
    | exact superpose eq24838 eq18
    | (have j1 := eq24838 y
       grind)
    | exact resolve eq18 eq24838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq24838
  have eq25740 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq25396
       grind)
    | exact superpose eq25396 eq40
    | exact resolve eq40 eq25396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq25396
  have eq25743 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq25740
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq25740
    | exact resolve eq25740 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq25740
  have eq25747 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq20 eq25743
    | exact resolve eq25743 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq25743
  have eq26560 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq25248 eq26
    | (have j1 := eq25248 (σ y)
       grind)
    | exact resolve eq26 eq25248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq25248
  have eq26728 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq25747 eq26560
    | exact resolve eq26560 eq25747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25747 eq26560
  have eq26826 : False := by grind
  exact eq26826

/-- `Equation2132`: `x = ((y ◇ y) ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_y_pxy_y_pxy_Equation2132 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2132 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2132.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  clear eq35
  have eq74 : y ≠ (M.op x y) ∨ x = (M.op y x) ∨ y = (k x y) := by
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
  have eq75 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
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
  have eq104 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq92 x y
       grind)
    | exact superpose eq92 eq44
    | (have j1 := eq92 x y
       grind)
    | exact resolve eq44 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq104
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq104
    | exact resolve eq104 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq117 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq115
    | exact resolve eq115 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq118 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq117
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq117
    | exact resolve eq117 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq121 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq118 eq92
    | (have j0 := eq92 (σ x) (σ y)
       grind)
    | exact resolve eq92 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq121
    | exact resolve eq121 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq125 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq122
       have r₂ := eq27
       grind)
    | exact resolve eq122 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq127 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq125
    | exact resolve eq125 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq129 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq127 eq27
    | exact resolve eq27 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq505 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq127 eq75
    | (have r₁ := eq75
       have r₂ := eq127
       grind)
    | exact resolve eq75 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq127
  have eq506 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq505
  have eq509 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq506 eq118
    | exact resolve eq118 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506
  have eq513 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq509
  have eq518 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq513
       have r₂ := eq129
       grind)
    | exact resolve eq513 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq513
  have eq526 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq518 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq518
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq518
       grind)
    | exact resolve eq13 eq518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518
  have eq527 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq526
  have eq533 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq527
    | exact resolve eq527 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527
  have eq612 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq533 eq118
    | exact resolve eq118 eq533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq533
  have eq615 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq612
  have eq619 : y = (M.op x y) := by
    first
    | (have r₁ := eq615
       have r₂ := eq27
       grind)
    | exact resolve eq615 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq615
  have eq621 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq619 eq20
    | exact resolve eq20 eq619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq625 : y ≠ y ∨ x = (M.op y x) ∨ y = (k x y) := by
    first
    | exact superpose eq619 eq74
    | (have r₁ := eq74
       have r₂ := eq619
       grind)
    | exact resolve eq74 eq619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq631 : y = (k x y) ∨ x = (M.op y x) := by grind
  clear eq625
  have eq640 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq621
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq621
    | exact resolve eq621 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621
  have eq641 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq640 eq26
    | exact resolve eq26 eq640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq744 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq631
       grind)
    | exact superpose eq631 eq44
    | exact resolve eq44 eq631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631
  have eq751 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq640 eq744
    | exact resolve eq744 eq640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744
  have eq753 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq751
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq751
    | exact resolve eq751 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751
  have eq754 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq640 eq753
    | exact resolve eq753 eq640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq753
  have eq757 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq754 eq92
    | (have j0 := eq92 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq92 eq754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq754
  have eq758 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op y x) := by grind
  clear eq757
  have eq760 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq641 eq758
    | exact resolve eq758 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq758
  have eq763 : x = (M.op y x) := by
    first
    | (have r₁ := eq760
       have r₂ := eq27
       grind)
    | exact resolve eq760 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq760
  have eq769 : x ≠ x ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq763
       grind)
    | exact superpose eq763 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq763
       grind)
    | exact resolve eq13 eq763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763
  have eq770 : (M.op x y) = (k x y) := by grind
  clear eq769
  have eq772 : (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq770
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq770
    | exact resolve eq770 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq770
  have eq775 : y = (k x y) := by
    first
    | exact superpose eq619 eq772
    | exact resolve eq772 eq619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619 eq772
  have eq787 : (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq775
       grind)
    | exact superpose eq775 eq44
    | exact resolve eq44 eq775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq775
  have eq794 : (σ y) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq640 eq787
    | exact resolve eq787 eq640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787
  have eq796 : (σ y) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq794
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq794
    | exact resolve eq794 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq794
  have eq797 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq640 eq796
    | exact resolve eq796 eq640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640 eq796
  have eq805 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq797 eq92
    | (have j0 := eq92 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq92 eq797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq797
  have eq806 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq805
  have eq808 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq641 eq806
    | exact resolve eq806 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641 eq806
  have eq811 : False := by grind
  exact eq811

/-- `Equation2162`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxy_y_pxx_y_pxy_Equation2162 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2162 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2162.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
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
  have eq60 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : (M.op x y) ≠ (M.op x x) ∨ (k x y) = (M.op x x) := by
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
  have eq67 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq68 (σ X0)
       grind)
    | exact superpose eq68 eq10
    | exact resolve eq10 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq68 x
       grind)
    | exact superpose eq68 eq43
    | exact resolve eq43 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq74 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq71
       have i₂ := eq68 sF2
       grind)
    | exact superpose eq68 eq71
    | exact resolve eq71 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq75 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq70 X0
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq70
    | exact resolve eq70 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq70
  have eq79 : y ≠ (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ y = (k x y) := by
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
  have eq80 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq91 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq91
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq91
    | exact resolve eq91 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq98 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq96
    | exact resolve eq96 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq100 : y = (M.op x y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq98
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq98
    | exact resolve eq98 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq101 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq100
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq100
    | exact resolve eq100 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq100
  have eq1001 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq87 X0 X1
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq87
    | (have j0 := eq87 X0 X1
       grind)
    | exact resolve eq87 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq87
  have eq1111 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1001 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1001
  have eq12456 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq101 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12457 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq12456
    | exact resolve eq12456 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12456
  have eq12468 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq12457
       have r₂ := eq27
       grind)
    | exact resolve eq12457 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12457
  have eq12472 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq12468
    | exact resolve eq12468 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12468
  have eq12474 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq12472
    | exact resolve eq12472 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12472
  have eq12476 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq12474 eq67
    | (have r₁ := eq67
       have r₂ := eq12474
       grind)
    | exact resolve eq67 eq12474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12474
  have eq12539 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq12476
  have eq12546 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq12539 eq101
    | exact resolve eq101 eq12539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12539
  have eq12554 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq12546
  have eq12556 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq12554
       have r₂ := eq27
       grind)
    | exact resolve eq12554 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12554
  have eq12558 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq66
       have i₂ := eq12556
       grind)
    | exact superpose eq12556 eq66
    | (have r₁ := eq66
       have r₂ := eq12556
       grind)
    | exact resolve eq66 eq12556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12559 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq74
       have i₂ := eq12556
       grind)
    | exact superpose eq12556 eq74
    | exact resolve eq74 eq12556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12621 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq12558
  have eq12629 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq12559
    | exact resolve eq12559 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12559
  have eq12633 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq12621
       grind)
    | exact superpose eq12621 eq44
    | exact resolve eq44 eq12621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12621
  have eq12647 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq12633
    | exact resolve eq12633 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12633
  have eq12739 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12647 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq12647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12647
  have eq12742 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12739
    | exact resolve eq12739 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12739
  have eq12753 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq12742
       have r₂ := eq27
       grind)
    | exact resolve eq12742 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12742
  have eq12757 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12753
    | exact resolve eq12753 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12753
  have eq12758 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq12757
  have eq12761 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq12758
    | exact resolve eq12758 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12758
  have eq12773 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12761 eq12629
    | exact resolve eq12629 eq12761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12629 eq12761
  have eq12829 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq12773
  have eq12833 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq12829
       have r₂ := eq27
       grind)
    | exact resolve eq12829 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12829
  have eq12835 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12833 eq27
    | exact resolve eq27 eq12833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12838 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12833 eq80
    | (have r₁ := eq80
       have r₂ := eq12833
       grind)
    | exact resolve eq80 eq12833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq12833
  have eq12870 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq12838
  have eq16281 : (τ (σ y)) = (k x y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12870 eq60
    | exact resolve eq60 eq12870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16282 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12870 eq101
    | exact resolve eq101 eq12870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12870
  have eq16297 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq16282
  have eq16310 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq16297
       have r₂ := eq12835
       grind)
    | exact resolve eq16297 eq12835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16297
  have eq16311 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq16281
    | exact resolve eq16281 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16281
  have eq16322 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16310 eq67
    | exact resolve eq67 eq16310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16310
  have eq16419 : (σ y) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq16322
       have r₂ := eq12556
       grind)
    | exact resolve eq16322 eq12556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12556 eq16322
  have eq16617 : (τ (σ y)) = (k x y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16419 eq60
    | exact resolve eq60 eq16419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq16618 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16419 eq101
    | exact resolve eq101 eq16419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq16419
  have eq16633 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq16618
  have eq16646 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq16633
       have r₂ := eq12835
       grind)
    | exact resolve eq16633 eq12835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16633
  have eq16647 : y = (k x y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq16617
    | exact resolve eq16617 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq16617
  have eq16654 : y = (k x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq16647
       have r₂ := eq79
       grind)
    | exact resolve eq16647 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq16647
  have eq16655 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq66
       have i₂ := eq16646
       grind)
    | exact superpose eq16646 eq66
    | (have r₁ := eq66
       have r₂ := eq16646
       grind)
    | exact resolve eq66 eq16646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16656 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq16646
       grind)
    | exact superpose eq16646 eq74
    | exact resolve eq74 eq16646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16646
  have eq16728 : (M.op x y) = (k x y) ∨ y = (M.op x y) := by grind
  clear eq16655
  have eq16736 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq16656
    | exact resolve eq16656 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16656
  have eq16776 : (σ (M.op x y)) = (σ y) ∨ y = (k x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16736 eq16311
    | exact resolve eq16311 eq16736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16311 eq16736
  have eq16848 : (σ (M.op x y)) = (σ y) ∨ y = (k x y) ∨ y = (M.op x y) := by grind
  clear eq16776
  have eq16857 : y = (k x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq16848
       have r₂ := eq12835
       grind)
    | exact resolve eq16848 eq12835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12835 eq16848
  have eq16924 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16728
       have i₂ := eq16857
       grind)
    | exact superpose eq16857 eq16728
    | exact resolve eq16728 eq16857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16728 eq16857
  have eq16929 : y = (M.op x y) := by grind
  clear eq16924
  have eq17099 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq16929 eq20
    | exact resolve eq20 eq16929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq17235 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq17099
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq17099
    | exact resolve eq17099 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17099
  have eq17250 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq17235 eq26
    | exact resolve eq26 eq17235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq25294 : y = (k x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq16929 eq16654
    | exact resolve eq16654 eq16929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16654
  have eq25298 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq25294
       grind)
    | exact superpose eq25294 eq44
    | exact resolve eq44 eq25294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25309 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1111 x y
       have i₂ := eq25294
       grind)
    | exact superpose eq25294 eq1111
    | (have j0 := eq1111 x y
       grind)
    | exact resolve eq1111 eq25294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1111 eq25294
  have eq25312 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq25309
  have eq25319 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq25312
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq25312
    | exact resolve eq25312 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25312
  have eq25328 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq17235 eq25298
    | exact resolve eq25298 eq17235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25298
  have eq25330 : (M.op (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq25319
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq25319
    | exact resolve eq25319 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25319
  have eq25339 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq25328
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq25328
    | exact resolve eq25328 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25328
  have eq25340 : (M.op (σ x) (σ x)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq17235 eq25330
    | exact resolve eq25330 eq17235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25330
  have eq25349 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq17235 eq25339
    | exact resolve eq25339 eq17235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25339
  have eq25350 : (M.op (σ x) (σ x)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq25340
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq25340
    | exact resolve eq25340 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25340
  have eq25355 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq17250 eq25350
    | exact resolve eq25350 eq17250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25350
  have eq25358 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq25355
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq25355
    | exact resolve eq25355 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25355
  have eq25361 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq17235 eq25358
    | exact resolve eq25358 eq17235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25358
  have eq25364 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq25361
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq25361
    | exact resolve eq25361 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq25361
  have eq25367 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq17250 eq25364
    | exact resolve eq25364 eq17250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25364
  have eq25370 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq25367
       have r₂ := eq27
       grind)
    | exact resolve eq25367 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25367
  have eq26366 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq25370 eq67
    | (have r₁ := eq67
       have r₂ := eq25370
       grind)
    | exact resolve eq67 eq25370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq25370
  have eq26466 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq26366
  have eq26479 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq17235 eq26466
    | exact resolve eq26466 eq17235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26466
  have eq30580 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26479 eq25349
    | exact resolve eq25349 eq26479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25349 eq26479
  have eq30587 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq30580
  have eq30589 : y = (M.op x x) := by
    first
    | (have r₁ := eq30587
       have r₂ := eq27
       grind)
    | exact resolve eq30587 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30587
  have eq30605 : y ≠ (M.op x y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq66
       have i₂ := eq30589
       grind)
    | exact superpose eq30589 eq66
    | exact resolve eq66 eq30589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq30606 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq74
       have i₂ := eq30589
       grind)
    | exact superpose eq30589 eq74
    | exact resolve eq74 eq30589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq30589
  have eq30727 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq30606
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq30606
    | exact resolve eq30606 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30606
  have eq30728 : y = (k x y) := by
    first
    | (have r₁ := eq30605
       have r₂ := eq16929
       grind)
    | exact resolve eq30605 eq16929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16929 eq30605
  have eq30737 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq17235 eq30727
    | exact resolve eq30727 eq17235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30727
  have eq31694 : (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq30728
       grind)
    | exact superpose eq30728 eq44
    | exact resolve eq44 eq30728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq30728
  have eq31728 : (σ y) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq17235 eq31694
    | exact resolve eq31694 eq17235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31694
  have eq31741 : (σ y) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq31728
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq31728
    | exact resolve eq31728 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq31728
  have eq31753 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq17235 eq31741
    | exact resolve eq31741 eq17235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17235 eq31741
  have eq31958 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq31753 eq11
    | (have j0 := eq11 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq31753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31753
  have eq31959 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq31958
  have eq31962 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq17250 eq31959
    | exact resolve eq31959 eq17250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31959
  have eq31983 : (M.op (σ x) (σ x)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have r₁ := eq31962
       have r₂ := eq27
       grind)
    | exact resolve eq31962 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31962
  have eq31996 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq17250 eq31983
    | exact resolve eq31983 eq17250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17250 eq31983
  have eq32007 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30737 eq31996
    | exact resolve eq31996 eq30737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30737 eq31996
  have eq32012 : False := by grind
  exact eq32012

/-- `Equation2291`: `x = (y ◇ (x ◇ (x ◇ x))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_x_pyx_x_pyx_Equation2291 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2291 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2291.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X0) = X1 := by
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
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq34 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq46 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    grind
  have eq69 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 : G, (M.op (σ X0) X1) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 X0
       have i₂ := eq14 X1 (σ X0)
       grind)
    | exact superpose eq14 eq24
    | (have j1 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq24 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq174 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq69 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq748 : ∀ X0 X1 : G, (σ (σ X0)) ≠ (σ (σ (k X0 X1))) ∨ (σ (σ X0)) = (M.op (σ (σ X1)) (σ (σ X0))) ∨ (M.op (σ (σ X0)) (σ (σ X0))) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq174 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq174
    | (have j0 := eq174 (σ X1) (σ X0)
       grind)
    | exact resolve eq174 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq2658 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (σ X1)) = X0 ∨ (M.op X0 X0) = (σ X1) ∨ (k (τ X0) X1) = (τ (M.op (σ X1) X0)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X1)
       have i₂ := eq73 X1 X0
       grind)
    | exact superpose eq73 eq13
    | (have j0 := eq13 X0 (σ X1)
       have j1 := eq73 X1 X0
       grind)
    | (have r₁ := eq13 X1 (σ X0)
       have r₂ := eq73 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq73 X0 (σ X0)
       grind)
    | exact resolve eq13 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2673 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq73 X0 (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq2674 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq2673 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2673
  have eq2675 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (σ X1)) = X0 ∨ (M.op X0 X0) = (σ X1) ∨ (k (τ X0) X1) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2658 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2658
  have eq2676 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (M.op X0 X0) = (σ X1) ∨ (k (τ X0) X1) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2675 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2675
  have eq2678 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq2674 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2674
    | (have j0 := eq2674 X0
       grind)
    | exact resolve eq2674 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2674
  have eq2723 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq46 X0
       have i₂ := eq2678 X0
       grind)
    | exact superpose eq2678 eq46
    | (have j1 := eq2678 X0
       grind)
    | exact resolve eq46 eq2678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq2678
  have eq2734 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq2723 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2723
    | (have j0 := eq2723 X0
       grind)
    | exact resolve eq2723 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2723
  have eq2735 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq2734 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2734
  have eq2737 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2735 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2735
    | exact resolve eq2735 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2760 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X0))
       have i₂ := eq2735 X0
       grind)
    | exact superpose eq2735 eq11
    | exact resolve eq11 eq2735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2735
  have eq2802 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2737 X0
       have i₂ := eq34 X0 X0
       grind)
    | exact superpose eq34 eq2737
    | exact resolve eq2737 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2737
  have eq3004 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq2802 X0
       grind)
    | exact superpose eq2802 eq11
    | exact resolve eq11 eq2802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3077 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq3004 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq3004
    | exact resolve eq3004 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3004
  have eq3134 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq34 X0 X0
       have i₂ := eq3077 (τ X0)
       grind)
    | exact superpose eq3077 eq34
    | exact resolve eq34 eq3077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3179 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3134 X0
       have i₂ := eq2802 X0
       grind)
    | exact superpose eq2802 eq3134
    | exact resolve eq3134 eq2802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2802 eq3134
  have eq3636 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ X0) (σ (k X0 X0))) := by
    intro X0
    grind
  have eq3652 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq3636 X0
       have i₂ := eq15 X0 (k X0 X0)
       grind)
    | exact superpose eq15 eq3636
    | exact resolve eq3636 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3636
  have eq3684 : ∀ X0 : G, (σ (k X0 (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq3652 X0
       have i₂ := eq3077 X0
       grind)
    | exact superpose eq3077 eq3652
    | exact resolve eq3652 eq3077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3652
  have eq3699 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  clear eq3684
  have eq27131 : ∀ X0 X1 : G, (σ (σ (τ X0))) ≠ (σ (σ (τ (k X0 X1)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X0)))) ∨ (M.op (σ (σ (τ X0))) (σ (σ (τ X0)))) = (σ (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq748 (τ X0) (τ X1)
       have i₂ := eq34 X1 X0
       grind)
    | exact superpose eq34 eq748
    | (have j0 := eq748 (τ X0) (τ X1)
       grind)
    | exact resolve eq748 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq748
  have eq27202 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (σ (τ X0))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X0)))) ∨ (M.op (σ (σ (τ X0))) (σ (σ (τ X0)))) = (σ (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq27131 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq27131
    | (have j0 := eq27131 X0 X1
       grind)
    | exact resolve eq27131 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27131
  have eq27256 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X0)))) ∨ (M.op (σ (σ (τ X0))) (σ (σ (τ X0)))) = (σ (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq27202 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq27202
    | (have j0 := eq27202 X0 X1
       grind)
    | exact resolve eq27202 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27202
  have eq27308 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (σ (τ X1))) (σ X0)) ∨ (σ X0) ≠ (σ (k X0 X1)) ∨ (M.op (σ (σ (τ X0))) (σ (σ (τ X0)))) = (σ (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq27256 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq27256
    | (have j0 := eq27256 X0 X1
       grind)
    | exact resolve eq27256 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27256
  have eq27356 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) ≠ (σ (k X0 X1)) ∨ (M.op (σ (σ (τ X0))) (σ (σ (τ X0)))) = (σ (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq27308 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq27308
    | (have j0 := eq27308 X0 X1
       grind)
    | exact resolve eq27308 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27308
  have eq27395 : ∀ X0 X1 : G, (σ X1) = (M.op (σ (σ (τ X0))) (σ (σ (τ X0)))) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) ≠ (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq27356 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq27356
    | (have j0 := eq27356 X0 X1
       grind)
    | exact resolve eq27356 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27356
  have eq27430 : ∀ X0 X1 : G, (σ X1) = (σ (k (σ (τ X0)) (σ (τ X0)))) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) ≠ (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq27395 X0 X1
       have i₂ := eq2760 (σ (τ X0))
       grind)
    | exact superpose eq2760 eq27395
    | (have j0 := eq27395 X0 X1
       grind)
    | exact resolve eq27395 eq2760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27395
  have eq27463 : ∀ X0 X1 : G, (σ X1) = (σ (σ (k (τ X0) (τ X0)))) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) ≠ (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq27430 X0 X1
       have i₂ := eq15 (τ X0) (τ X0)
       grind)
    | exact superpose eq15 eq27430
    | (have j0 := eq27430 X0 X1
       grind)
    | exact resolve eq27430 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27430
  have eq27493 : ∀ X0 X1 : G, (σ X1) = (σ (k (σ (τ X0)) X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) ≠ (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq27463 X0 X1
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq27463
    | (have j0 := eq27463 X0 X1
       grind)
    | exact resolve eq27463 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq27463
  have eq27519 : ∀ X0 X1 : G, (σ X1) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) ≠ (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq27493 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq27493
    | (have j0 := eq27493 X0 X1
       grind)
    | exact resolve eq27493 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27493
  have eq27544 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq27519 X0 X1
       have i₂ := eq3077 X0
       grind)
    | exact superpose eq3077 eq27519
    | (have j0 := eq27519 X0 X1
       grind)
    | exact resolve eq27519 eq3077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27519
  have eq32484 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 (σ X1)
       have i₂ := eq2676 (σ X0) X1
       grind)
    | exact superpose eq2676 eq30
    | (have j1 := eq2676 (σ X0) X1
       grind)
    | exact resolve eq30 eq2676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2676
  have eq32577 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq32484 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq32484
    | (have j0 := eq32484 X0 X1
       grind)
    | exact resolve eq32484 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32484
  have eq32660 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq32577 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq32577
    | (have j0 := eq32577 X0 X1
       grind)
    | exact resolve eq32577 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32577
  have eq32735 : ∀ X0 X1 : G, (σ X1) = (σ (k X0 X0)) ∨ (k X0 X1) = X0 ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq32660 X0 X1
       have i₂ := eq2760 X0
       grind)
    | exact superpose eq2760 eq32660
    | (have j0 := eq32660 X0 X1
       grind)
    | exact resolve eq32660 eq2760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32660
  have eq32787 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (k X0 X1) = X0 ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq32735 X0 X1
       have i₂ := eq3077 X0
       grind)
    | exact superpose eq3077 eq32735
    | (have j0 := eq32735 X0 X1
       grind)
    | exact resolve eq32735 eq3077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32735
  have eq32831 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (k X0 X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq32787 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq32787
    | (have j0 := eq32787 X0 X1
       grind)
    | exact resolve eq32787 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32787
  have eq38125 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (σ (τ X1)) = (σ (M.op (τ X0) (τ X0))) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X1)) (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq32831 (τ X1) (τ X0)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq32831
    | (have j0 := eq32831 (τ X0) (τ X1)
       grind)
    | exact resolve eq32831 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq32831
  have eq38450 : ∀ X0 X1 : G, (σ (τ X1)) = (σ (τ (M.op X0 X0))) ∨ (τ X0) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X1)) (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq38125 X0 X1
       have i₂ := eq3179 X0
       grind)
    | exact superpose eq3179 eq38125
    | (have j0 := eq38125 X0 X1
       grind)
    | exact resolve eq38125 eq3179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3179 eq38125
  have eq38592 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (τ X1)) ∨ (τ X0) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X1)) (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq38450 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq38450
    | (have j0 := eq38450 X0 X1
       grind)
    | exact resolve eq38450 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38450
  have eq38709 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (τ X0) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X1)) (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq38592 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq38592
    | (have j0 := eq38592 X0 X1
       grind)
    | exact resolve eq38592 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38592
  have eq38808 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op (σ (τ X1)) X0)) ∨ (M.op X0 X0) = X1 ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq38709 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq38709
    | (have j0 := eq38709 X0 X1
       grind)
    | exact resolve eq38709 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38709
  have eq38888 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X0 X0) = X1 ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq38808 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq38808
    | (have j0 := eq38808 X0 X1
       grind)
    | exact resolve eq38808 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38808
  have eq39640 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ (M.op X1 X1) = X0 ∨ (τ X1) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq38888 X1 X0
       grind)
    | exact superpose eq38888 eq11
    | (have j1 := eq38888 X1 X0
       grind)
    | exact resolve eq11 eq38888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39752 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X1 X0)) ∨ (M.op X0 X0) = X1 ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq38888 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38888
  have eq39830 : ∀ X0 X1 : G, (τ X1) = (τ (k X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq39640 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq39640
    | (have j0 := eq39640 X0 X1
       grind)
    | exact resolve eq39640 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39640
  have eq41004 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq39830 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq39830
    | (have j0 := eq39830 (σ X1) (σ X0)
       grind)
    | exact resolve eq39830 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39830
  have eq41288 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq41004 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq41004
    | (have j0 := eq41004 X0 X1
       grind)
    | exact resolve eq41004 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41004
  have eq41336 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq41288 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq41288
    | (have j0 := eq41288 X0 X1
       grind)
    | exact resolve eq41288 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41288
  have eq41370 : ∀ X0 X1 : G, (σ X1) = (σ (k X0 X0)) ∨ (k X0 X1) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq41336 X0 X1
       have i₂ := eq2760 X0
       grind)
    | exact superpose eq2760 eq41336
    | (have j0 := eq41336 X0 X1
       grind)
    | exact resolve eq41336 eq2760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2760 eq41336
  have eq41398 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (k X0 X1) = X0 ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq41370 X0 X1
       have i₂ := eq3077 X0
       grind)
    | exact superpose eq3077 eq41370
    | (have j0 := eq41370 X0 X1
       grind)
    | exact resolve eq41370 eq3077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3077 eq41370
  have eq45608 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y x) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq41398 y x
       grind)
    | exact superpose eq41398 eq16
    | (have j1 := eq41398 y x
       grind)
    | exact resolve eq16 eq41398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41398
  have eq46115 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ (M.op y y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45608
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq45608
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq45608 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45608
  have eq46121 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq46115
  have eq46122 : y = (M.op x y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq46121
  have eq46873 : (τ y) ≠ (τ y) ∨ x = (M.op y y) ∨ (τ (k y x)) = (τ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq39752 y x
       have i₂ := eq46122
       grind)
    | exact superpose eq46122 eq39752
    | (have j0 := eq39752 y x
       grind)
    | exact resolve eq39752 eq46122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39752
  have eq46877 : (τ y) ≠ (τ y) ∨ x = (M.op y y) ∨ (τ (k y x)) = (τ y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq46873
  have eq46878 : x = (M.op y y) ∨ (τ (k y x)) = (τ y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq46877
  have eq47630 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (τ (k y x)) = (τ y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq3699 y
       have i₂ := eq46878
       grind)
    | exact superpose eq46878 eq3699
    | exact resolve eq3699 eq46878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46878
  have eq47664 : (σ x) = (σ (M.op y y)) ∨ (τ (k y x)) = (τ y) := by
    first
    | (have r₁ := eq47630
       have r₂ := eq16
       grind)
    | exact resolve eq47630 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47630
  have eq47696 : (M.op y y) = (τ (σ x)) ∨ (τ (k y x)) = (τ y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq47664
       grind)
    | exact superpose eq47664 eq10
    | exact resolve eq10 eq47664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47664
  have eq47840 : x = (M.op y y) ∨ (τ (k y x)) = (τ y) := by
    first
    | (have i₁ := eq47696
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq47696
    | exact resolve eq47696 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47696
  have eq48658 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (τ (k y x)) = (τ y) := by
    first
    | (have i₁ := eq3699 y
       have i₂ := eq47840
       grind)
    | exact superpose eq47840 eq3699
    | exact resolve eq3699 eq47840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47840
  have eq48692 : (τ (k y x)) = (τ y) := by
    first
    | (have r₁ := eq48658
       have r₂ := eq16
       grind)
    | exact resolve eq48658 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48658
  have eq48711 : (k y x) = (σ (τ y)) := by
    first
    | (have i₁ := eq11 (k y x)
       have i₂ := eq48692
       grind)
    | exact superpose eq48692 eq11
    | exact resolve eq11 eq48692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48692
  have eq48913 : y = (k y x) := by
    first
    | (have i₁ := eq48711
       have i₂ := eq11 y
       grind)
    | exact superpose eq11 eq48711
    | exact resolve eq48711 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48711
  have eq49713 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq27544 y x
       have i₂ := eq48913
       grind)
    | exact superpose eq48913 eq27544
    | (have j0 := eq27544 y x
       grind)
    | exact resolve eq27544 eq48913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27544 eq48913
  have eq49714 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq49713
  have eq53866 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq49714
       grind)
    | exact superpose eq49714 eq16
    | exact resolve eq16 eq49714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49714
  have eq53882 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq53866
       have i₂ := eq46122
       grind)
    | exact superpose eq46122 eq53866
    | exact resolve eq53866 eq46122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46122 eq53866
  have eq53883 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq53882
  have eq53884 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq53883
  have eq54350 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq3699 y
       have i₂ := eq53884
       grind)
    | exact superpose eq53884 eq3699
    | exact resolve eq3699 eq53884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53884
  have eq54384 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq54350
       have r₂ := eq16
       grind)
    | exact resolve eq54350 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54350
  have eq54418 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq54384
       grind)
    | exact superpose eq54384 eq10
    | exact resolve eq10 eq54384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54384
  have eq54572 : x = (M.op y y) := by
    first
    | (have i₁ := eq54418
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq54418
    | exact resolve eq54418 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54418
  have eq55217 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3699 y
       have i₂ := eq54572
       grind)
    | exact superpose eq54572 eq3699
    | exact resolve eq3699 eq54572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3699 eq54572
  have eq55251 : False := by grind
  exact eq55251
