import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4439`: `x ◇ (y ◇ x) = (x ◇ z) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxy_y_pyx_x_pxy_Equation4439 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4439 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4439.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X2) X1) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
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
  have eq28 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y) X0
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 X0 (M.op x y)
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq33 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq28 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq28
    | (have j0 := eq28 x
       grind)
    | exact resolve eq28 eq22
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
  have eq41 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq29 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq29
    | (have j0 := eq29 x
       grind)
    | exact resolve eq29 eq22
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
  have eq49 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X3) (M.op X0 X2)) = (M.op X1 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 (M.op X0 X2) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 X2 X3
       have i₂ := eq9 X0 X2 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op x (M.op X0 x)) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq9 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9
    | (have j0 := eq9 x X0 y
       grind)
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X3 X0)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 X3 (M.op X2 X0)
       have i₂ := eq9 X0 X2 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ x))) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq26 eq9
    | (have j0 := eq9 (σ x) X0 (σ y)
       grind)
    | exact resolve eq9 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq30 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq30
    | (have j0 := eq30 x
       grind)
    | exact resolve eq30 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq65 : (σ (k x y)) = (k (σ x) (σ y)) := by
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
  have eq70 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq80 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op x X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 x X0 X1
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq9
    | exact resolve eq9 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X1 (M.op x y))) = (M.op (M.op x (M.op X0 x)) X1) := by
    intro X0 X1
    first
    | exact superpose eq54 eq9
    | exact resolve eq9 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X1 : G, (M.op (M.op x y) X1) = (M.op (M.op x y) (M.op X1 (M.op x y))) := by
    intro X1
    first
    | (have i₁ := eq82 x X1
       have i₂ := eq80 X1 (M.op x x)
       grind)
    | exact superpose eq80 eq82
    | exact resolve eq82 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq86 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (σ x) X1) X0) := by
    intro X0 X1
    first
    | exact superpose eq57 eq9
    | exact resolve eq9 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (M.op X0 (σ x))) X1) := by
    intro X0 X1
    first
    | exact superpose eq57 eq9
    | exact resolve eq9 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) X1) = (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op (σ x) (σ y)))) := by
    intro X1
    first
    | exact superpose eq86 eq88
    | exact resolve eq88 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq91 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (M.op (M.op (M.op x y) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq80 X1 (M.op X0 x)
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq80
    | exact resolve eq80 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : ∀ X0 X1 X2 : G, (M.op (M.op x y) (M.op X0 (M.op x X1))) = (M.op (M.op (M.op x X1) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op x X1) X0 X2
       have i₂ := eq80 (M.op X0 (M.op x X1)) X1
       grind)
    | (have i₁ := eq9 (M.op x y) X1 X2
       have i₂ := eq80 (M.op X1 (M.op x y)) X1
       grind)
    | exact superpose eq80 eq9
    | exact resolve eq9 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : ∀ X0 X1 X2 : G, (M.op (M.op x y) (M.op X0 (M.op x X1))) = (M.op (M.op (M.op x y) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq98 X0 X1 X2
       have i₂ := eq80 X2 X1
       grind)
    | (have i₁ := eq98 X0 y X0
       have i₂ := eq80 X0 X1
       grind)
    | exact superpose eq80 eq98
    | exact resolve eq98 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq109 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op x y) (M.op X0 (M.op x X1))) := by
    intro X0 X1
    first
    | exact superpose eq91 eq103
    | exact resolve eq103 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq103
  have eq125 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X1) = (M.op (M.op (M.op (σ x) (σ y)) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq57 eq86
    | exact resolve eq86 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op X0 X2) (M.op (σ x) X1)) := by
    intro X0 X1 X2
    first
    | exact superpose eq86 eq9
    | exact resolve eq9 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) X1))) = (M.op (M.op (M.op (σ x) X1) X2) X0) := by
    intro X0 X1 X2
    first
    | exact superpose eq86 eq9
    | exact resolve eq9 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) X1))) = (M.op (M.op (M.op (σ x) (σ y)) X2) X0) := by
    intro X0 X1 X2
    first
    | exact superpose eq86 eq132
    | exact resolve eq132 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq140 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) = (M.op X0 (M.op (σ x) (M.op X0 (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq131 x x x
       have i₂ := eq52 sF2 x x x
       grind)
    | exact superpose eq52 eq131
    | exact resolve eq131 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq145 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) X1))) := by
    intro X0 X1
    first
    | exact superpose eq125 eq139
    | exact resolve eq139 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq139
  have eq164 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) ≠ (M.op X0 X2) ∨ (M.op X1 (M.op X0 X2)) = (k (M.op X0 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X0 X2) X1
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 (M.op X0 X2) X1
       grind)
    | (have r₁ := eq12 (M.op X0 (M.op X1 X0)) X1
       have r₂ := eq9 X0 X1 (M.op X1 X0)
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq167 : x ≠ (M.op x y) ∨ (k x y) = (M.op y x) := by
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
  have eq171 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq173 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ x) (M.op X0 (σ x))) ∨ (M.op X0 (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq57 eq12
    | (have j0 := eq12 (M.op (σ x) (σ y)) X0
       grind)
    | exact resolve eq12 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ (k x y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq65 eq171
    | exact resolve eq171 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171
  have eq185 : y ≠ (M.op x y) ∨ x = (M.op x y) ∨ x = (k x y) := by
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
  have eq189 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq65 eq189
    | exact resolve eq189 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq306 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) (τ X2))) = (k (k (σ X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq48 X2 (k X0 (τ X1))
       have i₂ := eq48 X1 X0
       grind)
    | exact superpose eq48 eq48
    | exact resolve eq48 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq311 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq332 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k (τ X0) X1) X2
       have i₂ := eq49 X0 X1
       grind)
    | exact superpose eq49 eq15
    | exact resolve eq15 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq350 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq311 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq311
    | exact resolve eq311 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311
  have eq508 : ∀ X0 X1 X2 : G, (M.op (M.op x y) (M.op (M.op X0 X1) (M.op x y))) = (M.op (M.op x y) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq83 (M.op X0 X1)
       have i₂ := eq53 X0 X1 sF0 x
       grind)
    | (have i₁ := eq83 (M.op X0 x)
       have i₂ := eq53 X0 X1 sF0 x
       grind)
    | exact superpose eq53 eq83
    | exact resolve eq83 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq510 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 X1) (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (σ y)) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq90 (M.op X0 X1)
       have i₂ := eq53 X0 X1 sF4 x
       grind)
    | (have i₁ := eq90 (M.op X0 x)
       have i₂ := eq53 X0 X1 sF4 x
       grind)
    | exact superpose eq53 eq90
    | exact resolve eq90 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq511 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq90 eq510
    | exact resolve eq510 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq510
  have eq513 : ∀ X0 X1 X2 : G, (M.op (M.op x y) (M.op X0 X1)) = (M.op (M.op x y) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq83 eq508
    | exact resolve eq508 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq508
  have eq555 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq570 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq65
       have i₂ := eq14 sF2 sF3
       grind)
    | exact superpose eq14 eq65
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq65 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq571 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq70
       have i₂ := eq14 sF3 sF3
       grind)
    | exact superpose eq14 eq70
    | (have j1 := eq14 (σ y) (σ y)
       grind)
    | exact resolve eq70 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq572 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq571
  have eq578 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq570
    | exact resolve eq570 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570
  have eq580 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq578
    | exact resolve eq578 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578
  have eq582 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq580
    | exact resolve eq580 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580
  have eq764 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | exact superpose eq511 eq145
    | exact resolve eq145 eq511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145 eq511
  have eq1134 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op x y) (M.op X0 X1)) := by
    intro X0 X1
    first
    | exact superpose eq513 eq109
    | exact resolve eq109 eq513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq513
  have eq1544 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq582
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq582
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq582 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1547 : ∀ X0 : G, (σ (k X0 (k x y))) = (k (σ X0) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 (k x y)
       have i₂ := eq582
       grind)
    | exact superpose eq582 eq15
    | exact resolve eq15 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1549 : (σ (k (k x y) (M.op x y))) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq29 (k x y)
       have i₂ := eq582
       grind)
    | exact superpose eq582 eq29
    | exact resolve eq29 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq1554 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1544
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1544
    | exact resolve eq1544 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1544
  have eq1555 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq1554
    | exact resolve eq1554 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1554
  have eq1556 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1555
       have r₂ := eq27
       grind)
    | exact resolve eq1555 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1555
  have eq1557 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1556
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1556
    | exact resolve eq1556 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1556
  have eq1558 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1557
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1557
    | exact resolve eq1557 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1557
  have eq1563 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1558 eq193
    | (have r₁ := eq193
       have r₂ := eq1558
       grind)
    | exact resolve eq193 eq1558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1567 : (σ x) ≠ (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1558
  have eq1568 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1563
  have eq1569 : (σ x) = (σ (k x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1568
       have r₂ := eq1567
       grind)
    | exact resolve eq1568 eq1567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1567 eq1568
  have eq1652 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X2) (M.op X1 (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X2) X1 x
       have i₂ := eq55 X0 X2 x X1
       grind)
    | exact superpose eq55 eq9
    | exact resolve eq9 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq2101 : (τ (σ x)) = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq1569
       grind)
    | exact superpose eq1569 eq10
    | exact resolve eq10 eq1569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1569
  have eq2120 : x = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq38 eq2101
    | exact resolve eq2101 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2101
  have eq2122 : x = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq2120
       have r₂ := eq185
       grind)
    | exact resolve eq2120 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2120
  have eq2130 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq582
       have i₂ := eq2122
       grind)
    | exact superpose eq2122 eq582
    | exact resolve eq582 eq2122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2131 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq2122
       grind)
    | exact superpose eq2122 eq14
    | (have j0 := eq14 x y
       grind)
    | exact resolve eq14 eq2122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2122
  have eq2133 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2131
  have eq2134 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2130
  have eq2137 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2133
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2133
    | exact resolve eq2133 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2133
  have eq2138 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2137
  have eq2139 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2134
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2134
    | exact resolve eq2134 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2134
  have eq2140 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2139
  have eq2143 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2138
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2138
    | exact resolve eq2138 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2138
  have eq2145 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2140 eq27
    | exact resolve eq27 eq2140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2140
  have eq2162 : (σ x) ≠ (σ x) ∨ (σ (k x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2143 eq177
    | (have r₁ := eq177
       have r₂ := eq2143
       grind)
    | exact resolve eq177 eq2143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2163 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) (M.op X0 X1)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq2143 eq764
    | exact resolve eq764 eq2143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2165 : (σ (k x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq2162
  have eq2418 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 X1))) = (k (M.op X1 (M.op X0 X1)) X0) := by
    intro X0 X1
    first
    | (have j0 := eq164 X1 X0 (M.op X0 X1)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164
  have eq2476 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2165
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq2165
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq2165 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2165
  have eq2497 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2476
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2476
    | exact resolve eq2476 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2476
  have eq2498 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq2497
    | exact resolve eq2497 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2497
  have eq2499 : y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2498
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2498
    | exact resolve eq2498 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2498
  have eq2500 : y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq2499
  have eq2501 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2500
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2500
    | exact resolve eq2500 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2500
  have eq2502 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq2501
  have eq2503 : ∀ X0 : G, (M.op (σ y) (M.op X0 (σ y))) = (M.op (σ (M.op x y)) X0) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2502 eq9
    | exact resolve eq9 eq2502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3195 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2502 eq2163
    | exact resolve eq2163 eq2502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2163
  have eq3245 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq3195
  have eq3264 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq3245
    | exact resolve eq3245 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3245
  have eq3272 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3264 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq3264
       grind)
    | exact resolve eq12 eq3264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3293 : (k (σ x) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq3272
       have r₂ := eq2143
       grind)
    | exact resolve eq3272 eq2143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3272
  have eq3296 : (σ (k x (M.op x y))) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq41 eq3293
    | exact resolve eq3293 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq3293
  have eq3349 : (k x (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ x))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3296 eq10
    | exact resolve eq10 eq3296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3296
  have eq5003 : (M.op (σ (M.op x y)) (σ x)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq2503
    | (have j0 := eq2503 (σ x)
       grind)
    | exact resolve eq2503 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2503
  have eq5105 : (M.op (σ y) (σ x)) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2143 eq5003
    | exact resolve eq5003 eq2143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5003
  have eq5142 : (M.op (σ y) (σ x)) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq5105
  have eq5276 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5142 eq2502
    | exact resolve eq2502 eq5142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2502 eq5142
  have eq5303 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq5276
  have eq5316 : (τ (σ (M.op x y))) = (k x (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5303 eq3349
    | exact resolve eq3349 eq5303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3349
  have eq5319 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k (σ (M.op x y)) (σ x)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5303 eq12
    | (have j0 := eq12 (σ (M.op x y)) (σ x)
       grind)
    | (have r₁ := eq12 (σ (M.op x y)) (σ x)
       have r₂ := eq5303
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq5303
       grind)
    | exact resolve eq12 eq5303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5303
  have eq5329 : (k (σ (M.op x y)) (σ x)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq5319
  have eq5331 : (τ (σ (M.op x y))) = (k x (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq5316
  have eq5333 : (σ (k (M.op x y) x)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq33 eq5329
    | exact resolve eq5329 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq5329
  have eq5334 : (M.op x y) = (k x (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq37 eq5331
    | exact resolve eq5331 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5331
  have eq5338 : (M.op x y) = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5334 eq14
    | (have j0 := eq14 x (M.op x y)
       grind)
    | exact resolve eq14 eq5334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5340 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq5338
  have eq5928 : (k (M.op x y) x) = (τ (M.op (σ x) (σ (M.op x y)))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5333 eq10
    | exact resolve eq10 eq5333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5333
  have eq6021 : (k (M.op x y) x) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3264 eq5928
    | exact resolve eq5928 eq3264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3264 eq5928
  have eq6026 : (k (M.op x y) x) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq6021
  have eq6029 : (k (M.op x y) x) = (τ (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2143 eq6026
    | exact resolve eq6026 eq2143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2143 eq6026
  have eq6038 : (k (M.op x y) x) = (τ (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq6029
  have eq6041 : x = (k (M.op x y) x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38 eq6038
    | exact resolve eq6038 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6038
  have eq8824 : ∀ X0 X1 X2 : G, (k (σ (k X0 (τ X1))) X2) = (k (k (σ X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq48 X2 (k X0 (τ X1))
       have i₂ := eq306 X0 X1 X2
       grind)
    | exact superpose eq306 eq48
    | exact resolve eq48 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12654 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ x = (k x (M.op x y)) ∨ x = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5340 eq13
    | (have j0 := eq13 x (M.op x y)
       grind)
    | (have r₁ := eq13 x (M.op x y)
       have r₂ := eq5340
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq5340
       grind)
    | exact resolve eq13 eq5340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5340
  have eq12675 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ x = (k x (M.op x y)) ∨ x = (M.op x (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq12654
  have eq12676 : x = (k x (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq12675
  have eq14875 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12676 eq5334
    | exact resolve eq5334 eq12676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12676
  have eq14907 : x = (M.op x (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq14875
  have eq14923 : x ≠ x ∨ (k x (M.op x y)) = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14907 eq12
    | (have j0 := eq12 x (M.op x y)
       grind)
    | (have r₁ := eq12 x (M.op x y)
       have r₂ := eq14907
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq14907
       grind)
    | exact resolve eq12 eq14907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14907
  have eq14941 : (k x (M.op x y)) = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq14923
  have eq14950 : (k x (M.op x y)) = (M.op x (M.op x x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq54 eq14941
    | exact resolve eq14941 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14941
  have eq16430 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X1 X0 (M.op X0 x) x
       have i₂ := eq1652 X0 X1 x
       grind)
    | exact superpose eq1652 eq52
    | exact resolve eq52 eq1652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1652
  have eq16546 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X3) (M.op X0 X2)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 X0 X1 X2 X3
       have i₂ := eq16430 X1 X0
       grind)
    | exact superpose eq16430 eq52
    | exact resolve eq52 eq16430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq16565 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (k (M.op X1 (M.op X0 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2418 X0 X1
       have i₂ := eq16430 X0 X1
       grind)
    | exact superpose eq16430 eq2418
    | exact resolve eq2418 eq16430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2418
  have eq16597 : ∀ X0 : G, (M.op X0 (M.op (σ x) X0)) = (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq140 X0
       have i₂ := eq16430 X0 sF2
       grind)
    | exact superpose eq16430 eq140
    | exact resolve eq140 eq16430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140 eq16430
  have eq19043 : (M.op x (M.op y x)) = (k (M.op y (M.op x y)) x) := by
    first
    | (have i₁ := eq16565 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16565
    | (have j0 := eq16565 x y
       grind)
    | exact resolve eq16565 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19148 : ∀ X0 : G, (M.op X0 (M.op x X0)) = (k (M.op (M.op x y) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq16565 X0 x
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq16565
    | exact resolve eq16565 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28481 : (M.op x y) = (M.op x (M.op x x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14950 eq5334
    | exact resolve eq5334 eq14950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5334 eq14950
  have eq28513 : (M.op x y) = (M.op x (M.op x x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq28481
  have eq28529 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16565 x x
       have i₂ := eq28513
       grind)
    | exact superpose eq28513 eq16565
    | exact resolve eq16565 eq28513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28513
  have eq28635 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28529 eq6041
    | exact resolve eq6041 eq28529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6041 eq28529
  have eq28655 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq28635
  have eq28663 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28655 eq20
    | exact resolve eq20 eq28655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28664 : ∀ X0 : G, (M.op y X0) = (M.op x (M.op X0 x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq28655 eq54
    | exact resolve eq54 eq28655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28667 : y ≠ y ∨ x = y ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28655 eq185
    | (have r₁ := eq185
       have r₂ := eq28655
       grind)
    | exact resolve eq185 eq28655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq28671 : ∀ X0 X1 : G, (M.op y X0) = (M.op y (M.op X0 X1)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq28655 eq1134
    | exact resolve eq1134 eq28655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28677 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq28678 : x = y ∨ x = (k x y) ∨ x = (M.op x y) := by grind
  clear eq28667
  have eq28684 : x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq28678
       have r₂ := eq28677
       grind)
    | exact resolve eq28678 eq28677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28678
  have eq28686 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq28663
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq28663
    | exact resolve eq28663 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq28663
  have eq28701 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28686 eq2145
    | (have r₁ := eq2145
       have r₂ := eq28686
       grind)
    | exact resolve eq2145 eq28686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2145 eq28686
  have eq28869 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq28701
  have eq28870 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq28869
  have eq28889 : (σ x) ≠ (σ x) ∨ (σ (k x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28870 eq177
    | (have r₁ := eq177
       have r₂ := eq28870
       grind)
    | exact resolve eq177 eq28870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq28890 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) (M.op X0 X1)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq28870 eq764
    | exact resolve eq764 eq28870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764
  have eq29023 : (σ (k x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq28889
  have eq30524 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq29023
       have i₂ := eq28684
       grind)
    | exact superpose eq28684 eq29023
    | exact resolve eq29023 eq28684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28684 eq29023
  have eq30575 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq30524
  have eq30580 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq30575
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq30575
    | exact resolve eq30575 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30575
  have eq36254 : ∀ X0 : G, (M.op y X0) = (M.op (M.op x y) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq54 X0
       have i₂ := eq28664 X0
       grind)
    | exact superpose eq28664 eq54
    | exact resolve eq54 eq28664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq28664
  have eq38517 : (M.op y x) = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq28671 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28671
    | (have j0 := eq28671 x y
       grind)
    | exact resolve eq28671 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28671
  have eq38810 : (M.op y x) = (M.op y y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq28655 eq38517
    | exact resolve eq38517 eq28655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28655 eq38517
  have eq38871 : (M.op y x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq38810
       have r₂ := eq28677
       grind)
    | exact resolve eq38810 eq28677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28677 eq38810
  have eq44280 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30580 eq28890
    | exact resolve eq28890 eq30580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28890 eq30580
  have eq44535 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq44280
  have eq44653 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq44535
    | exact resolve eq44535 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44535
  have eq44690 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq44653 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq44653
       grind)
    | exact resolve eq12 eq44653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44653
  have eq44781 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq44690
       have r₂ := eq28870
       grind)
    | exact resolve eq44690 eq28870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44690
  have eq44807 : (M.op (σ x) (σ y)) = (σ (k x x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq59 eq44781
    | exact resolve eq44781 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq44781
  have eq45053 : (k x x) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k x x)
       have i₂ := eq44807
       grind)
    | exact superpose eq44807 eq10
    | exact resolve eq10 eq44807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44807
  have eq45071 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28870 eq45053
    | exact resolve eq45053 eq28870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28870 eq45053
  have eq45120 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) := by grind
  clear eq45071
  have eq45122 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38 eq45120
    | exact resolve eq45120 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq45120
  have eq45126 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14 x x
       have i₂ := eq45122
       grind)
    | exact superpose eq45122 eq14
    | (have j0 := eq14 x x
       grind)
    | exact resolve eq14 eq45122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45122
  have eq45128 : x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq45126
  have eq45138 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq80 X0 x
       have i₂ := eq45128
       grind)
    | exact superpose eq45128 eq80
    | exact resolve eq80 eq45128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq46293 : ∀ X0 : G, (M.op y X0) = (M.op x X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq45138 eq36254
    | exact resolve eq36254 eq45138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36254 eq45138
  have eq46425 : ∀ X0 : G, (M.op y X0) = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq46293 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46293
  have eq48882 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq38871
       have i₂ := eq46425 y
       grind)
    | exact superpose eq46425 eq38871
    | exact resolve eq38871 eq46425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38871
  have eq49006 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq48882
  have eq49089 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq49006
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq49006
    | exact resolve eq49006 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49006
  have eq49135 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq46425 x
       have i₂ := eq49089
       grind)
    | exact superpose eq49089 eq46425
    | exact resolve eq46425 eq49089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46425 eq49089
  have eq49199 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq49135
  have eq49430 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq45128
       have i₂ := eq49199
       grind)
    | exact superpose eq49199 eq45128
    | exact resolve eq45128 eq49199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45128 eq49199
  have eq49493 : x = (M.op x y) := by grind
  clear eq49430
  have eq49530 : x = (M.op x y) := by
    first
    | exact superpose eq49493 eq18
    | exact resolve eq18 eq49493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq49531 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq49493 eq20
    | exact resolve eq20 eq49493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq49532 : ∀ X0 : G, (k (σ (M.op x y)) (σ X0)) = (σ (k x X0)) := by
    intro X0
    first
    | exact superpose eq49493 eq28
    | exact resolve eq28 eq49493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq49537 : x = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq49493 eq37
    | exact resolve eq37 eq49493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq49544 : x ≠ x ∨ (k x y) = (M.op y x) := by
    first
    | exact superpose eq49493 eq167
    | (have r₁ := eq167
       have r₂ := eq49493
       grind)
    | exact resolve eq167 eq49493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq49572 : ∀ X0 X1 : G, (M.op x X0) = (M.op x (M.op X0 X1)) := by
    intro X0 X1
    first
    | exact superpose eq49493 eq1134
    | exact resolve eq1134 eq49493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1134
  have eq49579 : (k (M.op (σ x) (σ y)) (σ (M.op x y))) = (σ (k (k x y) x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq49493 eq1549
    | exact resolve eq1549 eq49493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1549
  have eq49723 : (M.op x (M.op y x)) = (k (M.op y x) x) := by
    first
    | exact superpose eq49493 eq19043
    | exact resolve eq19043 eq49493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19043
  have eq49724 : ∀ X0 : G, (M.op X0 (M.op x X0)) = (k (M.op x X0) X0) := by
    intro X0
    first
    | exact superpose eq49493 eq19148
    | exact resolve eq19148 eq49493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19148 eq49493
  have eq49769 : (k x y) = (M.op y x) := by grind
  clear eq49544
  have eq49818 : (M.op x y) = (k (M.op y x) x) := by
    first
    | (have i₁ := eq49723
       have i₂ := eq49572 y x
       grind)
    | exact superpose eq49572 eq49723
    | exact resolve eq49723 eq49572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49723
  have eq49837 : (σ x) = (σ (M.op y x)) ∨ (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq193
       have i₂ := eq49769
       grind)
    | exact superpose eq49769 eq193
    | exact resolve eq193 eq49769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq49838 : (M.op (σ x) (σ y)) = (σ (M.op y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq582
       have i₂ := eq49769
       grind)
    | exact superpose eq49769 eq582
    | exact resolve eq582 eq49769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582
  have eq49841 : ∀ X0 : G, (k (σ X0) (M.op (σ x) (σ y))) = (σ (k X0 (M.op y x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1547 X0
       have i₂ := eq49769
       grind)
    | exact superpose eq49769 eq1547
    | exact resolve eq1547 eq49769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1547
  have eq49853 : (k (M.op (σ x) (σ y)) (σ (M.op x y))) = (σ (k (M.op y x) x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq49579
       have i₂ := eq49769
       grind)
    | exact superpose eq49769 eq49579
    | exact resolve eq49579 eq49769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49579 eq49769
  have eq49856 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq49531
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq49531
    | exact resolve eq49531 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49531
  have eq49878 : x = (k (M.op y x) x) := by
    first
    | (have i₁ := eq49818
       have i₂ := eq49530
       grind)
    | exact superpose eq49530 eq49818
    | exact resolve eq49818 eq49530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49818
  have eq49896 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq49856 eq22
    | exact resolve eq22 eq49856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq49897 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq49856 eq26
    | exact resolve eq26 eq49856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq49901 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (σ (M.op x y)) (M.op X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq49856 eq57
    | exact resolve eq57 eq49856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq49904 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (σ (M.op x y)) X1) X0) := by
    intro X0 X1
    first
    | exact superpose eq49856 eq86
    | exact resolve eq86 eq49856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq49906 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ (M.op x y)) (M.op X0 (σ (M.op x y)))) ∨ (M.op X0 (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq49856 eq173
    | (have j0 := eq173 X0
       grind)
    | exact resolve eq173 eq49856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173
  have eq50022 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) = (M.op X0 (M.op (σ (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq49856 eq16597
    | exact resolve eq16597 eq49856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16597
  have eq50105 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y x)) ∨ (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq49856 eq49837
    | exact resolve eq49837 eq49856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49837
  have eq50106 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq49856 eq49838
    | exact resolve eq49838 eq49856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49838
  have eq50109 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (k (σ X0) (M.op (σ x) (σ y))) = (σ (k X0 (M.op y x))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq49856 eq49841
    | (have j0 := eq49841 X0
       grind)
    | exact resolve eq49841 eq49856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49841
  have eq50120 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (k (M.op (σ x) (σ y)) (σ (M.op x y))) = (σ (k (M.op y x) x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq49856 eq49853
    | exact resolve eq49853 eq49856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49853
  have eq50140 : (k (M.op (σ x) (σ y)) (σ (M.op x y))) = (σ (k (M.op y x) x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq50120
       have r₂ := eq27
       grind)
    | exact resolve eq50120 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50120
  have eq50151 : ∀ X0 : G, (k (σ X0) (M.op (σ x) (σ y))) = (σ (k X0 (M.op y x))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq50109 X0
       grind)
    | (have r₁ := eq50109 X0
       have r₂ := eq27
       grind)
    | exact resolve eq50109 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50109
  have eq50154 : (M.op (σ x) (σ y)) = (σ (M.op y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq50106
       have r₂ := eq27
       grind)
    | exact resolve eq50106 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50106
  have eq50155 : (σ x) = (σ (M.op y x)) ∨ (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq50105
       have r₂ := eq27
       grind)
    | exact resolve eq50105 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50105
  have eq50222 : (σ x) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq50140
       have i₂ := eq49878
       grind)
    | exact superpose eq49878 eq50140
    | exact resolve eq50140 eq49878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50140
  have eq50226 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ (M.op y x)) := by
    first
    | exact superpose eq49856 eq50155
    | exact resolve eq50155 eq49856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49856 eq50155
  have eq50246 : (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq50222
       have i₂ := eq49896
       grind)
    | exact superpose eq49896 eq50222
    | exact resolve eq50222 eq49896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50222
  have eq50459 : (σ x) = (M.op (σ (M.op y x)) (σ x)) ∨ (σ x) = (M.op (σ (M.op y x)) (σ x)) ∨ (σ (M.op y x)) = (M.op (σ (M.op y x)) (σ x)) := by
    first
    | (have i₁ := eq555 (M.op y x) x
       have i₂ := eq49878
       grind)
    | exact superpose eq49878 eq555
    | (have j0 := eq555 (M.op y x) x
       grind)
    | exact resolve eq555 eq49878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555 eq49878
  have eq50463 : (σ x) = (M.op (σ (M.op y x)) (σ x)) ∨ (σ (M.op y x)) = (M.op (σ (M.op y x)) (σ x)) := by grind
  clear eq50459
  have eq50467 : (σ (M.op x y)) = (M.op (σ (M.op y x)) (σ (M.op x y))) ∨ (σ (M.op y x)) = (M.op (σ (M.op y x)) (σ x)) := by
    first
    | (have i₁ := eq50463
       have i₂ := eq49896
       grind)
    | exact superpose eq49896 eq50463
    | exact resolve eq50463 eq49896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50463
  have eq50470 : (σ (M.op y x)) = (M.op (σ (M.op y x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op y x)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq50467
       have i₂ := eq49896
       grind)
    | exact superpose eq49896 eq50467
    | exact resolve eq50467 eq49896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50467
  have eq50623 : (τ (σ (M.op x y))) = (k (τ (M.op (σ x) (σ y))) (τ (σ (M.op x y)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq50246 eq350
    | exact resolve eq350 eq50246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50627 : x = (k (τ (M.op (σ x) (σ y))) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq49537 eq50623
    | exact resolve eq50623 eq49537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50623
  have eq52049 : (τ x) = (k (τ (τ (M.op (σ x) (σ y)))) (τ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq50627 eq350
    | exact resolve eq350 eq50627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50627
  have eq52279 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op x X0)) = (k (M.op x X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq49724 (M.op X0 X1)
       have i₂ := eq49572 X0 X1
       grind)
    | exact superpose eq49572 eq49724
    | exact resolve eq49724 eq49572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49572 eq49724
  have eq52301 : ∀ X0 X1 : G, (M.op X0 (M.op x X0)) = (k (M.op x X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq52279 X0 X1
       have i₂ := eq16546 x X0 X0 X1
       grind)
    | exact superpose eq16546 eq52279
    | exact resolve eq52279 eq16546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16546 eq52279
  have eq53000 : ∀ X0 : G, (σ (k (τ x) (τ X0))) = (k (k (σ (τ (τ (M.op (σ x) (σ y))))) x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq52049 eq306
    | exact resolve eq306 eq52049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306 eq52049
  have eq53015 : ∀ X0 : G, (σ (k (τ x) (τ X0))) = (k (σ (k (τ (τ (M.op (σ x) (σ y)))) (τ x))) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq53000 x
       have i₂ := eq8824 (τ (τ sF4)) x x
       grind)
    | exact superpose eq8824 eq53000
    | exact resolve eq53000 eq8824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8824 eq53000
  have eq53019 : ∀ X0 : G, (σ (k (τ x) (τ X0))) = (k (k (τ (M.op (σ x) (σ y))) (σ (τ x))) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq53015 X0
       have i₂ := eq49 (τ sF4) (τ x)
       grind)
    | exact superpose eq49 eq53015
    | exact resolve eq53015 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53015
  have eq53021 : ∀ X0 : G, (σ (k (τ x) (τ X0))) = (k (k (τ (M.op (σ x) (σ y))) x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq53019 X0
       have i₂ := eq11 x
       grind)
    | exact superpose eq11 eq53019
    | exact resolve eq53019 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53019
  have eq53023 : ∀ X0 : G, (k x (σ (τ X0))) = (k (k (τ (M.op (σ x) (σ y))) x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq53021 X0
       have i₂ := eq49 x (τ X0)
       grind)
    | exact superpose eq49 eq53021
    | exact resolve eq53021 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53021
  have eq53024 : ∀ X0 : G, (k x X0) = (k (k (τ (M.op (σ x) (σ y))) x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq53023 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq53023
    | exact resolve eq53023 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53023
  have eq53447 : ∀ X0 : G, (M.op y x) = (k x (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq52301 y x
       have i₂ := eq49530
       grind)
    | exact superpose eq49530 eq52301
    | exact resolve eq52301 eq49530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49530 eq52301
  have eq54291 : ∀ X0 : G, (σ (k x (τ X0))) = (k (σ (k (τ (M.op (σ x) (σ y))) x)) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq53024 eq48
    | exact resolve eq48 eq53024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53024
  have eq54313 : ∀ X0 : G, (σ (k x (τ X0))) = (k (k (M.op (σ x) (σ y)) (σ x)) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq54291 X0
       have i₂ := eq49 sF4 x
       grind)
    | exact superpose eq49 eq54291
    | exact resolve eq54291 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54291
  have eq54328 : ∀ X0 : G, (σ (k x (τ X0))) = (k (k (M.op (σ x) (σ y)) (σ (M.op x y))) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq54313 X0
       have i₂ := eq49896
       grind)
    | exact superpose eq49896 eq54313
    | exact resolve eq54313 eq49896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54313
  have eq54339 : ∀ X0 : G, (k (σ x) X0) = (k (k (M.op (σ x) (σ y)) (σ (M.op x y))) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq54328 X0
       have i₂ := eq48 X0 x
       grind)
    | exact superpose eq48 eq54328
    | exact resolve eq54328 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54328
  have eq54349 : ∀ X0 : G, (k (σ (M.op x y)) X0) = (k (k (M.op (σ x) (σ y)) (σ (M.op x y))) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq54339 X0
       have i₂ := eq49896
       grind)
    | exact superpose eq49896 eq54339
    | exact resolve eq54339 eq49896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54339
  have eq54973 : ∀ X0 : G, (k X0 (M.op (σ x) (σ y))) = (σ (k (τ X0) (M.op y x))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq50151 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq50151
    | exact resolve eq50151 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54995 : ∀ X0 : G, (σ (k X0 (τ (M.op (σ x) (σ y))))) = (σ (k X0 (M.op y x))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq50151 eq48
    | exact resolve eq48 eq50151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq50151
  have eq55019 : ∀ X0 : G, (k X0 (M.op (σ x) (σ y))) = (k X0 (σ (M.op y x))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq54973 X0
       have i₂ := eq49 X0 (M.op y x)
       grind)
    | exact superpose eq49 eq54973
    | exact resolve eq54973 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq54973
  have eq55044 : (k (σ (M.op x y)) (σ (M.op y x))) = (k (k (M.op (σ x) (σ y)) (σ (M.op x y))) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq54349 (σ (M.op y x))
       have i₂ := eq55019 (k sF4 sF1)
       grind)
    | exact superpose eq55019 eq54349
    | exact resolve eq54349 eq55019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55019
  have eq55065 : (k (σ (M.op x y)) (σ (M.op y x))) = (k (k (M.op (σ x) (σ y)) (σ (M.op x y))) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq55044
  have eq55084 : (σ (k x (M.op y x))) = (k (k (M.op (σ x) (σ y)) (σ (M.op x y))) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq49532 eq55065
    | exact resolve eq55065 eq49532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49532 eq55065
  have eq55094 : (σ (M.op y x)) = (k (k (M.op (σ x) (σ y)) (σ (M.op x y))) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq55084
       have i₂ := eq53447 x
       grind)
    | exact superpose eq53447 eq55084
    | exact resolve eq55084 eq53447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53447 eq55084
  have eq55485 : (τ (σ (M.op y x))) = (k (τ (k (M.op (σ x) (σ y)) (σ (M.op x y)))) (τ (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq55094 eq350
    | exact resolve eq350 eq55094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55094
  have eq55489 : (τ (σ (M.op y x))) = (k (k (τ (M.op (σ x) (σ y))) (τ (σ (M.op x y)))) (τ (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq55485
       have i₂ := eq350 sF4 sF1
       grind)
    | exact superpose eq350 eq55485
    | exact resolve eq55485 eq350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350 eq55485
  have eq55491 : (τ (σ (M.op y x))) = (k (k (τ (M.op (σ x) (σ y))) x) (τ (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq49537 eq55489
    | exact resolve eq55489 eq49537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49537 eq55489
  have eq55493 : (M.op y x) = (k (k (τ (M.op (σ x) (σ y))) x) (τ (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq55491
       have i₂ := eq10 (M.op y x)
       grind)
    | exact superpose eq10 eq55491
    | exact resolve eq55491 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55491
  have eq58939 : (σ (M.op y x)) = (σ (k (k (τ (M.op (σ x) (σ y))) x) (M.op y x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq55493 eq54995
    | exact resolve eq54995 eq55493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54995 eq55493
  have eq59008 : (σ (M.op y x)) = (σ (k (k (τ (M.op (σ x) (σ y))) x) (M.op y x))) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq58939
  have eq59033 : (σ (M.op y x)) = (k (k (M.op (σ x) (σ y)) (σ x)) (σ (M.op y x))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq59008
       have i₂ := eq332 sF4 x (M.op y x)
       grind)
    | exact superpose eq332 eq59008
    | exact resolve eq59008 eq332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332 eq59008
  have eq59045 : (σ (M.op y x)) = (k (k (M.op (σ x) (σ y)) (σ (M.op x y))) (σ (M.op y x))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq59033
       have i₂ := eq49896
       grind)
    | exact superpose eq49896 eq59033
    | exact resolve eq59033 eq49896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49896 eq59033
  have eq88613 : (M.op (σ x) (σ y)) = (k (k (M.op (σ x) (σ y)) (σ (M.op x y))) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq59045
       have i₂ := eq50154
       grind)
    | exact superpose eq50154 eq59045
    | exact resolve eq59045 eq50154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50154 eq59045
  have eq88654 : (M.op (σ x) (σ y)) = (k (k (M.op (σ x) (σ y)) (σ (M.op x y))) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq88613
  have eq88694 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq88654 eq54349
    | exact resolve eq54349 eq88654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54349 eq88654
  have eq88708 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq88694
  have eq88746 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq88708 eq14
    | (have j0 := eq14 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq14 eq88708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88748 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq88746
  have eq89905 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq88748 eq13
    | (have j0 := eq13 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq13 (σ (M.op x y)) (M.op (σ x) (σ y))
       have r₂ := eq88748
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq88748
       grind)
    | exact resolve eq13 eq88748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88748
  have eq89972 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq89905
  have eq90028 : (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq89972
       have r₂ := eq27
       grind)
    | exact resolve eq89972 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89972
  have eq90432 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq90028 eq88708
    | exact resolve eq88708 eq90028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90028
  have eq90442 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by grind
  clear eq90432
  have eq90466 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq90442
       have r₂ := eq27
       grind)
    | exact resolve eq90442 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90442
  have eq90492 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k (σ (M.op x y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq90466 eq12
    | (have j0 := eq12 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq12 (σ (M.op x y)) (M.op (σ x) (σ y))
       have r₂ := eq90466
       grind)
    | exact resolve eq12 eq90466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90466
  have eq90556 : (k (σ (M.op x y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq90492
  have eq90570 : (k (σ (M.op x y)) (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq49901 eq90556
    | exact resolve eq90556 eq49901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90556
  have eq93293 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq90570 eq88708
    | exact resolve eq88708 eq90570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88708 eq90570
  have eq93303 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq93293
  have eq93363 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq93303 eq16565
    | exact resolve eq16565 eq93303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16565 eq93303
  have eq93617 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq93363 eq50246
    | exact resolve eq50246 eq93363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50246 eq93363
  have eq93776 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq93617
  have eq93781 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq93776
       have r₂ := eq27
       grind)
    | exact resolve eq93776 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93776
  have eq93784 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq93781 eq27
    | exact resolve eq27 eq93781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq93794 : (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq93781 eq49897
    | exact resolve eq49897 eq93781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49897
  have eq93795 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ (M.op x y)) (M.op X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq93781 eq49901
    | exact resolve eq49901 eq93781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49901
  have eq93796 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op (M.op (σ (M.op x y)) X1) X0) := by
    intro X0 X1
    first
    | exact superpose eq93781 eq49904
    | exact resolve eq49904 eq93781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49904
  have eq93797 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ (M.op x y)) (M.op X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq93781 eq49906
    | (have j0 := eq49906 X0
       grind)
    | exact resolve eq49906 eq93781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49906
  have eq93800 : ∀ X0 : G, (M.op X0 (M.op (σ y) X0)) = (M.op X0 (M.op (σ (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq93781 eq50022
    | exact resolve eq50022 eq93781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50022
  have eq93868 : (σ y) ≠ (σ y) ∨ (σ (M.op x y)) = (σ (M.op y x)) := by
    first
    | exact superpose eq93781 eq50226
    | (have r₁ := eq50226
       have r₂ := eq93781
       grind)
    | exact resolve eq50226 eq93781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50226
  have eq95011 : (σ (M.op x y)) = (σ (M.op y x)) := by grind
  clear eq93868
  have eq95322 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op y x)) = (M.op (σ (M.op y x)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq50470
       have i₂ := eq95011
       grind)
    | exact superpose eq95011 eq50470
    | exact resolve eq50470 eq95011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50470
  have eq95389 : ∀ X0 : G, (σ y) ≠ (M.op (σ (M.op x y)) (M.op X0 (σ (M.op x y)))) ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq93781 eq93797
    | (have j0 := eq93797 X0
       grind)
    | exact resolve eq93797 eq93781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93781 eq93797
  have eq95391 : (σ (k y y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ (M.op x y)))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq93795 eq572
    | exact resolve eq572 eq93795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572
  have eq95645 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq95322
       have i₂ := eq95011
       grind)
    | exact superpose eq95011 eq95322
    | exact resolve eq95322 eq95011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95011 eq95322
  have eq95646 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq95645
  have eq95666 : (σ (k y y)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq93800 eq95391
    | exact resolve eq95391 eq93800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95391
  have eq95797 : (σ (k y y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq95646 eq95666
    | exact resolve eq95666 eq95646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95666
  have eq96010 : (σ (M.op x y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq95646 eq95797
    | exact resolve eq95797 eq95646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95797
  have eq96182 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ (k y y)) := by
    first
    | exact superpose eq93795 eq96010
    | exact resolve eq96010 eq93795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93795 eq96010
  have eq96239 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ (k y y)) := by
    first
    | exact superpose eq93800 eq96182
    | exact resolve eq96182 eq93800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93800 eq96182
  have eq96289 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ (k y y)) := by
    first
    | exact superpose eq95646 eq96239
    | exact resolve eq96239 eq95646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96239
  have eq96323 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ (k y y)) := by
    first
    | exact superpose eq95646 eq96289
    | exact resolve eq96289 eq95646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96289
  have eq96347 : (σ (M.op x y)) = (σ (k y y)) := by
    first
    | (have r₁ := eq96323
       have r₂ := eq93784
       grind)
    | exact resolve eq96323 eq93784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96323
  have eq96366 : (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq70
       have i₂ := eq96347
       grind)
    | exact superpose eq96347 eq70
    | exact resolve eq70 eq96347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq96347
  have eq96688 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = (M.op (σ (M.op x y)) (M.op X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq95646 eq9
    | exact resolve eq9 eq95646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96691 : ∀ X0 X1 : G, (M.op (σ (M.op x y)) X1) = (M.op (M.op (σ (M.op x y)) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq95646 eq53
    | exact resolve eq53 eq95646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq95646
  have eq96765 : ∀ X1 : G, (M.op (σ y) X1) = (M.op (σ (M.op x y)) X1) := by
    intro X1
    first
    | exact superpose eq93796 eq96691
    | exact resolve eq96691 eq93796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93796 eq96691
  have eq97348 : ∀ X0 : G, (σ y) ≠ (M.op (σ (M.op x y)) X0) ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq96688 eq95389
    | (have j0 := eq95389 X0
       grind)
    | exact resolve eq95389 eq96688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95389 eq96688
  have eq101181 : (σ y) ≠ (σ y) ∨ (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq93794 eq97348
    | (have j0 := eq97348 (σ y)
       grind)
    | (have r₁ := eq97348 (σ y)
       have r₂ := eq93794
       grind)
    | exact resolve eq97348 eq93794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97348
  have eq101190 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by grind
  clear eq101181
  have eq101198 : (k (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq96765 eq101190
    | exact resolve eq101190 eq96765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96765 eq101190
  have eq101206 : (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq93794 eq101198
    | exact resolve eq101198 eq93794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93794 eq101198
  have eq101214 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq96366 eq101206
    | exact resolve eq101206 eq96366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96366 eq101206
  have eq101221 : False := by grind
  exact eq101221

/-- `Equation4447`: `x ◇ (y ◇ x) = (y ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,Y) else if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_y_pyy_pxx_pxy_Equation4447 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4447 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4447.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X1) X2) := by
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
  have eq28 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y)
       grind)
    | exact resolve eq15 eq20
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
  have eq34 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (τ X0) X1
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq10
    | exact resolve eq10 eq14
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
  have eq36 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
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
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq10
    | exact resolve eq10 eq14
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
  have eq47 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 y)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq15
    | exact resolve eq15 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq98 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq44 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq44
    | (have j0 := eq44 y
       grind)
    | exact resolve eq44 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq107 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq47 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq47
    | exact resolve eq47 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq47 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq47
    | (have j0 := eq47 y
       grind)
    | exact resolve eq47 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq176 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X0) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq16 x X0 X3
       have i₂ := eq16 x X0 X1
       grind)
    | (have i₁ := eq16 (M.op X1 X1) X1 x
       have i₂ := eq16 X0 X1 (M.op X1 (M.op X1 X1))
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X1) X2)) = (M.op (M.op X0 (M.op X1 X0)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X2 (M.op X1 X1) X3
       have i₂ := eq16 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 x
       have i₂ := eq16 X2 X1 x
       grind)
    | (have i₁ := eq16 X0 X1 (M.op X1 (M.op X1 X1))
       have i₂ := eq16 (M.op X1 X1) X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq306 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k (τ X0) X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq15
    | exact resolve eq15 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq349 : ∀ X0 : G, (k (σ X0) (k (σ y) (σ y))) = (σ (k X0 (k y y))) := by
    intro X0
    first
    | exact superpose eq115 eq38
    | exact resolve eq38 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq363 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq576 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X1) X2)) = (M.op X3 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq179 X2 (M.op X1 X1) X3
       have i₂ := eq16 X0 X1 X3
       grind)
    | (have i₁ := eq179 X0 X0 (M.op X1 X0)
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq179
    | exact resolve eq179 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq577 : ∀ X0 : G, (M.op X0 (M.op x X0)) = (M.op y (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq179 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq179
    | (have j0 := eq179 X0 x y
       grind)
    | exact resolve eq179 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq578 : ∀ X0 : G, (M.op X0 (M.op (σ x) X0)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq179
    | (have j0 := eq179 X0 (σ x) (σ y)
       grind)
    | exact resolve eq179 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq591 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) X3) = (M.op (M.op X1 X2) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op X1 X2) X2 X3
       have i₂ := eq179 X2 X1 X0
       grind)
    | (have i₁ := eq16 (M.op X1 X2) X2 X3
       have i₂ := eq179 X0 X1 X2
       grind)
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq594 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 X1 (M.op X3 (M.op X1 X1))
       have i₂ := eq179 (M.op X1 X1) X3 X2
       grind)
    | (have i₁ := eq16 X0 X1 (M.op X3 (M.op X1 X1))
       have i₂ := eq179 X2 X3 (M.op X1 X1)
       grind)
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq609 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op x X0) (M.op y (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op x X0) X0 X1
       have i₂ := eq577 X0
       grind)
    | (have i₁ := eq16 (M.op x y) y x
       have i₂ := eq577 X0
       grind)
    | exact superpose eq577 eq16
    | exact resolve eq16 eq577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq611 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op y (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq176 X0 (M.op x (M.op X0 X0)) X1
       have i₂ := eq577 (M.op X0 X0)
       grind)
    | exact superpose eq577 eq176
    | exact resolve eq176 eq577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq612 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op y (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 (M.op x (M.op X1 X1))
       have i₂ := eq577 (M.op X1 X1)
       grind)
    | exact superpose eq577 eq16
    | exact resolve eq16 eq577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq613 : ∀ X0 : G, (M.op y (M.op x y)) = (M.op (M.op x X0) (M.op y (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq609 X0 x
       have i₂ := eq611 X0 x
       grind)
    | exact superpose eq611 eq609
    | exact resolve eq609 eq611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609
  have eq620 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op x (σ x)) (M.op y (M.op x y))) := by
    first
    | (have i₁ := eq578 (M.op x sF2)
       have i₂ := eq577 sF2
       grind)
    | exact superpose eq577 eq578
    | exact resolve eq578 eq577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq577
  have eq635 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq578 eq176
    | exact resolve eq176 eq578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq636 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq578 eq16
    | exact resolve eq16 eq578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578
  have eq641 : (M.op y (M.op x y)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq613 eq620
    | exact resolve eq620 eq613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620
  have eq652 : ∀ X1 : G, (M.op y (M.op x y)) = (M.op (M.op y (M.op x y)) X1) := by
    intro X1
    first
    | (have i₁ := eq611 (M.op x x) X1
       have i₂ := eq611 x (M.op x x)
       grind)
    | exact superpose eq611 eq611
    | exact resolve eq611 eq611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611
  have eq685 : ∀ X1 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) X1) := by
    intro X1
    first
    | exact superpose eq641 eq652
    | exact resolve eq652 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652
  have eq1790 : ∀ X0 X1 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (k X0 X0) X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq635 X0 X1
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq635
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq635 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1822 : (M.op x y) = (k x y) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
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
  have eq1829 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
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
  have eq1835 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1836 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1835 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1835
  have eq1838 : ∀ X0 X1 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (k X0 X0) X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1790 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1790
  have eq1980 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1836 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq1836
    | (have j0 := eq1836 (σ X0)
       grind)
    | exact resolve eq1836 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2325 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = (k X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq182 x
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq182
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq182 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2337 : (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ y) (M.op (σ x) (σ y)))) = (k (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq685 eq182
    | exact resolve eq182 eq685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2354 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq635 X0 (M.op X0 X0)
       have i₂ := eq182 X0
       grind)
    | exact superpose eq182 eq635
    | exact resolve eq635 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2375 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = (k X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq2325 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2325
  have eq2397 : (M.op (σ y) (M.op (σ x) (σ y))) = (k (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq685 eq2337
    | exact resolve eq2337 eq685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685 eq2337
  have eq2409 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (k X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq1838 eq2375
    | (have j0 := eq2375 X0
       have j1 := eq1838 X0 x
       grind)
    | exact resolve eq2375 eq1838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1838 eq2375
  have eq2446 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = (τ (M.op (σ y) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq363 X0 (M.op (σ X0) (σ X0))
       have i₂ := eq2354 (σ X0)
       grind)
    | exact superpose eq2354 eq363
    | exact resolve eq363 eq2354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2448 : (σ (M.op (σ y) (M.op (σ x) (σ y)))) = (k (σ x) (σ (M.op x x))) := by
    first
    | (have i₁ := eq35 (M.op x x)
       have i₂ := eq2354 x
       grind)
    | exact superpose eq2354 eq35
    | exact resolve eq35 eq2354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2449 : (σ (M.op (σ y) (M.op (σ x) (σ y)))) = (k (σ y) (σ (M.op y y))) := by
    first
    | (have i₁ := eq36 (M.op y y)
       have i₂ := eq2354 y
       grind)
    | exact superpose eq2354 eq36
    | exact resolve eq36 eq2354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2450 : (σ (M.op (σ y) (M.op (σ x) (σ y)))) = (k (σ (M.op x y)) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq37 (M.op sF0 sF0)
       have i₂ := eq2354 sF0
       grind)
    | exact superpose eq2354 eq37
    | exact resolve eq37 eq2354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq2452 : (τ (M.op (σ y) (M.op (σ x) (σ y)))) = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq90 (M.op sF2 sF2)
       have i₂ := eq2354 sF2
       grind)
    | exact superpose eq2354 eq90
    | exact resolve eq90 eq2354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2453 : (τ (M.op (σ y) (M.op (σ x) (σ y)))) = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | (have i₁ := eq107 (M.op sF3 sF3)
       have i₂ := eq2354 sF3
       grind)
    | exact superpose eq2354 eq107
    | exact resolve eq107 eq2354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq6478 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1822
       grind)
    | exact superpose eq1822 eq40
    | exact resolve eq40 eq1822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6479 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq6478
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6478
    | exact resolve eq6478 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6478
  have eq6481 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq6479
    | exact resolve eq6479 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6479
  have eq31436 : (σ (M.op (σ y) (M.op (σ x) (σ y)))) ≠ (σ (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (σ (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op (σ (M.op (σ y) (M.op (σ x) (σ y)))) (σ (M.op (σ y) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq2397 eq1980
    | (have j0 := eq1980 (M.op (σ y) (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq1980 eq2397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1980
  have eq31472 : (σ (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op (σ (M.op (σ y) (M.op (σ x) (σ y)))) (σ (M.op (σ y) (M.op (σ x) (σ y))))) := by grind
  clear eq31436
  have eq31586 : (τ (M.op (σ y) (M.op (σ x) (σ y)))) = (k (M.op (σ y) (M.op (σ x) (σ y))) (τ (σ (M.op (σ y) (M.op (σ x) (σ y)))))) := by
    first
    | exact superpose eq31472 eq2446
    | exact resolve eq2446 eq31472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31607 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ (M.op (σ y) (M.op (σ x) (σ y)))) X0) := by
    intro X0
    first
    | exact superpose eq31472 eq635
    | exact resolve eq635 eq31472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31611 : ∀ X0 : G, (M.op (σ (M.op (σ y) (M.op (σ x) (σ y)))) (σ (M.op (σ y) (M.op (σ x) (σ y))))) = (M.op (σ (M.op (σ y) (M.op (σ x) (σ y)))) X0) := by
    intro X0
    first
    | exact superpose eq31472 eq16
    | exact resolve eq16 eq31472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31649 : ∀ X0 : G, (σ (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op (σ (M.op (σ y) (M.op (σ x) (σ y)))) X0) := by
    intro X0
    first
    | exact superpose eq31472 eq31611
    | exact resolve eq31611 eq31472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31472 eq31611
  have eq31670 : (k (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ y) (M.op (σ x) (σ y)))) = (τ (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq31586
       have i₂ := eq15 (M.op sF3 sF4)
       grind)
    | exact superpose eq15 eq31586
    | exact resolve eq31586 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31586
  have eq31685 : (M.op (σ y) (M.op (σ x) (σ y))) = (σ (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq31607 eq31649
    | exact resolve eq31649 eq31607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31607 eq31649
  have eq31699 : (M.op (σ y) (M.op (σ x) (σ y))) = (τ (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq2397 eq31670
    | exact resolve eq31670 eq2397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2397 eq31670
  have eq31871 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq6481 eq1829
    | exact resolve eq1829 eq6481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6481
  have eq31878 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq31871
       have r₂ := eq27
       grind)
    | exact resolve eq31871 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31871
  have eq32213 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq31878 eq636
    | exact resolve eq636 eq31878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32216 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq31878 eq32213
    | exact resolve eq32213 eq31878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31878 eq32213
  have eq32327 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq32216 eq31685
    | exact resolve eq31685 eq32216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32417 : (k x (τ (σ y))) = (τ (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (σ y) = (σ (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq32327 eq2452
    | exact resolve eq2452 eq32327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32447 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) X0) ∨ (σ y) = (σ (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq32327 eq16
    | exact resolve eq16 eq32327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32464 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (σ (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq32327 eq636
    | exact resolve eq636 eq32327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32327
  have eq32467 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (σ (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26 eq32464
    | exact resolve eq32464 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32464
  have eq32483 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) X0) ∨ (σ y) = (σ (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq26 eq32447
    | (have j0 := eq32447 X0
       grind)
    | exact resolve eq32447 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32447
  have eq32504 : (k x (τ (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (σ (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq31699 eq32417
    | exact resolve eq32417 eq31699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32417
  have eq32530 : (k x y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (σ (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq31 eq32504
    | exact resolve eq32504 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32504
  have eq32548 : (M.op (σ x) (σ y)) = (k x y) ∨ (σ y) = (σ (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq32483 eq32530
    | exact resolve eq32530 eq32483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32483 eq32530
  have eq32558 : y = (M.op y y) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1822 eq32548
    | exact resolve eq32548 eq1822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32548
  have eq32560 : (k (σ y) (σ y)) = (σ (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2449
       have i₂ := eq32558
       grind)
    | exact superpose eq32558 eq2449
    | exact resolve eq2449 eq32558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32583 : (k y y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2354 y
       have i₂ := eq32558
       grind)
    | exact superpose eq32558 eq2354
    | exact resolve eq2354 eq32558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32603 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op y y) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq636 y y
       have i₂ := eq32558
       grind)
    | exact superpose eq32558 eq636
    | exact resolve eq636 eq32558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32606 : y = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq32558 eq32603
    | exact resolve eq32603 eq32558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32558 eq32603
  have eq32637 : (k (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq31685 eq32560
    | exact resolve eq32560 eq31685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32560
  have eq32656 : (k (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq32637
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq32637
    | exact resolve eq32637 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32637
  have eq32673 : y = (k (σ y) (σ y)) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq32606 eq32656
    | exact resolve eq32656 eq32606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32656
  have eq32713 : y = (σ y) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq32606 eq31685
    | exact resolve eq31685 eq32606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32718 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ y) (σ y)) X0)) = (M.op (M.op (M.op (σ x) (σ y)) y) X1) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq32606 eq178
    | exact resolve eq178 eq32606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32731 : (M.op y (M.op x y)) = (M.op (M.op (σ x) (σ y)) y) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq32606 eq612
    | exact resolve eq612 eq32606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32606
  have eq32735 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) y) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq641 eq32731
    | exact resolve eq32731 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32731
  have eq32748 : ∀ X1 : G, (M.op y (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) y) X1) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    intro X1
    first
    | (have i₁ := eq32718 x X1
       have i₂ := eq612 x (M.op sF3 sF3)
       grind)
    | exact superpose eq612 eq32718
    | exact resolve eq32718 eq612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32718
  have eq32751 : y = (M.op x x) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq32713
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq32713
    | exact resolve eq32713 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32713
  have eq32756 : (k y y) = (M.op (M.op (σ x) (σ y)) y) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq32583 eq32735
    | exact resolve eq32735 eq32583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32735
  have eq32768 : ∀ X1 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) y) X1) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    intro X1
    first
    | exact superpose eq641 eq32748
    | exact resolve eq32748 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32748
  have eq32774 : (k (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq32751 eq32756
    | exact resolve eq32756 eq32751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32756
  have eq32786 : ∀ X1 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X1) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    intro X1
    first
    | exact superpose eq32751 eq32768
    | exact resolve eq32768 eq32751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32768
  have eq32792 : y = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq32673 eq32774
    | exact resolve eq32774 eq32673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32774
  have eq32801 : ∀ X1 : G, (k y y) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X1) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    intro X1
    first
    | exact superpose eq32583 eq32786
    | exact resolve eq32786 eq32583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32583 eq32786
  have eq32805 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq32751 eq32792
    | exact resolve eq32792 eq32751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32792
  have eq32813 : ∀ X1 : G, (k (σ y) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X1) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    intro X1
    first
    | exact superpose eq32751 eq32801
    | exact resolve eq32801 eq32751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32801
  have eq32824 : ∀ X1 : G, y = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X1) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    intro X1
    first
    | exact superpose eq32673 eq32813
    | exact resolve eq32813 eq32673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32673 eq32813
  have eq32835 : ∀ X1 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X1) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    intro X1
    first
    | exact superpose eq32751 eq32824
    | exact resolve eq32824 eq32751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32824
  have eq32840 : ∀ X1 : G, (σ y) = (M.op (σ y) X1) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    intro X1
    first
    | exact superpose eq32805 eq32835
    | exact resolve eq32835 eq32805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32805 eq32835
  have eq32890 : (M.op x y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq636 x x
       have i₂ := eq32751
       grind)
    | exact superpose eq32751 eq636
    | exact resolve eq636 eq32751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32751
  have eq32893 : (M.op x y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq32890
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq32890
    | exact resolve eq32890 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32890
  have eq33005 : (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq32893 eq31685
    | exact resolve eq31685 eq32893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32893
  have eq33044 : (σ y) = (σ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq20 eq33005
    | exact resolve eq33005 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33005
  have eq33091 : (σ y) = (τ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq33044 eq15
    | exact resolve eq15 eq33044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33218 : y = (σ y) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq31 eq33091
    | exact resolve eq33091 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33091
  have eq33219 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (σ y) := by grind
  clear eq33218
  have eq33270 : (M.op (σ y) (M.op x y)) = (σ (M.op (σ y) (M.op x y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (σ y) := by
    first
    | exact superpose eq33219 eq31685
    | exact resolve eq31685 eq33219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33219
  have eq39213 : (σ y) = (σ (σ y)) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq32840 eq31685
    | exact resolve eq31685 eq32840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32840
  have eq39301 : y = (M.op x x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (σ y)) := by grind
  clear eq39213
  have eq39375 : (k (σ x) (σ y)) = (σ (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (σ y)) := by
    first
    | (have i₁ := eq2448
       have i₂ := eq39301
       grind)
    | exact superpose eq39301 eq2448
    | exact resolve eq2448 eq39301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2448
  have eq39400 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op y X0) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (σ y)) := by
    intro X0
    first
    | (have i₁ := eq635 x X0
       have i₂ := eq39301
       grind)
    | exact superpose eq39301 eq635
    | exact resolve eq635 eq39301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39401 : (k x y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (σ y)) := by
    first
    | (have i₁ := eq2354 x
       have i₂ := eq39301
       grind)
    | exact superpose eq39301 eq2354
    | exact resolve eq2354 eq39301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39407 : ∀ X0 : G, (M.op x y) = (M.op y X0) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16 x x x
       have i₂ := eq39301
       grind)
    | exact superpose eq39301 eq16
    | exact resolve eq16 eq39301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39410 : ∀ X0 X1 : G, (M.op X0 (M.op y X0)) = (M.op (M.op x y) X1) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq178 x x x x
       have i₂ := eq39301
       grind)
    | exact superpose eq39301 eq178
    | exact resolve eq178 eq39301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39424 : (M.op x y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (σ y)) := by
    first
    | (have i₁ := eq636 x x
       have i₂ := eq39301
       grind)
    | exact superpose eq39301 eq636
    | exact resolve eq636 eq39301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39427 : (M.op x y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (σ y)) := by
    first
    | (have i₁ := eq39424
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq39424
    | exact resolve eq39424 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39424
  have eq39441 : ∀ X0 X1 : G, (M.op X0 (M.op y X0)) = (M.op (M.op x y) X1) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq39410 X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq39410
    | (have j0 := eq39410 X0 X1
       grind)
    | exact resolve eq39410 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39410
  have eq39443 : ∀ X0 : G, (M.op x y) = (M.op y X0) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (σ y)) := by
    intro X0
    first
    | (have i₁ := eq39407 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq39407
    | (have j0 := eq39407 X0
       grind)
    | exact resolve eq39407 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39407
  have eq39444 : ∀ X0 : G, (k x y) = (M.op y X0) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (σ y)) := by
    intro X0
    first
    | exact superpose eq39401 eq39400
    | exact resolve eq39400 eq39401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39400
  have eq39461 : (k (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (σ y)) := by
    first
    | exact superpose eq31685 eq39375
    | exact resolve eq39375 eq31685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39375
  have eq39471 : ∀ X1 : G, (M.op y (M.op x y)) = (M.op (M.op x y) X1) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (σ y)) := by
    intro X1
    first
    | (have i₁ := eq39441 x X1
       have i₂ := eq612 x y
       grind)
    | exact superpose eq612 eq39441
    | exact resolve eq39441 eq612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39441
  have eq39473 : (M.op x y) = (k x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (σ y)) := by
    first
    | exact superpose eq39443 eq39444
    | exact resolve eq39444 eq39443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39443 eq39444
  have eq39486 : (k (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (σ y)) := by
    first
    | (have i₁ := eq39461
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq39461
    | exact resolve eq39461 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39461
  have eq39493 : ∀ X1 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op x y) X1) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (σ y)) := by
    intro X1
    first
    | exact superpose eq641 eq39471
    | exact resolve eq39471 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39471
  have eq39504 : (M.op x y) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (σ y)) := by
    first
    | exact superpose eq39427 eq39486
    | exact resolve eq39486 eq39427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39486
  have eq39508 : ∀ X1 : G, (k x y) = (M.op (M.op x y) X1) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (σ y)) := by
    intro X1
    first
    | exact superpose eq39401 eq39493
    | exact resolve eq39493 eq39401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39401 eq39493
  have eq39518 : ∀ X1 : G, (M.op x y) = (M.op (M.op x y) X1) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (σ y)) := by
    intro X1
    first
    | exact superpose eq39473 eq39508
    | exact resolve eq39508 eq39473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39473 eq39508
  have eq39900 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (σ y)) := by
    first
    | exact superpose eq39427 eq31685
    | exact resolve eq31685 eq39427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39942 : (σ y) = (σ (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq20 eq39900
    | exact resolve eq39900 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39900
  have eq40505 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (σ y)) := by
    first
    | exact superpose eq39504 eq1829
    | exact resolve eq1829 eq39504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39504
  have eq40509 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (σ y)) := by grind
  clear eq40505
  have eq55717 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (σ y)) := by
    first
    | exact superpose eq40509 eq636
    | exact resolve eq636 eq40509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55731 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (σ y)) := by
    first
    | exact superpose eq40509 eq55717
    | exact resolve eq55717 eq40509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40509 eq55717
  have eq55770 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) ∨ (σ y) = (σ (σ y)) := by
    first
    | exact superpose eq39427 eq55731
    | exact resolve eq55731 eq39427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55731
  have eq55894 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) ∨ (σ y) = (σ (σ y)) := by
    first
    | exact superpose eq55770 eq636
    | exact resolve eq636 eq55770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55770
  have eq55906 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) ∨ (σ y) = (σ (σ y)) := by
    first
    | exact superpose eq26 eq55894
    | exact resolve eq55894 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55894
  have eq55954 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) ∨ (σ y) = (σ (σ y)) := by
    first
    | exact superpose eq39427 eq55906
    | exact resolve eq55906 eq39427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39427 eq55906
  have eq55955 : (σ y) = (σ (σ y)) ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq55954
  have eq55993 : (σ y) = (τ (σ y)) ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq55955 eq15
    | exact resolve eq15 eq55955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55955
  have eq56120 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) ∨ y = (σ y) := by
    first
    | exact superpose eq31 eq55993
    | exact resolve eq55993 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55993
  have eq56164 : (M.op x y) ≠ (σ (M.op x y)) ∨ (M.op x y) = (σ y) ∨ y = (σ y) := by
    first
    | exact superpose eq56120 eq27
    | exact resolve eq27 eq56120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56120
  have eq74581 : (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) ∨ (σ y) = (σ (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq32467 eq31685
    | exact resolve eq31685 eq32467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74655 : (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (σ (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq39301 eq74581
    | exact resolve eq74581 eq39301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74581
  have eq74677 : y = (M.op y y) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq74655
    | exact resolve eq74655 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74655
  have eq74739 : (k (σ y) (σ y)) = (σ (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2449
       have i₂ := eq74677
       grind)
    | exact superpose eq74677 eq2449
    | exact resolve eq2449 eq74677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74760 : (k y y) = (M.op y y) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq182 y
       have i₂ := eq74677
       grind)
    | exact superpose eq74677 eq182
    | exact resolve eq182 eq74677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74773 : (k y y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2354 y
       have i₂ := eq74677
       grind)
    | exact superpose eq74677 eq2354
    | exact resolve eq2354 eq74677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74805 : ∀ X0 X1 : G, (M.op X0 (M.op y X0)) = (M.op X1 (M.op y y)) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq576 y y x x
       have i₂ := eq74677
       grind)
    | exact superpose eq74677 eq576
    | exact resolve eq576 eq74677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74811 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op y y) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq636 y y
       have i₂ := eq74677
       grind)
    | exact superpose eq74677 eq636
    | exact resolve eq636 eq74677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74855 : (M.op y y) = (M.op (σ y) (M.op x y)) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq39301 eq74811
    | exact resolve eq74811 eq39301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74811
  have eq74861 : ∀ X1 : G, (M.op y (M.op x y)) = (M.op X1 (M.op y y)) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x x) := by
    intro X1
    first
    | (have i₁ := eq74805 x X1
       have i₂ := eq612 x y
       grind)
    | exact superpose eq612 eq74805
    | exact resolve eq74805 eq612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74805
  have eq74874 : (k y y) = (M.op (σ y) (M.op x y)) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq39301 eq74773
    | exact resolve eq74773 eq39301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74773
  have eq74884 : y = (k y y) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq74677 eq74760
    | exact resolve eq74760 eq74677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74760
  have eq74891 : (k (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq31685 eq74739
    | exact resolve eq74739 eq31685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74739
  have eq74893 : y = (M.op (σ y) (M.op x y)) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq74677 eq74855
    | exact resolve eq74855 eq74677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74855
  have eq74896 : ∀ X1 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op X1 (M.op y y)) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x x) := by
    intro X1
    first
    | exact superpose eq641 eq74861
    | exact resolve eq74861 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74861
  have eq74913 : (k (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq74891
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq74891
    | exact resolve eq74891 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74891
  have eq74917 : ∀ X1 : G, (M.op X1 (M.op y y)) = (M.op (σ y) (M.op x y)) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x x) := by
    intro X1
    first
    | exact superpose eq39301 eq74896
    | exact resolve eq74896 eq39301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74896
  have eq74932 : (k (σ y) (σ y)) = (M.op (σ y) (M.op x y)) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq39301 eq74913
    | exact resolve eq74913 eq39301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74913
  have eq74934 : ∀ X1 : G, (M.op X1 y) = (M.op (σ y) (M.op x y)) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x x) := by
    intro X1
    first
    | exact superpose eq74677 eq74917
    | exact resolve eq74917 eq74677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74677 eq74917
  have eq74944 : y = (k (σ y) (σ y)) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq74893 eq74932
    | exact resolve eq74932 eq74893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74932
  have eq74946 : ∀ X1 : G, (k y y) = (M.op X1 y) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x x) := by
    intro X1
    first
    | exact superpose eq74874 eq74934
    | exact resolve eq74934 eq74874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74934
  have eq74956 : ∀ X1 : G, y = (M.op x x) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op X1 y) := by
    intro X1
    first
    | exact superpose eq74884 eq74946
    | exact resolve eq74946 eq74884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74884 eq74946
  have eq75490 : y = (σ y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (σ y) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq74893 eq33270
    | exact resolve eq33270 eq74893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75513 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ y) (σ y)) X0)) = (M.op (M.op (M.op x y) y) X1) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq74893 eq178
    | exact resolve eq178 eq74893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq75527 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op x y) y) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq74893 eq636
    | exact resolve eq636 eq74893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74893
  have eq75539 : y = (σ y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (σ y) ∨ (σ y) = (σ (σ y)) ∨ y = (M.op x x) := by grind
  clear eq75490
  have eq75552 : (M.op (M.op x y) y) = (M.op (σ y) (M.op x y)) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq39301 eq75527
    | exact resolve eq75527 eq39301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75527
  have eq75566 : ∀ X1 : G, (M.op y (M.op x y)) = (M.op (M.op (M.op x y) y) X1) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x x) := by
    intro X1
    first
    | (have i₁ := eq75513 x X1
       have i₂ := eq612 x (M.op sF3 sF3)
       grind)
    | exact superpose eq612 eq75513
    | exact resolve eq75513 eq612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75513
  have eq75579 : y = (σ y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (σ y) ∨ (σ y) = (σ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq75539
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq75539
    | exact resolve eq75539 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75539
  have eq75580 : y = (M.op x x) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (σ (σ y)) ∨ y = (σ y) := by grind
  clear eq75579
  have eq75581 : (k y y) = (M.op (M.op x y) y) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq74874 eq75552
    | exact resolve eq75552 eq74874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75552
  have eq75594 : ∀ X1 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (M.op x y) y) X1) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x x) := by
    intro X1
    first
    | exact superpose eq641 eq75566
    | exact resolve eq75566 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75566
  have eq75601 : (k (σ y) (σ y)) = (M.op (M.op x y) (σ y)) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq75580 eq75581
    | exact resolve eq75581 eq75580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75581
  have eq75613 : ∀ X1 : G, (M.op (σ y) (M.op x y)) = (M.op (M.op (M.op x y) y) X1) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x x) := by
    intro X1
    first
    | exact superpose eq39301 eq75594
    | exact resolve eq75594 eq39301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39301 eq75594
  have eq75616 : y = (M.op (M.op x y) (σ y)) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq74944 eq75601
    | exact resolve eq75601 eq74944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75601
  have eq75625 : ∀ X1 : G, (M.op (σ y) (M.op x y)) = (M.op (M.op (M.op x y) (σ y)) X1) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x x) := by
    intro X1
    first
    | exact superpose eq75580 eq75613
    | exact resolve eq75613 eq75580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75613
  have eq75627 : (σ y) = (M.op (M.op x y) (σ y)) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq75580 eq75616
    | exact resolve eq75616 eq75580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75616
  have eq75636 : ∀ X1 : G, (k y y) = (M.op (M.op (M.op x y) (σ y)) X1) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x x) := by
    intro X1
    first
    | exact superpose eq74874 eq75625
    | exact resolve eq75625 eq74874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74874 eq75625
  have eq75646 : ∀ X1 : G, (k (σ y) (σ y)) = (M.op (M.op (M.op x y) (σ y)) X1) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x x) := by
    intro X1
    first
    | exact superpose eq75580 eq75636
    | exact resolve eq75636 eq75580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75636
  have eq75656 : ∀ X1 : G, y = (M.op (M.op (M.op x y) (σ y)) X1) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x x) := by
    intro X1
    first
    | exact superpose eq74944 eq75646
    | exact resolve eq75646 eq74944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74944 eq75646
  have eq75665 : ∀ X1 : G, (σ y) = (M.op (M.op (M.op x y) (σ y)) X1) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x x) := by
    intro X1
    first
    | exact superpose eq75580 eq75656
    | exact resolve eq75656 eq75580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75656
  have eq75670 : ∀ X1 : G, (σ y) = (M.op (σ y) X1) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x x) := by
    intro X1
    first
    | exact superpose eq75627 eq75665
    | exact resolve eq75665 eq75627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75627 eq75665
  have eq75741 : (M.op x y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (σ (σ y)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq636 x x
       have i₂ := eq75580
       grind)
    | exact superpose eq75580 eq636
    | exact resolve eq636 eq75580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75580
  have eq75762 : (M.op x y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (σ (σ y)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq75741
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq75741
    | exact resolve eq75741 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75741
  have eq75804 : (M.op x y) = (M.op (σ y) (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (σ (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq33044 eq75762
    | exact resolve eq75762 eq33044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33044 eq75762
  have eq76346 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (σ y) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (σ (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq75804 eq33270
    | exact resolve eq33270 eq75804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33270
  have eq76402 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (σ y) ∨ (σ y) = (σ (σ y)) := by grind
  clear eq76346
  have eq76439 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (σ y) ∨ (σ y) = (σ (σ y)) := by
    first
    | exact superpose eq20 eq76402
    | exact resolve eq76402 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76402
  have eq76440 : (σ y) = (σ (σ y)) ∨ y = (σ y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq76439
  have eq76460 : (σ y) = (τ (σ y)) ∨ y = (σ y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq76440 eq15
    | exact resolve eq15 eq76440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76597 : y = (σ y) ∨ y = (σ y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq31 eq76460
    | exact resolve eq76460 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76460
  have eq76598 : (M.op x y) = (σ (M.op x y)) ∨ y = (σ y) := by grind
  clear eq76597
  have eq76637 : (M.op x y) = (τ (M.op x y)) ∨ y = (σ y) := by
    first
    | exact superpose eq76598 eq28
    | exact resolve eq28 eq76598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76686 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (σ y) ∨ y = (σ y) ∨ y = (σ y) := by
    first
    | exact superpose eq76598 eq56164
    | (have r₁ := eq56164
       have r₂ := eq76598
       grind)
    | exact resolve eq56164 eq76598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56164
  have eq76693 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (σ y) ∨ y = (σ y) := by grind
  clear eq76686
  have eq76694 : (M.op x y) = (σ y) ∨ y = (σ y) := by grind
  clear eq76693
  have eq76748 : y = (τ (M.op x y)) ∨ y = (σ y) := by
    first
    | exact superpose eq76694 eq31
    | exact resolve eq31 eq76694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76694
  have eq76996 : y = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq76637 eq76748
    | exact resolve eq76748 eq76637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76637 eq76748
  have eq77052 : (M.op x y) = (M.op x (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq76996
       grind)
    | exact superpose eq76996 eq18
    | exact resolve eq18 eq76996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77055 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (k X0 (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq76996
       grind)
    | exact superpose eq76996 eq40
    | exact resolve eq40 eq76996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77074 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (k x (σ y)) ∨ (σ y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1822
       have i₂ := eq76996
       grind)
    | exact superpose eq76996 eq1822
    | exact resolve eq1822 eq76996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77110 : (M.op x y) ≠ (σ y) ∨ y = (M.op x y) := by grind
  have eq116155 : ∀ X0 : G, (M.op x y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq636 x x
       have i₂ := eq74956 X0
       grind)
    | exact superpose eq74956 eq636
    | (have j1 := eq74956 X0
       grind)
    | exact resolve eq636 eq74956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74956
  have eq116175 : ∀ X0 : G, (M.op x y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq116155 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq116155
    | (have j0 := eq116155 X0
       grind)
    | exact resolve eq116155 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116155
  have eq116230 : ∀ X0 : G, (M.op x y) = (M.op (σ y) (M.op x y)) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | exact superpose eq39942 eq116175
    | (have j0 := eq116175 X0
       grind)
    | exact resolve eq116175 eq39942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39942 eq116175
  have eq116283 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (M.op (σ y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq75804 eq116230
    | exact resolve eq116230 eq75804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75804 eq116230
  have eq118723 : (σ y) = (σ (σ y)) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq75670 eq31685
    | exact resolve eq31685 eq75670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75670
  have eq118878 : (σ y) = (σ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x x) := by grind
  clear eq118723
  have eq118992 : (σ y) = (M.op x x) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (σ (σ y)) := by
    first
    | exact superpose eq76440 eq118878
    | exact resolve eq118878 eq76440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76440 eq118878
  have eq119194 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op (σ y) X1) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (σ (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq176 x X1 x
       have i₂ := eq118992
       grind)
    | exact superpose eq118992 eq176
    | exact resolve eq176 eq118992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq118992
  have eq119810 : ∀ X0 : G, (M.op (σ y) X0) = (σ (M.op (σ y) X0)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (σ (σ y)) := by
    intro X0
    first
    | exact superpose eq119194 eq31685
    | exact resolve eq31685 eq119194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119194
  have eq129540 : (σ y) = (σ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (σ (σ y)) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (M.op (σ y) (M.op x y)) := by
    first
    | exact superpose eq116283 eq119810
    | exact resolve eq119810 eq116283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116283
  have eq129549 : (M.op x y) = (M.op (σ y) (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (σ (σ y)) := by grind
  clear eq129540
  have eq129724 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (σ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (σ (σ y)) := by
    first
    | exact superpose eq129549 eq119810
    | exact resolve eq119810 eq129549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119810 eq129549
  have eq129750 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (σ (σ y)) := by grind
  clear eq129724
  have eq129799 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (σ (σ y)) := by
    first
    | exact superpose eq20 eq129750
    | exact resolve eq129750 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129750
  have eq129800 : (σ y) = (σ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq129799
  have eq129819 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (k X0 (σ y))) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq129800 eq10
    | exact resolve eq10 eq129800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq173033 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (k x (σ y)) ∨ (σ y) = (M.op x x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq77074 eq16
    | exact resolve eq16 eq77074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq173044 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) X0)) = (M.op X1 (M.op (σ y) (σ y))) ∨ (M.op x y) = (k x (σ y)) ∨ (σ y) = (M.op x x) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq77074 eq576
    | exact resolve eq576 eq77074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq173083 : ∀ X1 : G, (M.op y (M.op x y)) = (M.op X1 (M.op (σ y) (σ y))) ∨ (M.op x y) = (k x (σ y)) ∨ (σ y) = (M.op x x) ∨ y = (M.op x y) := by
    intro X1
    first
    | (have i₁ := eq173044 x X1
       have i₂ := eq612 x sF3
       grind)
    | exact superpose eq612 eq173044
    | exact resolve eq173044 eq612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173044
  have eq173090 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) ∨ (M.op x y) = (k x (σ y)) ∨ (σ y) = (M.op x x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq77074 eq173033
    | exact resolve eq173033 eq77074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173033
  have eq173162 : ∀ X1 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op X1 (M.op (σ y) (σ y))) ∨ (M.op x y) = (k x (σ y)) ∨ (σ y) = (M.op x x) ∨ y = (M.op x y) := by
    intro X1
    first
    | exact superpose eq641 eq173083
    | exact resolve eq173083 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173083
  have eq173230 : ∀ X1 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op X1 (σ y)) ∨ (M.op x y) = (k x (σ y)) ∨ (σ y) = (M.op x x) ∨ y = (M.op x y) := by
    intro X1
    first
    | exact superpose eq77074 eq173162
    | exact resolve eq173162 eq77074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77074 eq173162
  have eq173285 : ∀ X1 : G, (σ y) = (M.op x x) ∨ (M.op x y) = (k x (σ y)) ∨ (σ y) = (M.op X1 (σ y)) ∨ y = (M.op x y) := by
    intro X1
    first
    | exact superpose eq173090 eq173230
    | exact resolve eq173230 eq173090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173090 eq173230
  have eq178330 : ∀ X0 X1 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ y) X0) ∨ (M.op x y) = (k x (σ y)) ∨ (σ y) = (M.op X1 (σ y)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq635 x X0
       have i₂ := eq173285 X1
       grind)
    | exact superpose eq173285 eq635
    | (have j1 := eq173285 X1
       grind)
    | exact resolve eq635 eq173285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635
  have eq178331 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (k x (σ y)) ∨ (M.op x y) = (k x (σ y)) ∨ (σ y) = (M.op X0 (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq2354 x
       have i₂ := eq173285 X0
       grind)
    | exact superpose eq173285 eq2354
    | (have j1 := eq173285 X0
       grind)
    | exact resolve eq2354 eq173285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178373 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op x (σ y)) ∨ (M.op x y) = (k x (σ y)) ∨ (σ y) = (M.op X1 (σ y)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 x x x
       have i₂ := eq173285 X1
       grind)
    | exact superpose eq173285 eq16
    | (have j1 := eq173285 X1
       grind)
    | exact resolve eq16 eq173285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173285
  have eq178429 : ∀ X0 X1 : G, (M.op x y) = (M.op (σ y) X0) ∨ (M.op x y) = (k x (σ y)) ∨ (σ y) = (M.op X1 (σ y)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq77052 eq178373
    | (have j0 := eq178373 X0 X1
       grind)
    | exact resolve eq178373 eq77052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178373
  have eq178440 : ∀ X0 X1 : G, (M.op (σ y) X0) = (k x (σ y)) ∨ (M.op x y) = (k x (σ y)) ∨ (σ y) = (M.op X1 (σ y)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq178331 eq178330
    | (have j0 := eq178330 X0 X1
       have j1 := eq178331 X1
       grind)
    | exact resolve eq178330 eq178331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178330 eq178331
  have eq178479 : ∀ X1 : G, (M.op x y) = (k x (σ y)) ∨ (M.op x y) = (k x (σ y)) ∨ (σ y) = (M.op X1 (σ y)) ∨ y = (M.op x y) := by
    intro X1
    first
    | exact superpose eq178429 eq178440
    | (have j0 := eq178440 x X1
       have j1 := eq178429 x X1
       grind)
    | exact resolve eq178440 eq178429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178429 eq178440
  have eq178480 : ∀ X1 : G, (σ y) = (M.op X1 (σ y)) ∨ (M.op x y) = (k x (σ y)) ∨ y = (M.op x y) := by
    intro X1
    first
    | (have j0 := eq178479 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178479
  have eq179655 : (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (k x (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq178480 eq77052
    | exact resolve eq77052 eq178480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179787 : (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (k x (σ y)) := by grind
  clear eq179655
  have eq179857 : (M.op x y) = (k x (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq179787
       have r₂ := eq77110
       grind)
    | exact resolve eq179787 eq77110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179787
  have eq180057 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq179857 eq77055
    | exact resolve eq77055 eq179857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77055
  have eq180060 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq179857 eq129819
    | exact resolve eq129819 eq179857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179857
  have eq180066 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq180057
  have eq180074 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq180060
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq180060
    | exact resolve eq180060 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180060
  have eq180077 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq180066
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq180066
    | exact resolve eq180066 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq180066
  have eq180095 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq180074
    | exact resolve eq180074 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180074
  have eq180098 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq180077
    | exact resolve eq180077 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180077
  have eq180113 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq76598 eq180095
    | exact resolve eq180095 eq76598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180095
  have eq180131 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq180098 eq1829
    | exact resolve eq1829 eq180098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1829
  have eq180150 : (σ (σ (M.op x y))) = (k (σ (σ x)) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq180098 eq129819
    | exact resolve eq129819 eq180098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180098
  have eq180163 : (σ (σ (M.op x y))) = (k (σ (σ x)) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq76598 eq180150
    | exact resolve eq180150 eq76598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180150
  have eq180168 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq180131
       have r₂ := eq27
       grind)
    | exact resolve eq180131 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180131
  have eq180446 : (τ (σ (M.op x y))) = (k x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq180113 eq98
    | exact resolve eq98 eq180113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq180113
  have eq180497 : (M.op x y) = (k x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq28 eq180446
    | exact resolve eq180446 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq180446
  have eq180506 : (M.op x y) = (k x (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq76598 eq180497
    | exact resolve eq180497 eq76598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76598 eq180497
  have eq181134 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq180168 eq182
    | exact resolve eq182 eq180168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181147 : (k (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq180168 eq2354
    | exact resolve eq2354 eq180168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2354
  have eq181198 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) X0)) = (M.op X1 (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq180168 eq576
    | exact resolve eq576 eq180168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181238 : ∀ X1 : G, (M.op y (M.op x y)) = (M.op X1 (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    intro X1
    first
    | (have i₁ := eq181198 x X1
       have i₂ := eq612 x sF3
       grind)
    | exact superpose eq612 eq181198
    | exact resolve eq181198 eq612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181198
  have eq181265 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq180168 eq181134
    | exact resolve eq181134 eq180168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181134
  have eq181319 : ∀ X1 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op X1 (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    intro X1
    first
    | exact superpose eq641 eq181238
    | exact resolve eq181238 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181238
  have eq181392 : ∀ X1 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op X1 (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    intro X1
    first
    | exact superpose eq180168 eq181319
    | exact resolve eq181319 eq180168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180168 eq181319
  have eq181448 : ∀ X1 : G, (k (σ y) (σ y)) = (M.op X1 (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    intro X1
    first
    | exact superpose eq181147 eq181392
    | exact resolve eq181392 eq181147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181147 eq181392
  have eq181490 : ∀ X1 : G, (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op X1 (σ y)) ∨ y = (M.op x y) := by
    intro X1
    first
    | exact superpose eq181265 eq181448
    | exact resolve eq181448 eq181265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181265 eq181448
  have eq182863 : ∀ X0 : G, (k x (τ (σ y))) = (τ (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op X0 (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq181490 eq2452
    | (have j1 := eq181490 X0
       grind)
    | exact resolve eq2452 eq181490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2452
  have eq182949 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op X0 (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq181490 eq636
    | (have j1 := eq181490 X0
       grind)
    | exact resolve eq636 eq181490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181490
  have eq182962 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op X0 (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq182949
    | (have j0 := eq182949 X0
       grind)
    | exact resolve eq182949 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182949
  have eq183011 : ∀ X0 : G, (k x (τ (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op X0 (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq31699 eq182863
    | (have j0 := eq182863 X0
       grind)
    | exact resolve eq182863 eq31699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182863
  have eq183044 : ∀ X0 : G, (k x y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op X0 (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq31 eq183011
    | (have j0 := eq183011 X0
       grind)
    | exact resolve eq183011 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183011
  have eq183066 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k x y) ∨ (σ y) = (M.op X0 (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq182962 eq183044
    | (have j0 := eq183044 X0
       have j1 := eq182962 X0
       grind)
    | exact resolve eq183044 eq182962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183044
  have eq183078 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k x (σ y)) ∨ (σ y) = (M.op X0 (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq76996 eq183066
    | (have j0 := eq183066 X0
       grind)
    | exact resolve eq183066 eq76996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76996 eq183066
  have eq183080 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq178480 eq183078
    | (have j0 := eq183078 X0
       have j1 := eq178480 X0
       grind)
    | exact resolve eq183078 eq178480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178480 eq183078
  have eq183313 : (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq183080 eq77052
    | exact resolve eq77052 eq183080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183487 : (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq183313
  have eq183599 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq183487
       have r₂ := eq77110
       grind)
    | exact resolve eq183487 eq77110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183487
  have eq183771 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq183599 eq27
    | exact resolve eq27 eq183599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183599
  have eq184130 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op X0 (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq182962 eq31685
    | (have j1 := eq182962 X0
       grind)
    | exact resolve eq31685 eq182962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182962
  have eq184221 : ∀ X0 : G, (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op X0 (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq183080 eq184130
    | (have j0 := eq184130 X0
       have j1 := eq183080 X0
       grind)
    | exact resolve eq184130 eq183080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183080 eq184130
  have eq184245 : ∀ X0 : G, (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op X0 (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq20 eq184221
    | (have j0 := eq184221 X0
       grind)
    | exact resolve eq184221 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184221
  have eq184261 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq184245 X0
       grind)
    | (have r₁ := eq184245 X0
       have r₂ := eq183771
       grind)
    | exact resolve eq184245 eq183771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183771 eq184245
  have eq184498 : (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq184261 eq77052
    | exact resolve eq77052 eq184261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77052 eq184261
  have eq184630 : (M.op x y) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq184498
  have eq184682 : y = (M.op x y) := by
    first
    | (have r₁ := eq184630
       have r₂ := eq77110
       grind)
    | exact resolve eq184630 eq77110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77110 eq184630
  have eq184814 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq184682
       grind)
    | exact superpose eq184682 eq18
    | exact resolve eq18 eq184682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq184815 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq184682
       grind)
    | exact superpose eq184682 eq24
    | exact resolve eq24 eq184682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq184816 : ∀ X0 : G, (k (σ y) (σ X0)) = (σ (k (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq184682
       grind)
    | exact superpose eq184682 eq36
    | exact resolve eq36 eq184682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq184817 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (k X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq184682
       grind)
    | exact superpose eq184682 eq40
    | exact resolve eq40 eq184682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq184828 : ∀ X0 : G, (σ (k X0 (k (M.op x y) (M.op x y)))) = (k (σ X0) (k (σ y) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq349 X0
       have i₂ := eq184682
       grind)
    | exact superpose eq184682 eq349
    | exact resolve eq349 eq184682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349
  have eq184833 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x X0) (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq613 X0
       have i₂ := eq184682
       grind)
    | exact superpose eq184682 eq613
    | exact resolve eq613 eq184682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613
  have eq184835 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq641
       have i₂ := eq184682
       grind)
    | exact superpose eq184682 eq641
    | exact resolve eq641 eq184682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184836 : (M.op x y) = (k x (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq1822
       have i₂ := eq184682
       grind)
    | exact superpose eq184682 eq1822
    | exact resolve eq1822 eq184682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1822
  have eq184837 : (σ (M.op (σ y) (M.op (σ x) (σ y)))) = (k (σ y) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq2449
       have i₂ := eq184682
       grind)
    | exact superpose eq184682 eq2449
    | exact resolve eq2449 eq184682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2449
  have eq184838 : (τ (M.op (σ y) (M.op (σ x) (σ y)))) = (k (M.op x y) (τ (M.op (σ y) (σ y)))) := by
    first
    | (have i₁ := eq2453
       have i₂ := eq184682
       grind)
    | exact superpose eq184682 eq2453
    | exact resolve eq2453 eq184682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2453
  have eq184925 : (M.op (σ y) (M.op (σ x) (σ y))) = (k (M.op x y) (τ (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq31699 eq184838
    | exact resolve eq184838 eq31699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31699 eq184838
  have eq184926 : (M.op (σ y) (M.op (σ x) (σ y))) = (k (σ y) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq31685 eq184837
    | exact resolve eq184837 eq31685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184837
  have eq184939 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (τ (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq184835 eq184925
    | exact resolve eq184925 eq184835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184925
  have eq184940 : (M.op (M.op x y) (M.op x y)) = (k (σ y) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq184835 eq184926
    | exact resolve eq184926 eq184835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184926
  have eq184955 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq184815 eq20
    | exact resolve eq20 eq184815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184958 : (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq184815 eq15
    | exact resolve eq15 eq184815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185025 : ∀ X0 : G, (τ (k X0 (σ y))) = (k (τ X0) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq184815 eq306
    | exact resolve eq306 eq184815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306
  have eq185037 : (τ (M.op (σ y) (M.op (σ x) (σ y)))) = (k (M.op x y) (τ (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq184815 eq2446
    | exact resolve eq2446 eq184815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2446 eq184815
  have eq185162 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq184939 eq185037
    | exact resolve eq185037 eq184939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184939 eq185037
  have eq185289 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq184835 eq185162
    | exact resolve eq185162 eq184835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185162
  have eq185451 : (σ (M.op (σ y) (M.op (σ x) (σ y)))) = (k (σ y) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq184955 eq2450
    | exact resolve eq2450 eq184955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185481 : (M.op (M.op x y) (M.op x y)) = (σ (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq184940 eq185451
    | exact resolve eq185451 eq184940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184940 eq185451
  have eq185516 : (M.op (M.op x y) (M.op x y)) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq184835 eq185481
    | exact resolve eq185481 eq184835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185481
  have eq186957 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x x) X0)) = (M.op X1 (M.op (M.op x y) (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq184814 eq576
    | exact resolve eq576 eq184814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576
  have eq186958 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op x X0) (M.op (M.op x y) (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq184814 eq591
    | exact resolve eq591 eq184814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591
  have eq186961 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op x y) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq184814 eq594
    | exact resolve eq594 eq184814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186969 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op x y) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq184833 eq186958
    | exact resolve eq186958 eq184833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184833 eq186958
  have eq186970 : ∀ X1 : G, (M.op y (M.op x y)) = (M.op X1 (M.op (M.op x y) (M.op x y))) := by
    intro X1
    first
    | (have i₁ := eq186957 x X1
       have i₂ := eq612 x (M.op x x)
       grind)
    | exact superpose eq612 eq186957
    | exact resolve eq186957 eq612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612 eq186957
  have eq186977 : ∀ X1 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op X1 (M.op (M.op x y) (M.op x y))) := by
    intro X1
    first
    | exact superpose eq641 eq186970
    | exact resolve eq186970 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641 eq186970
  have eq186979 : ∀ X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op X1 (M.op (M.op x y) (M.op x y))) := by
    intro X1
    first
    | exact superpose eq184835 eq186977
    | exact resolve eq186977 eq184835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186977
  have eq187031 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (σ (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq184835 eq32467
    | exact resolve eq32467 eq184835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32467
  have eq187110 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (σ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq187031
       have i₂ := eq184682
       grind)
    | exact superpose eq184682 eq187031
    | exact resolve eq187031 eq184682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187031
  have eq187135 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (σ (σ y)) := by
    first
    | (have i₁ := eq187110
       have i₂ := eq184682
       grind)
    | exact superpose eq184682 eq187110
    | exact resolve eq187110 eq184682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187110
  have eq187142 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (σ (σ y)) := by
    first
    | exact superpose eq39518 eq187135
    | (have j1 := eq39518 (M.op x y)
       grind)
    | exact resolve eq187135 eq39518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39518 eq187135
  have eq187143 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (σ (σ y)) := by grind
  clear eq187142
  have eq187360 : ∀ X0 : G, (σ (k X0 (M.op (M.op x y) (M.op x y)))) = (k (σ X0) (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq185289 eq38
    | exact resolve eq38 eq185289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq187546 : (k (M.op x y) (M.op x y)) = (σ (k (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq185516
       have i₂ := eq11 sF0 sF0
       grind)
    | exact superpose eq11 eq185516
    | (have j1 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq185516 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187547 : (σ (M.op (σ y) (M.op (σ x) (σ y)))) = (k (σ (M.op x y)) (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq185516 eq2450
    | exact resolve eq2450 eq185516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2450
  have eq187714 : (k (M.op x y) (M.op x y)) = (σ (k (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq187546
  have eq187843 : (σ (M.op (σ y) (M.op (σ x) (σ y)))) = (k (σ y) (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq184955 eq187547
    | exact resolve eq187547 eq184955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187547
  have eq187844 : (k (M.op x y) (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq41 eq187714
    | exact resolve eq187714 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187714
  have eq187941 : (M.op (σ y) (M.op (σ x) (σ y))) = (k (σ y) (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq31685 eq187843
    | exact resolve eq187843 eq31685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187843
  have eq187942 : (k (σ (M.op x y)) (σ y)) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq184955 eq187844
    | exact resolve eq187844 eq184955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187844
  have eq188003 : (M.op (M.op x y) (M.op x y)) = (k (σ y) (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq184835 eq187941
    | exact resolve eq187941 eq184835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187941
  have eq188004 : (k (σ (M.op x y)) (σ y)) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq20 eq187942
    | exact resolve eq187942 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187942
  have eq188041 : (k (σ y) (σ y)) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq184955 eq188004
    | exact resolve eq188004 eq184955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188004
  have eq188106 : (σ (M.op (σ y) (M.op (σ x) (σ y)))) = (k (σ y) (σ (k (M.op x y) (M.op x y)))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq184816 (k sF0 sF0)
       have i₂ := eq2409 sF0
       grind)
    | exact superpose eq2409 eq184816
    | (have j1 := eq2409 (M.op x y)
       grind)
    | exact resolve eq184816 eq2409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2409 eq184816
  have eq188521 : (σ (M.op (σ y) (M.op (σ x) (σ y)))) = (k (σ y) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq41 eq188106
    | exact resolve eq188106 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188106
  have eq188671 : (σ (M.op (σ y) (M.op (σ x) (σ y)))) = (k (σ y) (k (σ (M.op x y)) (σ y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq184955 eq188521
    | exact resolve eq188521 eq184955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188521
  have eq188767 : (σ (M.op (σ y) (M.op (σ x) (σ y)))) = (k (σ y) (k (σ (M.op x y)) (σ y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq20 eq188671
    | exact resolve eq188671 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188671
  have eq188816 : (σ (M.op (σ y) (M.op (σ x) (σ y)))) = (k (σ y) (k (σ y) (σ y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq184955 eq188767
    | exact resolve eq188767 eq184955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188767
  have eq188848 : (M.op (σ y) (M.op (σ x) (σ y))) = (k (σ y) (k (σ y) (σ y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq31685 eq188816
    | exact resolve eq188816 eq31685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31685 eq188816
  have eq188863 : (M.op (M.op x y) (M.op x y)) = (k (σ y) (k (σ y) (σ y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq184835 eq188848
    | exact resolve eq188848 eq184835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184835 eq188848
  have eq188873 : (M.op (M.op x y) (M.op x y)) = (k (σ y) (k (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq188041 eq188863
    | exact resolve eq188863 eq188041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188863
  have eq189869 : (k (τ (σ (σ x))) (M.op x y)) = (τ (σ (σ (M.op x y)))) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq180163 eq185025
    | exact resolve eq185025 eq180163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180163
  have eq189877 : (τ (M.op x y)) = (k (τ x) (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq180506 eq185025
    | exact resolve eq185025 eq180506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180506
  have eq190153 : (M.op x y) = (σ y) ∨ (τ (M.op x y)) = (k (τ x) (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq184955 eq189877
    | exact resolve eq189877 eq184955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189877
  have eq190154 : (τ (M.op x y)) = (k (τ x) (M.op x y)) ∨ (M.op x y) = (σ y) := by grind
  clear eq190153
  have eq190157 : (σ (M.op x y)) = (k (τ (σ (σ x))) (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | (have i₁ := eq189869
       have i₂ := eq15 sF1
       grind)
    | exact superpose eq15 eq189869
    | exact resolve eq189869 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189869
  have eq190219 : (σ (M.op x y)) = (k (σ x) (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | (have i₁ := eq190157
       have i₂ := eq15 sF2
       grind)
    | exact superpose eq15 eq190157
    | exact resolve eq190157 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190157
  have eq190247 : (σ y) = (k (σ x) (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq184955 eq190219
    | exact resolve eq190219 eq184955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190219
  have eq190259 : (M.op x y) = (σ y) ∨ (σ y) = (k (σ x) (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq184955 eq190247
    | exact resolve eq190247 eq184955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190247
  have eq190260 : (σ y) = (k (σ x) (M.op x y)) ∨ (M.op x y) = (σ y) := by grind
  clear eq190259
  have eq190287 : (σ (σ y)) = (k (σ (σ x)) (σ y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq190260 eq184817
    | exact resolve eq184817 eq190260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190260
  have eq192109 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq182 X0
       have i₂ := eq186969 X0 (M.op X0 X0)
       grind)
    | exact superpose eq186969 eq182
    | exact resolve eq182 eq186969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq193352 : (k (σ x) (σ (M.op x x))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq35 (M.op x x)
       have i₂ := eq192109 x
       grind)
    | exact superpose eq192109 eq35
    | exact resolve eq35 eq192109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193370 : (k x (τ (M.op (σ x) (σ x)))) = (τ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq90 (M.op sF2 sF2)
       have i₂ := eq192109 sF2
       grind)
    | exact superpose eq192109 eq90
    | exact resolve eq90 eq192109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq193397 : (M.op (M.op x y) (M.op x y)) = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | exact superpose eq185289 eq193370
    | exact resolve eq193370 eq185289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185289 eq193370
  have eq193413 : (M.op (M.op x y) (M.op x y)) = (k (σ x) (σ (M.op x x))) := by
    first
    | exact superpose eq185516 eq193352
    | exact resolve eq193352 eq185516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193352
  have eq195616 : (σ (τ (M.op x y))) = (k (σ (τ x)) (σ y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq190154 eq184817
    | exact resolve eq184817 eq190154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190154
  have eq195618 : (k x (σ y)) = (σ (τ (M.op x y))) ∨ (M.op x y) = (σ y) := by
    first
    | (have i₁ := eq195616
       have i₂ := eq14 x
       grind)
    | exact superpose eq14 eq195616
    | exact resolve eq195616 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195616
  have eq195627 : (M.op x y) = (k x (σ y)) ∨ (M.op x y) = (σ y) := by
    first
    | (have i₁ := eq195618
       have i₂ := eq14 sF0
       grind)
    | exact superpose eq14 eq195618
    | exact resolve eq195618 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195618
  have eq195665 : (σ (M.op x y)) = (k (σ x) (σ (σ y))) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq195627 eq35
    | exact resolve eq35 eq195627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq195627
  have eq195694 : (σ (M.op x y)) = (k (σ x) (σ (σ y))) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq20 eq195665
    | exact resolve eq195665 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195665
  have eq195707 : (σ y) = (k (σ x) (σ (σ y))) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq184955 eq195694
    | exact resolve eq195694 eq184955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195694
  have eq195741 : (σ y) = (k (σ x) (σ y)) ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq129800 eq195707
    | exact resolve eq195707 eq129800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195707
  have eq195803 : (M.op x y) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq184955 eq195741
    | exact resolve eq195741 eq184955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195741
  have eq195804 : (σ y) = (k (σ x) (σ y)) ∨ (M.op x y) = (σ y) := by grind
  clear eq195803
  have eq196049 : (σ (σ (σ y))) = (k (σ (σ (σ x))) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq190287 eq129819
    | exact resolve eq129819 eq190287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129819 eq190287
  have eq196062 : (M.op x y) = (σ y) ∨ (σ (σ (σ y))) = (k (σ (σ (σ x))) (σ y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq184955 eq196049
    | exact resolve eq196049 eq184955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196049
  have eq196063 : (σ (σ (σ y))) = (k (σ (σ (σ x))) (σ y)) ∨ (M.op x y) = (σ y) := by grind
  clear eq196062
  have eq205308 : (τ (σ (σ (σ y)))) = (k (τ (σ (σ (σ x)))) (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq196063 eq185025
    | exact resolve eq185025 eq196063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185025
  have eq205311 : (τ (σ (σ (σ y)))) = (k (σ (σ x)) (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | (have i₁ := eq205308
       have i₂ := eq15 (σ sF2)
       grind)
    | exact superpose eq15 eq205308
    | exact resolve eq205308 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205308
  have eq205349 : (σ (σ y)) = (k (σ (σ x)) (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | (have i₁ := eq205311
       have i₂ := eq15 (σ sF3)
       grind)
    | exact superpose eq15 eq205311
    | exact resolve eq205311 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205311
  have eq226518 : (σ (M.op (M.op x y) (M.op x y))) = (k (σ (σ y)) (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq188003 eq187360
    | exact resolve eq187360 eq188003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187360 eq188003
  have eq226996 : (M.op (M.op x y) (M.op x y)) = (k (σ (σ y)) (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq185516 eq226518
    | exact resolve eq226518 eq185516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226518
  have eq227293 : (k (M.op x y) (M.op x y)) = (k (σ (σ y)) (k (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq226996
       have i₂ := eq11 sF0 sF0
       grind)
    | exact superpose eq11 eq226996
    | (have j1 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq226996 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226996
  have eq227299 : (k (M.op x y) (M.op x y)) = (k (σ (σ y)) (k (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq227293
  have eq245989 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (σ (σ y)) := by
    first
    | exact superpose eq187143 eq192109
    | exact resolve eq192109 eq187143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187143 eq192109
  have eq262405 : (σ (M.op (M.op x y) (M.op x y))) = (k (σ (σ y)) (k (σ y) (σ y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq188873 eq184828
    | exact resolve eq184828 eq188873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184828 eq188873
  have eq262411 : (M.op (M.op x y) (M.op x y)) = (k (σ (σ y)) (k (σ y) (σ y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq185516 eq262405
    | exact resolve eq262405 eq185516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262405
  have eq262425 : (M.op (M.op x y) (M.op x y)) = (k (σ (σ y)) (k (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq188041 eq262411
    | exact resolve eq262411 eq188041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188041 eq262411
  have eq262439 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq227299 eq262425
    | exact resolve eq262425 eq227299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227299 eq262425
  have eq262451 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have j1 := eq13 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq262439
       have r₂ := eq13 (M.op x y) (k (M.op x y) (M.op x y))
       grind)
    | (have r₁ := eq262439
       have r₂ := eq13 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq262439 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262439
  have eq262552 : (k (M.op x y) (M.op x y)) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq262451 eq185516
    | exact resolve eq185516 eq262451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185516
  have eq262554 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op X0 (k (M.op x y) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq262451 eq186979
    | exact resolve eq186979 eq262451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq262667 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op (k (M.op x y) (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq262451 eq186969
    | exact resolve eq186969 eq262451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186969
  have eq262689 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op x y) (k (M.op x y) (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq262451 eq594
    | exact resolve eq594 eq262451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594
  have eq262691 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op x y) (k (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq262451 eq636
    | exact resolve eq636 eq262451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636
  have eq262693 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (k (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq262451 eq186961
    | exact resolve eq186961 eq262451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186961
  have eq262695 : (k (M.op x y) (M.op x y)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq262693 eq262691
    | exact resolve eq262691 eq262693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262691
  have eq262697 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (k (M.op x y) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq262693 eq262689
    | exact resolve eq262689 eq262693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262689 eq262693
  have eq262770 : (k (M.op x y) (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq41 eq262552
    | exact resolve eq262552 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq262552
  have eq262848 : (k (σ (M.op x y)) (σ y)) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq184955 eq262770
    | exact resolve eq262770 eq184955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262770
  have eq262906 : (k (σ (M.op x y)) (σ y)) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq20 eq262848
    | exact resolve eq262848 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262848
  have eq262953 : (k (σ y) (σ y)) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq184955 eq262906
    | exact resolve eq262906 eq184955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262906
  have eq294712 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (σ (σ y)) := by
    first
    | exact superpose eq245989 eq184817
    | exact resolve eq184817 eq245989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184817
  have eq294736 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (σ (σ y)) := by
    first
    | exact superpose eq20 eq294712
    | exact resolve eq294712 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294712
  have eq294761 : (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (σ (σ y)) := by
    first
    | exact superpose eq184955 eq294736
    | exact resolve eq294736 eq184955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294736
  have eq294783 : (σ y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (σ (σ y)) := by
    first
    | exact superpose eq262953 eq294761
    | exact resolve eq294761 eq262953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262953 eq294761
  have eq294800 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (σ y) ∨ (σ y) = (σ (σ y)) := by
    first
    | exact superpose eq245989 eq294783
    | exact resolve eq294783 eq245989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245989 eq294783
  have eq294846 : (k (σ x) (σ (M.op x y))) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ y) ∨ (σ y) = (σ (σ y)) := by
    first
    | (have i₁ := eq193413
       have i₂ := eq294800
       grind)
    | exact superpose eq294800 eq193413
    | exact resolve eq193413 eq294800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193413
  have eq294955 : (k (M.op x y) (M.op x y)) = (M.op x (M.op x y)) ∨ (M.op x y) = (σ y) ∨ (σ y) = (σ (σ y)) := by
    first
    | (have i₁ := eq262697 x x
       have i₂ := eq294800
       grind)
    | exact superpose eq294800 eq262697
    | exact resolve eq262697 eq294800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262697 eq294800
  have eq295003 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ y) ∨ (σ y) = (σ (σ y)) := by
    first
    | exact superpose eq184814 eq294955
    | exact resolve eq294955 eq184814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294955
  have eq295056 : (k (σ x) (σ (M.op x y))) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ y) ∨ (σ y) = (σ (σ y)) := by
    first
    | exact superpose eq262451 eq294846
    | exact resolve eq294846 eq262451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294846
  have eq295102 : (k (M.op x y) (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (M.op x y) = (σ y) ∨ (σ y) = (σ (σ y)) := by
    first
    | exact superpose eq20 eq295056
    | exact resolve eq295056 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295056
  have eq295137 : (k (σ x) (σ y)) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ y) ∨ (σ y) = (σ (σ y)) := by
    first
    | exact superpose eq184955 eq295102
    | exact resolve eq295102 eq184955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184955 eq295102
  have eq295160 : (σ y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ y) ∨ (σ y) = (σ (σ y)) := by
    first
    | exact superpose eq195804 eq295137
    | exact resolve eq295137 eq195804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195804 eq295137
  have eq295175 : (M.op x y) = (σ y) ∨ (M.op x y) = (σ y) ∨ (σ y) = (σ (σ y)) := by
    first
    | exact superpose eq295003 eq295160
    | exact resolve eq295160 eq295003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295003 eq295160
  have eq295176 : (σ y) = (σ (σ y)) ∨ (M.op x y) = (σ y) := by grind
  clear eq295175
  have eq295216 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (k X0 (σ y))) ∨ (M.op x y) = (σ y) := by
    intro X0
    first
    | exact superpose eq295176 eq10
    | exact resolve eq10 eq295176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq304957 : ∀ X0 : G, (τ (k (σ X0) (σ y))) = (k X0 (σ y)) ∨ (M.op x y) = (σ y) := by
    intro X0
    first
    | exact superpose eq295216 eq15
    | exact resolve eq15 eq295216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295216
  have eq305330 : ∀ X0 : G, (k X0 y) = (k X0 (σ y)) ∨ (M.op x y) = (σ y) := by
    intro X0
    first
    | exact superpose eq72 eq304957
    | exact resolve eq304957 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304957
  have eq305615 : ∀ X0 : G, (k X0 (M.op x y)) = (k X0 (σ y)) ∨ (M.op x y) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq305330 X0
       have i₂ := eq184682
       grind)
    | exact superpose eq184682 eq305330
    | exact resolve eq305330 eq184682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305330
  have eq306121 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (M.op x y))) ∨ (M.op x y) = (σ y) := by
    intro X0
    first
    | exact superpose eq305615 eq72
    | exact resolve eq72 eq305615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq306148 : (σ (σ (σ y))) = (k (σ (σ (σ x))) (M.op x y)) ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq305615 eq196063
    | exact resolve eq196063 eq305615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196063 eq305615
  have eq306405 : (σ (σ (σ y))) = (k (σ (σ (σ x))) (M.op x y)) ∨ (M.op x y) = (σ y) := by grind
  clear eq306148
  have eq306560 : (σ (σ y)) = (k (σ (σ (σ x))) (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq295176 eq306405
    | exact resolve eq306405 eq295176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306405
  have eq306584 : ∀ X0 : G, (k X0 y) = (k X0 (τ (M.op x y))) ∨ (M.op x y) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq306121 X0
       have i₂ := eq363 X0 sF0
       grind)
    | exact superpose eq363 eq306121
    | exact resolve eq306121 eq363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306121
  have eq306726 : (σ y) = (k (σ (σ (σ x))) (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq295176 eq306560
    | exact resolve eq306560 eq295176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306560
  have eq306742 : ∀ X0 : G, (k X0 (M.op x y)) = (k X0 (τ (M.op x y))) ∨ (M.op x y) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq306584 X0
       have i₂ := eq184682
       grind)
    | exact superpose eq184682 eq306584
    | exact resolve eq306584 eq184682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306584
  have eq307057 : (τ (σ y)) = (k (σ (σ x)) (τ (M.op x y))) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq306726 eq363
    | exact resolve eq363 eq306726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363 eq306726
  have eq307079 : y = (k (σ (σ x)) (τ (M.op x y))) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq31 eq307057
    | exact resolve eq307057 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq307057
  have eq307086 : (M.op x y) = (k (σ (σ x)) (τ (M.op x y))) ∨ (M.op x y) = (σ y) := by
    first
    | (have i₁ := eq307079
       have i₂ := eq184682
       grind)
    | exact superpose eq184682 eq307079
    | exact resolve eq307079 eq184682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307079
  have eq307247 : (M.op x y) = (k (σ (σ x)) (M.op x y)) ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq306742 eq307086
    | exact resolve eq307086 eq306742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306742 eq307086
  have eq307416 : (M.op x y) = (k (σ (σ x)) (M.op x y)) ∨ (M.op x y) = (σ y) := by grind
  clear eq307247
  have eq307954 : (M.op x y) = (σ (σ y)) ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq307416 eq205349
    | exact resolve eq205349 eq307416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205349 eq307416
  have eq307973 : (M.op x y) = (σ (σ y)) ∨ (M.op x y) = (σ y) := by grind
  clear eq307954
  have eq308090 : (M.op x y) = (σ y) ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq307973 eq295176
    | exact resolve eq295176 eq307973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295176 eq307973
  have eq308270 : (M.op x y) = (σ y) := by grind
  clear eq308090
  have eq308510 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq308270 eq26
    | exact resolve eq26 eq308270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq308595 : (M.op x y) = (M.op (M.op x y) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq308270 eq32216
    | exact resolve eq32216 eq308270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32216
  have eq308809 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq308270 eq129800
    | exact resolve eq129800 eq308270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129800
  have eq308892 : (M.op x y) = (τ (M.op x y)) := by
    first
    | exact superpose eq308270 eq184958
    | exact resolve eq184958 eq308270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184958
  have eq308930 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq308270 eq262695
    | exact resolve eq262695 eq308270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262695 eq308270
  have eq309022 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq20 eq308809
    | exact resolve eq308809 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq308809
  have eq309023 : (M.op x y) = (σ (M.op x y)) := by grind
  clear eq309022
  have eq309133 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq308930 eq308595
    | exact resolve eq308595 eq308930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308595 eq308930
  have eq309291 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq309133
       have i₂ := eq184682
       grind)
    | exact superpose eq184682 eq309133
    | exact resolve eq309133 eq184682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309133
  have eq309361 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq1836 (M.op x y)
       grind)
    | (have r₁ := eq309291
       have r₂ := eq1836 (M.op x y)
       grind)
    | exact resolve eq309291 eq1836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309291
  have eq309406 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq262451 eq309361
    | exact resolve eq309361 eq262451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309361
  have eq309421 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq309406
       have i₂ := eq184682
       grind)
    | exact superpose eq184682 eq309406
    | exact resolve eq309406 eq184682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184682 eq309406
  have eq402284 : ∀ X0 : G, (M.op x y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq309421 eq262554
    | exact resolve eq262554 eq309421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309421
  have eq402632 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (k x (τ (M.op x y))) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq402284 eq193397
    | (have j1 := eq402284 X0
       grind)
    | exact resolve eq193397 eq402284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193397 eq402284
  have eq402815 : ∀ X0 : G, (k x (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq308892 eq402632
    | (have j0 := eq402632 X0
       grind)
    | exact resolve eq402632 eq308892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308892 eq402632
  have eq402866 : ∀ X0 : G, (k x (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq402815 X0
       have j1 := eq13 x (M.op x y)
       grind)
    | (have r₁ := eq402815 X0
       have r₂ := eq13 (M.op x y) (k x (M.op x y))
       grind)
    | (have r₁ := eq402815 X0
       have r₂ := eq13 x (M.op x y)
       grind)
    | (have r₁ := eq402815 (M.op x y)
       have r₂ := eq13 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq402815 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402815
  have eq402901 : ∀ X0 : G, (k x (M.op x y)) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq262451 eq402866
    | (have j0 := eq402866 X0
       grind)
    | exact resolve eq402866 eq262451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402866
  have eq402953 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq402901 eq184836
    | (have j1 := eq402901 (M.op x y)
       grind)
    | exact resolve eq184836 eq402901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184836 eq402901
  have eq402997 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq402953 (M.op x y)
       have j1 := eq1836 (M.op x y)
       grind)
    | (have r₁ := eq402953 X0
       have r₂ := eq1836 (M.op x y)
       grind)
    | exact resolve eq402953 eq1836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1836 eq402953
  have eq403014 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq262451 eq402997
    | (have j0 := eq402997 X0
       grind)
    | exact resolve eq402997 eq262451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402997
  have eq441401 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op X1 (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq403014 eq262667
    | (have j1 := eq403014 X1
       grind)
    | exact resolve eq262667 eq403014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262667 eq403014
  have eq442884 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have j0 := eq441401 (M.op x y) (M.op x y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441401
  have eq442885 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq442884
  have eq442895 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq262451 eq442885
    | exact resolve eq442885 eq262451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262451 eq442885
  have eq443410 : ∀ X0 : G, (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq442895 eq262554
    | exact resolve eq262554 eq442895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262554 eq442895
  have eq443817 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op X1 (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 x x x
       have i₂ := eq443410 X0
       grind)
    | exact superpose eq443410 eq16
    | (have j1 := eq443410 X1
       grind)
    | exact resolve eq16 eq443410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443410
  have eq443863 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ (M.op x y) = (M.op X1 (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq184814 eq443817
    | (have j0 := eq443817 X0 X1
       grind)
    | exact resolve eq443817 eq184814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184814 eq443817
  have eq445662 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have j0 := eq443863 (M.op x y) (M.op x y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443863
  have eq445663 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq445662
  have eq446177 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq445663 eq186979
    | exact resolve eq186979 eq445663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186979 eq445663
  have eq447166 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq446177 eq308510
    | exact resolve eq308510 eq446177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308510 eq446177
  have eq447729 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq447166 eq27
    | exact resolve eq27 eq447166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq447166
  have eq447811 : False := by grind
  exact eq447811

/-- `Equation4452`: `x ◇ (y ◇ x) = (z ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_pxx_x_pxy_Equation4452 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4452 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4452.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X0) X0) := by
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
  have eq36 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
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
  have eq45 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq35
    | (have j0 := eq35 (M.op x y)
       grind)
    | exact resolve eq35 eq20
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
  have eq52 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X3 X1) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq14 X1 x X3
       have i₂ := eq14 X1 x X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X0)) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 X2 (M.op x X0)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op y (M.op X0 y)) = (M.op (M.op x y) y) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y X0 x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op (σ y) (M.op X0 (σ y))) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 X1 x
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq69 : x ≠ (M.op x y) ∨ (k y x) = (M.op y y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq36 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq36
    | exact resolve eq36 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : (k (σ y) (σ x)) = (σ (k y x)) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq36
    | (have j0 := eq36 x
       grind)
    | exact resolve eq36 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq36
    | (have j0 := eq36 y
       grind)
    | exact resolve eq36 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) ≠ (M.op X2 X0) ∨ (M.op X0 (M.op X2 X0)) = X0 ∨ (M.op X2 X0) = (k (M.op X2 X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X2 X0) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 (M.op X2 X0) X0
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq77
       grind)
    | exact superpose eq77 eq16
    | exact resolve eq16 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq78
       grind)
    | exact superpose eq78 eq16
    | exact resolve eq16 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq100 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq35 eq11
    | (have j0 := eq11 (σ x) (σ X0)
       grind)
    | exact resolve eq11 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq101 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq11 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq105 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq43
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq43
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq43 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
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
  clear eq44
  have eq108 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq78
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq78
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq78 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq108
  have eq116 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq105
  have eq118 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq107
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq107
    | exact resolve eq107 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq121 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq118
    | exact resolve eq118 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq122 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq121
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq121
    | exact resolve eq121 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq131 : ∀ X0 : G, (σ (k (M.op x y) (τ X0))) = (k (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq37 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq37
    | exact resolve eq37 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq156 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq139 eq16
    | exact resolve eq16 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218 : (M.op (M.op x y) y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq55 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq55
    | (have j0 := eq55 x
       grind)
    | exact resolve eq55 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219 : ∀ X0 : G, (M.op (M.op X0 y) y) = (M.op (M.op x y) y) := by
    intro X0
    first
    | (have i₁ := eq55 x
       have i₂ := eq14 y x X0
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq226 : (M.op x y) ≠ (M.op y (M.op x y)) ∨ y = (M.op y (M.op x y)) ∨ (M.op x y) = (k (M.op x y) y) := by
    first
    | exact superpose eq218 eq12
    | (have j0 := eq12 (M.op x y) y
       grind)
    | exact resolve eq12 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq232 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq56
    | (have j0 := eq56 (σ x)
       grind)
    | exact resolve eq56 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq233 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq56 x
       have i₂ := eq14 sF3 x x
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq239 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq232 eq56
    | exact resolve eq56 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq242 : ∀ X0 : G, (M.op (σ y) (M.op X0 (σ y))) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | exact superpose eq232 eq14
    | exact resolve eq14 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq243 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq56 eq242
    | exact resolve eq242 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242
  have eq244 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq232 eq243
    | exact resolve eq243 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq307 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  clear eq34
  have eq363 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  clear eq38
  have eq373 : ∀ X0 : G, (M.op (M.op X0 y) y) = (M.op y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq218 eq219
    | exact resolve eq219 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq375 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq232 eq233
    | exact resolve eq233 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq853 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) ≠ (M.op X0 (M.op X2 X0)) ∨ (M.op X0 X0) = (k X0 (M.op X0 (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op X0 (M.op X2 X0))
       have i₂ := eq54 X0 X2 X1
       grind)
    | exact superpose eq54 eq13
    | (have j0 := eq13 X0 (M.op X0 (M.op X2 X0))
       grind)
    | (have r₁ := eq13 X0 (M.op X0 (M.op X2 X0))
       have r₂ := eq54 X0 X2 X2
       grind)
    | exact resolve eq13 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq870 : ∀ X0 X2 : G, (M.op X0 X0) = (k X0 (M.op X0 (M.op X2 X0))) := by
    intro X0 X2
    first
    | (have j0 := eq853 X0 x X2
       grind)
    | (have r₁ := eq853 X0 x X2
       have r₂ := eq57 X0 x X2
       grind)
    | (have r₁ := eq853 X0 X2 x
       have r₂ := eq57 X0 x X2
       grind)
    | exact resolve eq853 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq853
  have eq1352 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq307 X0 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq307
    | (have j0 := eq307 X0 y
       grind)
    | exact resolve eq307 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1353 : ∀ X0 : G, (k (τ X0) (M.op x y)) = (τ (k X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq20 eq307
    | (have j0 := eq307 X0 (M.op x y)
       grind)
    | exact resolve eq307 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307
  have eq1435 : ∀ X0 : G, (M.op (σ y) (M.op X0 (σ y))) ≠ (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (M.op (σ y) (M.op (σ x) (σ y))) = (k (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | exact superpose eq375 eq81
    | (have r₁ := eq81 (σ y) (σ x) (M.op X0 (σ y))
       have r₂ := eq375 X0
       grind)
    | exact resolve eq81 eq375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq1442 : (M.op (M.op (σ x) (σ y)) (σ y)) ≠ (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (M.op (σ y) (M.op (σ x) (σ y))) = (k (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq56 eq1435
    | exact resolve eq1435 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq1435
  have eq1460 : (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (M.op (σ y) (M.op (σ x) (σ y))) = (k (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | (have r₁ := eq1442
       have r₂ := eq232
       grind)
    | exact resolve eq1442 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1442
  have eq1474 : (M.op (σ y) (M.op (σ x) (σ y))) = (k (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) ∨ (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq239 eq1460
    | exact resolve eq1460 eq239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1460
  have eq1626 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq99 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq10986 : (M.op y y) = (τ (k (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq115
       grind)
    | exact superpose eq115 eq16
    | exact resolve eq16 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq11017 : (M.op y y) = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq93 eq10986
    | exact resolve eq10986 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10986
  have eq11020 : (M.op y y) = (k y y) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq11017
       have r₂ := eq13 y y
       grind)
    | exact resolve eq11017 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11017
  have eq11022 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq78
       have i₂ := eq11020
       grind)
    | exact superpose eq11020 eq78
    | exact resolve eq78 eq11020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11430 : (τ (k (σ x) (σ x))) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq116
       grind)
    | exact superpose eq116 eq16
    | exact resolve eq16 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq11463 : (k x x) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq49 eq11430
    | exact resolve eq11430 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq11430
  have eq11466 : (k x x) = (M.op x x) := by
    first
    | (have j1 := eq13 x x
       grind)
    | (have r₁ := eq11463
       have r₂ := eq13 x x
       grind)
    | exact resolve eq11463 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11463
  have eq11467 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq11466
       grind)
    | exact superpose eq11466 eq43
    | exact resolve eq43 eq11466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11466
  have eq12137 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq122 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12138 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq12137
    | exact resolve eq12137 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12137
  have eq12149 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq12138
       have r₂ := eq27
       grind)
    | exact resolve eq12138 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12138
  have eq12151 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq12149
    | exact resolve eq12149 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12149
  have eq12153 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq12151 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq12151
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq12151
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq12151
       grind)
    | exact resolve eq12 eq12151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12151
  have eq12190 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq12153
  have eq12216 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq12190
    | exact resolve eq12190 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12190
  have eq12217 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq12216
  have eq12222 : (τ (σ y)) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq12217 eq88
    | exact resolve eq88 eq12217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12217
  have eq12238 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq12222
    | exact resolve eq12222 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12222
  have eq12251 : y = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq12238
       grind)
    | exact superpose eq12238 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq12238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12238
  have eq12252 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq12251
  have eq12254 : x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12252
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12252
    | exact resolve eq12252 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12252
  have eq12255 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12254
  have eq12686 : y ≠ y ∨ x = (M.op x y) ∨ y = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq12255
       grind)
    | exact superpose eq12255 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq12255
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq12255
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq12255
       grind)
    | exact resolve eq12 eq12255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12697 : ∀ X0 : G, (M.op x y) = (M.op x (M.op X0 x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq57 x X0 y
       have i₂ := eq12255
       grind)
    | exact superpose eq12255 eq57
    | exact resolve eq57 eq12255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12725 : x = (M.op x y) ∨ y = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12686
  have eq12747 : ∀ X0 : G, (M.op x y) = (M.op x (M.op X0 x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq12697 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12697
    | (have j0 := eq12697 X0
       grind)
    | exact resolve eq12697 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12697
  have eq12753 : x = (M.op x y) ∨ y = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12725
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12725
    | exact resolve eq12725 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12725
  have eq12754 : y = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12753
  have eq12758 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq77
       have i₂ := eq12754
       grind)
    | exact superpose eq12754 eq77
    | exact resolve eq77 eq12754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12754
  have eq12774 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12758
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12758
    | exact resolve eq12758 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12758
  have eq12785 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12774 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq12774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12774
  have eq12786 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12785
  have eq12788 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12786
    | exact resolve eq12786 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12786
  have eq12789 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq12788
  have eq12814 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X0 (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq12789 eq57
    | exact resolve eq57 eq12789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12864 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X0 (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq12814
    | (have j0 := eq12814 X0
       grind)
    | exact resolve eq12814 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12814
  have eq13338 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 x) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq12747 x
       have i₂ := eq14 x x X0
       grind)
    | exact superpose eq14 eq12747
    | exact resolve eq12747 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12747
  have eq13511 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13338 y
       have i₂ := eq12255
       grind)
    | exact superpose eq12255 eq13338
    | exact resolve eq13338 eq12255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13338
  have eq13596 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq13511
  have eq13640 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12255
       have i₂ := eq13596
       grind)
    | exact superpose eq13596 eq12255
    | exact resolve eq12255 eq13596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12255 eq13596
  have eq13685 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq13640
  have eq13687 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13685 eq27
    | exact resolve eq27 eq13685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13688 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13685 eq70
    | (have r₁ := eq70
       have r₂ := eq13685
       grind)
    | exact resolve eq70 eq13685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13689 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13685 eq83
    | (have r₁ := eq83
       have r₂ := eq13685
       grind)
    | exact resolve eq83 eq13685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq13690 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13685 eq232
    | exact resolve eq232 eq13685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13691 : (M.op (σ y) (σ x)) = (M.op (σ y) (M.op (σ y) (σ x))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13685 eq239
    | exact resolve eq239 eq13685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13693 : (M.op (σ y) (σ x)) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13685 eq244
    | exact resolve eq244 eq13685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244
  have eq13698 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq13689
  have eq13699 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq13688
  have eq13700 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq13690
    | exact resolve eq13690 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13690
  have eq15350 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ x)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq12864 x
       have i₂ := eq14 sF2 x x
       grind)
    | exact superpose eq14 eq12864
    | exact resolve eq12864 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12864
  have eq15517 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12789 eq15350
    | exact resolve eq15350 eq12789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15350
  have eq15610 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq15517
  have eq15661 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15610 eq12789
    | exact resolve eq12789 eq15610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12789 eq15610
  have eq15713 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq15661
  have eq15716 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15713 eq27
    | exact resolve eq27 eq15713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15713
  have eq31886 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq100 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq100
    | (have j0 := eq100 x
       grind)
    | exact resolve eq100 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq31972 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq31886
  have eq31977 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq31972
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq31972
    | exact resolve eq31972 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq31972
  have eq32011 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq31977
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq31977 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31977
  have eq32113 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq101 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq101
    | (have j0 := eq101 y
       grind)
    | exact resolve eq101 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq32198 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq32113
  have eq32202 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq32198
       have i₂ := eq78
       grind)
    | exact superpose eq78 eq32198
    | exact resolve eq32198 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32198
  have eq32237 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq32202
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq32202 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32202
  have eq32243 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13700 eq13691
    | exact resolve eq13691 eq13700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13691
  have eq32333 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq32243
  have eq32563 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13685 eq32333
    | exact resolve eq32333 eq13685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32582 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq32333 eq52
    | exact resolve eq52 eq32333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq32630 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32333 eq870
    | exact resolve eq870 eq32333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq870
  have eq32659 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq32563
  have eq32798 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13693 eq375
    | exact resolve eq375 eq13693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375
  have eq41987 : (M.op (σ y) (σ x)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32798 eq13693
    | exact resolve eq13693 eq32798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13693 eq32798
  have eq42103 : (M.op (σ y) (σ x)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq41987
  have eq53267 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq42103 eq32582
    | exact resolve eq32582 eq42103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32582 eq42103
  have eq53461 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq53267
  have eq62567 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32659 eq53461
    | exact resolve eq53461 eq32659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32659 eq53461
  have eq62717 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq62567
  have eq62722 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq62717 eq32630
    | exact resolve eq32630 eq62717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32630 eq62717
  have eq62851 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq62722
  have eq98681 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13698 eq13700
    | exact resolve eq13700 eq13698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13698 eq13700
  have eq98875 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq98681
  have eq99029 : (τ (σ x)) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq98875 eq61
    | exact resolve eq61 eq98875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq99030 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq98875 eq122
    | exact resolve eq122 eq98875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq98875
  have eq99049 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq99030
  have eq99062 : y = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq99049
       have r₂ := eq13687
       grind)
    | exact resolve eq99049 eq13687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13687 eq99049
  have eq99063 : x = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq99029
    | exact resolve eq99029 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99029
  have eq99086 : y ≠ y ∨ (k x y) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq99062
       grind)
    | exact superpose eq99062 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq99062
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq99062
       grind)
    | exact resolve eq13 eq99062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99096 : ∀ X0 : G, (M.op x y) = (M.op x (M.op X0 x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq57 x X0 y
       have i₂ := eq99062
       grind)
    | exact superpose eq99062 eq57
    | exact resolve eq57 eq99062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99062
  have eq99226 : (k x y) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq99086
  have eq99334 : ∀ X0 : G, (M.op x y) = (M.op x (M.op X0 x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq99096 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq99096
    | (have j0 := eq99096 X0
       grind)
    | exact resolve eq99096 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99096
  have eq120674 : x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq99063
       have i₂ := eq99226
       grind)
    | exact superpose eq99226 eq99063
    | exact resolve eq99063 eq99226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99063 eq99226
  have eq120680 : x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq120674
  have eq130851 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq99334 x
       have i₂ := eq120680
       grind)
    | exact superpose eq120680 eq99334
    | exact resolve eq99334 eq120680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99334
  have eq131186 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq130851
  have eq131208 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq120680
       have i₂ := eq131186
       grind)
    | exact superpose eq131186 eq120680
    | exact resolve eq120680 eq131186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120680 eq131186
  have eq131398 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq131208
  have eq131425 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq131398 eq13685
    | exact resolve eq13685 eq131398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131452 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq131398 eq32333
    | exact resolve eq32333 eq131398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32333
  have eq131492 : (M.op (σ x) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq131398 eq62851
    | exact resolve eq62851 eq131398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62851 eq131398
  have eq131543 : (M.op (σ x) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq131492
  have eq131582 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq131452
  have eq131608 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq131425
  have eq131624 : (M.op (σ x) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq131543
    | exact resolve eq131543 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131543
  have eq133753 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq131608 eq29
    | exact resolve eq29 eq131608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134006 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq28 eq133753
    | exact resolve eq133753 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133753
  have eq134054 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ (M.op x y)) X0) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq134006 eq131
    | exact resolve eq131 eq134006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq134006
  have eq134242 : ∀ X0 : G, (k (σ y) X0) = (k (σ (M.op x y)) X0) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq134054 X0
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq134054
    | exact resolve eq134054 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq134054
  have eq135348 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq131582 eq13
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq131582
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq131582
       grind)
    | exact resolve eq13 eq131582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131582
  have eq135518 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq135348
  have eq135643 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13685 eq131624
    | exact resolve eq131624 eq13685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13685 eq131624
  have eq135652 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq135643
  have eq143527 : (τ (σ y)) = (k y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq135518 eq93
    | exact resolve eq93 eq135518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135518
  have eq143557 : (τ (σ y)) = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq143527
       have i₂ := eq11020
       grind)
    | exact superpose eq11020 eq143527
    | exact resolve eq143527 eq11020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143527
  have eq143566 : y = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq143557
    | exact resolve eq143557 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143557
  have eq145905 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq135652 eq13699
    | exact resolve eq13699 eq135652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13699 eq135652
  have eq145913 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq145905
  have eq161984 : (M.op y y) = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq373 y
       have i₂ := eq143566
       grind)
    | exact superpose eq143566 eq373
    | exact resolve eq373 eq143566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143566
  have eq163882 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq145913 eq13
    | (have r₁ := eq13 y x
       have r₂ := eq145913
       grind)
    | exact resolve eq13 eq145913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145913
  have eq164266 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq163882
       have r₂ := eq131608
       grind)
    | exact resolve eq163882 eq131608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131608 eq163882
  have eq167186 : (τ (σ x)) = (k y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq164266 eq93
    | exact resolve eq93 eq164266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164266
  have eq167227 : (τ (σ x)) = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq167186
       have i₂ := eq11020
       grind)
    | exact superpose eq11020 eq167186
    | exact resolve eq167186 eq11020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167186
  have eq167236 : x = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq167227
    | exact resolve eq167227 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167227
  have eq170106 : (M.op x y) = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq373 y
       have i₂ := eq167236
       grind)
    | exact superpose eq167236 eq373
    | exact resolve eq373 eq167236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq170498 : (M.op x y) = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq170106
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq170106
    | exact resolve eq170106 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170106
  have eq268113 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq161984 eq170498
    | exact resolve eq170498 eq161984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161984 eq170498
  have eq268375 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq268113
  have eq268547 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq167236
       have i₂ := eq268375
       grind)
    | exact superpose eq268375 eq167236
    | exact resolve eq167236 eq268375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167236 eq268375
  have eq268815 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq268547
  have eq269255 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq268815 eq20
    | exact resolve eq20 eq268815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq269272 : (σ (k y y)) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq268815 eq139
    | exact resolve eq139 eq268815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq269318 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ (M.op x y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq268815 eq1353
    | exact resolve eq1353 eq268815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1353
  have eq269357 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq268815
  have eq269365 : ∀ X0 : G, (τ (k X0 (σ y))) = (τ (k X0 (σ (M.op x y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq269318 X0
       have i₂ := eq1352 X0
       grind)
    | exact superpose eq1352 eq269318
    | exact resolve eq269318 eq1352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1352 eq269318
  have eq269402 : (k (σ y) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq269272
       have i₂ := eq78
       grind)
    | exact superpose eq78 eq269272
    | exact resolve eq269272 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq269272
  have eq269419 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq269255
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq269255
    | exact resolve eq269255 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269255
  have eq270748 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq269419 eq15716
    | (have r₁ := eq15716
       have r₂ := eq269419
       grind)
    | exact resolve eq15716 eq269419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15716
  have eq270933 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq270748
  have eq270934 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq270933
  have eq271020 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq270934 eq70
    | (have r₁ := eq70
       have r₂ := eq270934
       grind)
    | exact resolve eq70 eq270934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq271022 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq270934 eq232
    | exact resolve eq232 eq270934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq271023 : (M.op (σ y) (σ x)) = (M.op (σ y) (M.op (σ y) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq270934 eq239
    | exact resolve eq239 eq270934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq271223 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq271020
  have eq271227 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq271022
    | exact resolve eq271022 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271022
  have eq274591 : (k y y) = (τ (k (σ (M.op x y)) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq269402 eq93
    | exact resolve eq93 eq269402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq269402
  have eq274669 : (k y y) = (k (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq156 eq274591
    | exact resolve eq274591 eq156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274591
  have eq274680 : (M.op y y) = (k (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq274669
       have i₂ := eq11020
       grind)
    | exact superpose eq11020 eq274669
    | exact resolve eq274669 eq11020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11020 eq274669
  have eq292041 : (k y x) = (τ (M.op (σ y) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq271223 eq88
    | exact resolve eq88 eq271223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271223
  have eq324563 : ∀ X0 : G, (k X0 (τ (σ y))) = (τ (k (σ X0) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq269365 eq363
    | exact resolve eq363 eq269365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269365
  have eq324676 : ∀ X0 : G, (k X0 (τ (σ (M.op x y)))) = (k X0 (τ (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq324563 X0
       have i₂ := eq363 X0 sF1
       grind)
    | exact superpose eq363 eq324563
    | exact resolve eq324563 eq363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363 eq324563
  have eq324703 : ∀ X0 : G, (k X0 y) = (k X0 (τ (σ (M.op x y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29 eq324676
    | exact resolve eq324676 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324676
  have eq324718 : ∀ X0 : G, (k X0 y) = (k X0 (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq30 eq324703
    | exact resolve eq324703 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq324703
  have eq338995 : (M.op (σ y) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq32237 eq134242
    | exact resolve eq134242 eq32237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134242
  have eq339023 : (M.op (σ y) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq338995
       have r₂ := eq269357
       grind)
    | exact resolve eq338995 eq269357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269357 eq338995
  have eq339050 : (τ (M.op (σ y) (σ y))) = (k (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq339023 eq156
    | exact resolve eq156 eq339023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156 eq339023
  have eq340022 : (k y x) = (k (M.op x y) y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq339050 eq292041
    | exact resolve eq292041 eq339050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292041 eq339050
  have eq340053 : (k y x) = (k (M.op x y) y) ∨ x = (M.op x y) := by grind
  clear eq340022
  have eq340091 : (k y x) = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq340053 eq274680
    | exact resolve eq274680 eq340053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274680 eq340053
  have eq340112 : (k y x) = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq340091
  have eq340135 : (k y x) = (M.op y y) := by
    first
    | (have r₁ := eq340112
       have r₂ := eq69
       grind)
    | exact resolve eq340112 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq340112
  have eq340248 : (k (σ y) (σ x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq77
       have i₂ := eq340135
       grind)
    | exact superpose eq340135 eq77
    | exact resolve eq77 eq340135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq340303 : (k (σ y) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq340248
       have i₂ := eq11022
       grind)
    | exact superpose eq11022 eq340248
    | exact resolve eq340248 eq11022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11022 eq340248
  have eq340324 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq32237 eq340303
    | exact resolve eq340303 eq32237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32237 eq340303
  have eq340433 : (k y x) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq340324 eq88
    | exact resolve eq88 eq340324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq340482 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq340433
       have i₂ := eq340135
       grind)
    | exact superpose eq340135 eq340433
    | exact resolve eq340433 eq340135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340135 eq340433
  have eq341832 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq271227 eq271023
    | exact resolve eq271023 eq271227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271023 eq271227
  have eq342216 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq341832
  have eq368397 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq342216 eq1474
    | exact resolve eq1474 eq342216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1474 eq342216
  have eq368434 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq269419 eq368397
    | exact resolve eq368397 eq269419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269419 eq368397
  have eq368474 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq368434
  have eq368481 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq368474
       have r₂ := eq27
       grind)
    | exact resolve eq368474 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368474
  have eq368484 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq270934 eq368481
    | exact resolve eq368481 eq270934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270934 eq368481
  have eq368512 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq368484
  have eq368619 : (τ (σ x)) = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq368512 eq65
    | exact resolve eq65 eq368512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq368512
  have eq368659 : x = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq368619
    | exact resolve eq368619 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq368619
  have eq368692 : x = (k x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq368659 eq324718
    | exact resolve eq324718 eq368659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324718 eq368659
  have eq368710 : x = (k x y) ∨ x = (M.op x y) := by grind
  clear eq368692
  have eq368820 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq368710
       grind)
    | exact superpose eq368710 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq368710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq368836 : x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq368820
  have eq368861 : x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq368836
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq368836
    | exact resolve eq368836 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368836
  have eq368862 : y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq368861
  have eq369058 : y ≠ y ∨ (k x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq368862
       grind)
    | exact superpose eq368862 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq368862
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq368862
       grind)
    | exact resolve eq13 eq368862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq369068 : ∀ X0 : G, (M.op x y) = (M.op x (M.op X0 x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq57 x X0 y
       have i₂ := eq368862
       grind)
    | exact superpose eq368862 eq57
    | exact resolve eq57 eq368862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq368862
  have eq369368 : (k x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq369058
  have eq369568 : ∀ X0 : G, (M.op x y) = (M.op x (M.op X0 x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq369068 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq369068
    | (have j0 := eq369068 X0
       grind)
    | exact resolve eq369068 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369068
  have eq379989 : x = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq368710
       have i₂ := eq369368
       grind)
    | exact superpose eq369368 eq368710
    | exact resolve eq368710 eq369368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368710 eq369368
  have eq380006 : x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq379989
  have eq381100 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq369568 x
       have i₂ := eq380006
       grind)
    | exact superpose eq380006 eq369568
    | exact resolve eq369568 eq380006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369568
  have eq381662 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq381100
  have eq381701 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq380006
       have i₂ := eq381662
       grind)
    | exact superpose eq381662 eq380006
    | exact resolve eq380006 eq381662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380006 eq381662
  have eq382034 : x = (M.op x y) := by grind
  clear eq381701
  have eq382070 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq382034 eq20
    | exact resolve eq20 eq382034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq382075 : (σ (k y x)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq382034 eq79
    | exact resolve eq79 eq382034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq382117 : (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq382034 eq218
    | exact resolve eq218 eq382034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq382182 : (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq382117
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq382117
    | exact resolve eq382117 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382117
  have eq382223 : (k (σ y) (σ x)) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq382075
       have i₂ := eq77
       grind)
    | exact superpose eq77 eq382075
    | exact resolve eq382075 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq382075
  have eq382227 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq382070
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq382070
    | exact resolve eq382070 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382070
  have eq382241 : x = (M.op y x) := by
    first
    | exact superpose eq382034 eq382182
    | exact resolve eq382182 eq382034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382182
  have eq382272 : (M.op (σ y) (σ y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq340324 eq382223
    | exact resolve eq382223 eq340324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340324 eq382223
  have eq382289 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq382227 eq26
    | exact resolve eq26 eq382227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq385461 : x ≠ (M.op y x) ∨ y = (M.op y (M.op x y)) ∨ (M.op x y) = (k (M.op x y) y) := by
    first
    | exact superpose eq382034 eq226
    | exact resolve eq226 eq382034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq385462 : y = (M.op y (M.op x y)) ∨ (M.op x y) = (k (M.op x y) y) := by
    first
    | (have r₁ := eq385461
       have r₂ := eq382241
       grind)
    | exact resolve eq385461 eq382241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385461
  have eq385463 : y = (M.op y x) ∨ (M.op x y) = (k (M.op x y) y) := by
    first
    | exact superpose eq382034 eq385462
    | exact resolve eq385462 eq382034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385462
  have eq385464 : x = y ∨ (M.op x y) = (k (M.op x y) y) := by
    first
    | (have i₁ := eq385463
       have i₂ := eq382241
       grind)
    | exact superpose eq382241 eq385463
    | exact resolve eq385463 eq382241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385463
  have eq385465 : x = (k x y) ∨ x = y := by
    first
    | exact superpose eq382034 eq385464
    | exact resolve eq385464 eq382034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385464
  have eq385500 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq1626 x y
       have i₂ := eq385465
       grind)
    | exact superpose eq385465 eq1626
    | (have j0 := eq1626 x y
       grind)
    | exact resolve eq1626 eq385465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1626 eq385465
  have eq385503 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y := by grind
  clear eq385500
  have eq385509 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq385503
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq385503
    | exact resolve eq385503 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385503
  have eq385533 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq385509
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq385509
    | exact resolve eq385509 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385509
  have eq385554 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq26 eq385533
    | exact resolve eq385533 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385533
  have eq385575 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq382227 eq385554
    | exact resolve eq385554 eq382227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385554
  have eq385590 : (σ y) = (M.op (σ y) (σ x)) ∨ x = y := by
    first
    | (have r₁ := eq385575
       have r₂ := eq27
       grind)
    | exact resolve eq385575 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385575
  have eq385602 : (σ y) = (M.op (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq385590
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq385590
    | exact resolve eq385590 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385590
  have eq385614 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq382227 eq385602
    | exact resolve eq385602 eq382227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385602
  have eq385626 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq385614
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq385614
    | exact resolve eq385614 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385614
  have eq385780 : (σ y) ≠ (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq385626 eq12
    | (have j0 := eq12 (σ y) (σ (M.op x y))
       grind)
    | (have r₁ := eq12 (σ y) (σ (M.op x y))
       have r₂ := eq385626
       grind)
    | exact resolve eq12 eq385626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385626
  have eq386092 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = y := by grind
  clear eq385780
  have eq386282 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq382289 eq386092
    | exact resolve eq386092 eq382289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382289 eq386092
  have eq386326 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = y := by
    first
    | (have r₁ := eq386282
       have r₂ := eq27
       grind)
    | exact resolve eq386282 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386282
  have eq386338 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq382272 eq386326
    | exact resolve eq386326 eq382272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382272 eq386326
  have eq386388 : (τ (σ y)) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq386338 eq340482
    | exact resolve eq340482 eq386338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340482 eq386338
  have eq386849 : y = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq29 eq386388
    | exact resolve eq386388 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq386388
  have eq387890 : (M.op y y) = (M.op y (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq373 y
       have i₂ := eq386849
       grind)
    | exact superpose eq386849 eq373
    | exact resolve eq373 eq386849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373
  have eq388333 : (M.op y y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq382034 eq387890
    | exact resolve eq387890 eq382034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387890
  have eq388448 : x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq388333
       have i₂ := eq382241
       grind)
    | exact superpose eq382241 eq388333
    | exact resolve eq388333 eq382241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382241 eq388333
  have eq388770 : x = y ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq386849
       have i₂ := eq388448
       grind)
    | exact superpose eq388448 eq386849
    | exact resolve eq386849 eq388448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386849 eq388448
  have eq389098 : x = y := by grind
  clear eq388770
  have eq390486 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq389098
       grind)
    | exact superpose eq389098 eq18
    | exact resolve eq18 eq389098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq390487 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq389098
       grind)
    | exact superpose eq389098 eq24
    | exact resolve eq24 eq389098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq389098
  have eq390770 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq390487
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq390487
    | exact resolve eq390487 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390487
  have eq390771 : x = (M.op x x) := by
    first
    | exact superpose eq382034 eq390486
    | exact resolve eq390486 eq382034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382034 eq390486
  have eq390846 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq382227 eq390770
    | exact resolve eq390770 eq382227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390770
  have eq392081 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq390846 eq26
    | exact resolve eq26 eq390846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq390846
  have eq392416 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq382227 eq392081
    | exact resolve eq392081 eq382227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392081
  have eq392573 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq11467
       have i₂ := eq390771
       grind)
    | exact superpose eq390771 eq11467
    | exact resolve eq11467 eq390771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11467 eq390771
  have eq393047 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq32011 eq392573
    | exact resolve eq392573 eq32011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32011 eq392573
  have eq393145 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq382227 eq393047
    | exact resolve eq393047 eq382227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393047
  have eq393232 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq393145
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq393145
    | exact resolve eq393145 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq393145
  have eq393252 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq382227 eq393232
    | exact resolve eq393232 eq382227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382227 eq393232
  have eq393615 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq392416 eq393252
    | exact resolve eq393252 eq392416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392416 eq393252
  have eq393616 : False := by grind
  exact eq393616

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,Y) else if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pxx_y_pxy_pxx_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (M.op X1 X0) := by
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
  have eq63 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op X0 X0) X0 x
       have i₂ := eq9 X0 x (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (M.op X0 X0)
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq63 X0
       grind)
    | exact resolve eq12 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq66 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq71 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq67 (σ X0)
       grind)
    | exact superpose eq67 eq15
    | exact resolve eq15 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq67 (τ X0)
       grind)
    | exact superpose eq67 eq32
    | exact resolve eq32 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq80 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq73 X0
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq73
    | exact resolve eq73 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq82 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq71 X0
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq71
    | exact resolve eq71 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq71
  have eq96 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq82 X0
       grind)
    | exact superpose eq82 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 : G, (k (σ X0) (σ (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq68 (σ X0)
       have i₂ := eq82 X0
       grind)
    | exact superpose eq82 eq68
    | exact resolve eq68 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq113 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq113
    | exact resolve eq113 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq124 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq120 X0
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq120
    | exact resolve eq120 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq120
  have eq1280 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
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
  have eq1303 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1280 X0 X1
       have i₂ := eq82 X0
       grind)
    | exact superpose eq82 eq1280
    | (have j0 := eq1280 X0 X1
       grind)
    | exact resolve eq1280 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1280
  have eq1317 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1303 X0 X1
       have i₂ := eq82 X0
       grind)
    | exact superpose eq82 eq1303
    | (have j0 := eq1303 X0 X1
       grind)
    | exact resolve eq1303 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq1303
  have eq1730 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = X0 ∨ (σ (M.op X1 X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1317 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1317
    | exact resolve eq1317 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1317
  have eq1820 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = X0 ∨ (σ (M.op X1 X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1730 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq1730
    | (have j0 := eq1730 X0 X1
       grind)
    | exact resolve eq1730 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1730
  have eq1833 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1820 X0 X1
       have j1 := eq96 X1 X0
       grind)
    | (have r₁ := eq1820 (M.op X1 (σ X0)) X0
       have r₂ := eq96 X0 X1
       grind)
    | (have r₁ := eq1820 X1 X0
       have r₂ := eq96 X0 X1
       grind)
    | exact resolve eq1820 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq1820
  have eq1858 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1833 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1833
    | (have j0 := eq1833 X1 (τ X0)
       grind)
    | exact resolve eq1833 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1869 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq1833 (σ X1) X0
       grind)
    | exact superpose eq1833 eq15
    | (have j1 := eq1833 (σ X1) X0
       grind)
    | exact resolve eq15 eq1833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1833
  have eq1901 : ∀ X0 X1 : G, (σ (τ (M.op X0 X0))) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1858 X0 X1
       have i₂ := eq80 X0
       grind)
    | exact superpose eq80 eq1858
    | (have j0 := eq1858 X0 X1
       grind)
    | exact resolve eq1858 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq1858
  have eq1902 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1901 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq1901
    | (have j0 := eq1901 X0 X1
       grind)
    | exact resolve eq1901 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1901
  have eq1916 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq1902 X0 (τ X1)
       grind)
    | exact superpose eq1902 eq19
    | (have j1 := eq1902 X0 (τ X1)
       grind)
    | exact resolve eq19 eq1902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq1902
  have eq2295 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1916 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1916
    | exact resolve eq1916 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1916
  have eq2393 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2295 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2295
    | (have j0 := eq2295 X0 X1
       grind)
    | exact resolve eq2295 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2295
  have eq2745 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1869 x y
       grind)
    | exact superpose eq1869 eq16
    | (have j1 := eq1869 x y
       grind)
    | exact resolve eq16 eq1869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1869
  have eq2944 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2745
       have i₂ := eq2393 y x
       grind)
    | exact superpose eq2393 eq2745
    | (have j1 := eq2393 y x
       grind)
    | (have r₁ := eq2745
       have r₂ := eq2393 y x
       grind)
    | exact resolve eq2745 eq2393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2393 eq2745
  have eq2945 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq2944
  have eq2961 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq124 x
       have i₂ := eq2945
       grind)
    | exact superpose eq2945 eq124
    | exact resolve eq124 eq2945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2945
  have eq2994 : (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq2961
       have r₂ := eq16
       grind)
    | exact resolve eq2961 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2961
  have eq3006 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq2994
       grind)
    | exact superpose eq2994 eq10
    | exact resolve eq10 eq2994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2994
  have eq3064 : y = (M.op x x) := by
    first
    | (have i₁ := eq3006
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq3006
    | exact resolve eq3006 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3006
  have eq3078 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq124 x
       have i₂ := eq3064
       grind)
    | exact superpose eq3064 eq124
    | exact resolve eq124 eq3064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq3064
  have eq3111 : False := by grind
  exact eq3111

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pxy_x_pxy_x_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (M.op X1 X0) := by
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
  have eq19 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 (M.op X0 X0)) X2 X0
       have i₂ := eq9 X0 (M.op X1 (M.op X0 X0)) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  clear eq17
  have eq28 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq28 (σ X0)
       grind)
    | exact superpose eq28 eq15
    | exact resolve eq15 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq31
    | exact resolve eq31 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq31
  have eq48 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 ∨ (M.op X0 X0) = (M.op (M.op X1 (M.op X2 (M.op X0 X0))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op X1 (M.op X2 (M.op X0 X0)))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 X0 (M.op X1 (M.op X2 (M.op X0 X0)))
       grind)
    | (have r₁ := eq13 X0 (M.op X1 (M.op X2 (M.op X0 X0)))
       have r₂ := eq9 X0 X1 X2
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 (M.op X0 X0))) X0) ∨ (k X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq48 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq67 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
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
  have eq78 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq74 X0 X1
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq74
    | (have j0 := eq74 X0 X1
       grind)
    | exact resolve eq74 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq74
  have eq118 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) = (M.op (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 (M.op X3 X1) X2 (M.op X0 (M.op X1 X1))
       have i₂ := eq19 X1 X0 X3
       grind)
    | exact superpose eq19 eq19
    | exact resolve eq19 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq171 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = (k X0 (M.op X1 (M.op X2 (M.op X0 X0)))) ∨ (k X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 (M.op X1 (M.op X2 (M.op X0 X0)))
       have i₂ := eq51 X0 X1 X2
       grind)
    | exact superpose eq51 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq51 X0 X1 X2
       grind)
    | (have r₁ := eq12 X0 (M.op X1 (M.op X2 (M.op X0 X0)))
       have r₂ := eq51 X0 X1 X2
       grind)
    | exact resolve eq12 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq172 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = (k X0 (M.op X1 (M.op X2 (M.op X0 X0)))) ∨ (k X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq171 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171
  have eq173 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 ∨ (k X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq172 X0 X1 X2
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq172
    | (have j0 := eq172 X0 X1 X2
       grind)
    | exact resolve eq172 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172
  have eq174 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq173 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173
  have eq216 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq78 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq78
    | exact resolve eq78 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq238 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq216 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq216
    | (have j0 := eq216 X0 X1
       grind)
    | exact resolve eq216 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq246 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq238 X0 X1
       have j1 := eq67 X1 X0
       grind)
    | (have r₁ := eq238 X1 X0
       have r₂ := eq67 X0 X1
       grind)
    | (have r₁ := eq238 (σ X0) (M.op X0 X0)
       have r₂ := eq67 X0 (σ (M.op X0 X0))
       grind)
    | exact resolve eq238 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq238
  have eq747 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq246 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq246
    | exact resolve eq246 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq763 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq246 (σ X1) X0
       grind)
    | exact superpose eq246 eq15
    | (have j1 := eq246 (σ X1) X0
       grind)
    | exact resolve eq15 eq246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246
  have eq814 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq747 X0 (τ X1)
       grind)
    | exact superpose eq747 eq18
    | (have j1 := eq747 X0 (τ X1)
       grind)
    | exact resolve eq18 eq747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1085 : ∀ X0 X1 X2 : G, (k X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq174 X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2))) x
       have i₂ := eq118 x X2 X0 X1
       grind)
    | exact superpose eq118 eq174
    | exact resolve eq174 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq1087 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2))) x
       have i₂ := eq118 x X2 X0 X1
       grind)
    | exact superpose eq118 eq9
    | exact resolve eq9 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq1203 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1085 X0 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq1087 (M.op (M.op X1 X0) (M.op X1 X0)) X1 X0
       grind)
    | exact superpose eq1087 eq1085
    | exact resolve eq1085 eq1087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1085 eq1087
  have eq1348 : ∀ X0 X1 : G, (τ (M.op X0 (σ X1))) = (k (τ (M.op X0 (σ X1))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq26 (M.op X0 (σ X1)) X1
       have i₂ := eq1203 (σ X1) X0
       grind)
    | exact superpose eq1203 eq26
    | exact resolve eq26 eq1203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1349 : ∀ X0 X1 : G, (σ (M.op X0 (τ X1))) = (k (σ (M.op X0 (τ X1))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (M.op X0 (τ X1))
       have i₂ := eq1203 (τ X1) X0
       grind)
    | exact superpose eq1203 eq18
    | exact resolve eq18 eq1203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1203
  have eq1537 : ∀ X0 X1 : G, (τ (M.op X0 (σ X1))) = (M.op (τ (M.op X0 (σ X1))) X1) ∨ (τ (M.op X0 (σ X1))) = (M.op (τ (M.op X0 (σ X1))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq747 (τ (M.op X0 (σ X1))) X1
       have i₂ := eq1348 X0 X1
       grind)
    | exact superpose eq1348 eq747
    | (have j0 := eq747 (τ (M.op X0 (σ X1))) X1
       grind)
    | exact resolve eq747 eq1348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1348
  have eq1544 : ∀ X0 X1 : G, (τ (M.op X0 (σ X1))) = (M.op (τ (M.op X0 (σ X1))) X1) := by
    intro X0 X1
    first
    | (have j0 := eq1537 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1537
  have eq1599 : ∀ X0 X1 : G, (σ (M.op X0 (τ X1))) = (M.op (σ (M.op X0 (τ X1))) X1) ∨ (σ (M.op X0 (τ X1))) = (M.op (σ (M.op X0 (τ X1))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq747 (σ (M.op X0 (τ X1))) X1
       have i₂ := eq1349 X0 X1
       grind)
    | exact superpose eq1349 eq747
    | (have j0 := eq747 (σ (M.op X0 (τ X1))) X1
       grind)
    | exact resolve eq747 eq1349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747 eq1349
  have eq1606 : ∀ X0 X1 : G, (σ (M.op X0 (τ X1))) = (M.op (σ (M.op X0 (τ X1))) X1) := by
    intro X0 X1
    first
    | (have j0 := eq1599 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1599
  have eq1848 : ∀ X0 X1 : G, (σ (M.op X1 X0)) = (M.op (σ (M.op X1 X0)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1606 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1606
    | exact resolve eq1606 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1606
  have eq6374 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq763 x y
       grind)
    | exact superpose eq763 eq16
    | (have j1 := eq763 x y
       grind)
    | exact resolve eq16 eq763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763
  have eq18070 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq814 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq814
    | exact resolve eq814 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814
  have eq18247 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18070 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq18070
    | (have j0 := eq18070 X0 X1
       grind)
    | exact resolve eq18070 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18070
  have eq35564 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6374
       have i₂ := eq18247 y x
       grind)
    | exact superpose eq18247 eq6374
    | (have j1 := eq18247 (σ y) (σ x)
       grind)
    | (have r₁ := eq6374
       have r₂ := eq18247 y x
       grind)
    | exact resolve eq6374 eq18247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6374 eq18247
  have eq35567 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq35564
  have eq35751 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1848 y x
       have i₂ := eq35567
       grind)
    | exact superpose eq35567 eq1848
    | exact resolve eq1848 eq35567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1848 eq35567
  have eq35758 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq35751
  have eq35762 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq35758
       grind)
    | exact superpose eq35758 eq16
    | exact resolve eq16 eq35758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35768 : (τ (σ x)) = (M.op (τ (σ x)) y) := by
    first
    | (have i₁ := eq1544 (σ x) y
       have i₂ := eq35758
       grind)
    | exact superpose eq35758 eq1544
    | exact resolve eq1544 eq35758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1544 eq35758
  have eq35827 : x = (M.op x y) := by
    first
    | (have i₁ := eq35768
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq35768
    | exact resolve eq35768 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35768
  have eq36389 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq35762
       have i₂ := eq35827
       grind)
    | exact superpose eq35827 eq35762
    | exact resolve eq35762 eq35827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35762 eq35827
  have eq36394 : False := by grind
  exact eq36394

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,Y) else if m(Y,X) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pyx_x_pxy_y_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X0) = (M.op X1 X0) := by
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
  have eq19 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 (M.op X0 X0)) X2 X0
       have i₂ := eq9 X0 (M.op X1 (M.op X0 X0)) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op X0 X0) X0 x
       have i₂ := eq9 X0 x (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq28 (σ X0)
       grind)
    | exact superpose eq28 eq15
    | exact resolve eq15 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq31
    | exact resolve eq31 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq31
  have eq64 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq20 (σ X0)
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq20
    | exact resolve eq20 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq71 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
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
  have eq75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq71 X0 X1
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq71
    | (have j0 := eq71 X0 X1
       grind)
    | exact resolve eq71 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq115 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) = (M.op (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 (M.op X3 X1) X2 (M.op X0 (M.op X1 X1))
       have i₂ := eq19 X1 X0 X3
       grind)
    | exact superpose eq19 eq19
    | exact resolve eq19 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq156 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq75 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq75
    | exact resolve eq75 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq175 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq156 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq156
    | (have j0 := eq156 X0 X1
       grind)
    | exact resolve eq156 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156
  have eq183 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq175 X0 X1
       have j1 := eq64 X1 X0
       grind)
    | (have r₁ := eq175 X1 X0
       have r₂ := eq64 X0 X1
       grind)
    | exact resolve eq175 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq560 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq183 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq183
    | exact resolve eq183 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq567 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq183 (σ X1) X0
       grind)
    | exact superpose eq183 eq15
    | (have j1 := eq183 (σ X1) X0
       grind)
    | exact resolve eq15 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq589 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq560 X0 (τ X1)
       grind)
    | exact superpose eq560 eq18
    | (have j1 := eq560 X0 (τ X1)
       grind)
    | exact resolve eq18 eq560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq857 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2))) x
       have i₂ := eq115 x X2 X0 X1
       grind)
    | exact superpose eq115 eq9
    | exact resolve eq9 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq900 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X0 x
       have i₂ := eq857 x X1 X0
       grind)
    | exact superpose eq857 eq9
    | exact resolve eq9 eq857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857
  have eq1495 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq589 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq589
    | exact resolve eq589 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589
  have eq1569 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1495 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1495
    | (have j0 := eq1495 X0 X1
       grind)
    | exact resolve eq1495 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1495
  have eq3058 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq567 x y
       grind)
    | exact superpose eq567 eq16
    | (have j1 := eq567 x y
       grind)
    | exact resolve eq16 eq567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567
  have eq3220 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq3058
       have i₂ := eq1569 y x
       grind)
    | exact superpose eq1569 eq3058
    | (have j1 := eq1569 (σ y) (σ x)
       grind)
    | (have r₁ := eq3058
       have r₂ := eq1569 y x
       grind)
    | exact resolve eq3058 eq1569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1569 eq3058
  have eq3221 : x = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq3220
  have eq3298 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq900 x y
       have i₂ := eq3221
       grind)
    | exact superpose eq3221 eq900
    | exact resolve eq900 eq3221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3221
  have eq3315 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq900 (σ x) (σ y)
       have i₂ := eq3298
       grind)
    | exact superpose eq3298 eq900
    | exact resolve eq900 eq3298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900 eq3298
  have eq3317 : x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq3315
       have i₂ := eq34 x
       grind)
    | exact superpose eq34 eq3315
    | exact resolve eq3315 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3315
  have eq3436 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq65 x
       have i₂ := eq3317
       grind)
    | exact superpose eq3317 eq65
    | exact resolve eq65 eq3317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq3317
  have eq3475 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq3436
       have i₂ := eq34 x
       grind)
    | exact superpose eq34 eq3436
    | exact resolve eq3436 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq3436
  have eq3476 : (σ x) = (σ (M.op x x)) := by grind
  clear eq3475
  have eq3481 : ∀ X0 : G, (σ x) ≠ (M.op X0 (σ x)) ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq64 x X0
       have i₂ := eq3476
       grind)
    | exact superpose eq3476 eq64
    | (have j0 := eq64 x X0
       grind)
    | exact resolve eq64 eq3476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq3491 : (M.op x x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq3476
       grind)
    | exact superpose eq3476 eq10
    | exact resolve eq10 eq3476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3476
  have eq3552 : x = (M.op x x) := by
    first
    | (have i₁ := eq3491
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3491
    | exact resolve eq3491 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3491
  have eq3557 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq3481 X0
       have j1 := eq560 (σ x) X0
       grind)
    | (have r₁ := eq3481 x
       have r₂ := eq560 (σ x) x
       grind)
    | exact resolve eq3481 eq560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3481
  have eq3693 : ∀ X0 : G, x ≠ (M.op X0 x) ∨ (k x X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq12 x X0
       have i₂ := eq3552
       grind)
    | exact superpose eq3552 eq12
    | (have j0 := eq12 x X0
       grind)
    | exact resolve eq12 eq3552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3552
  have eq3749 : ∀ X0 : G, (k x X0) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq3693 X0
       have j1 := eq560 x X0
       grind)
    | (have r₁ := eq3693 x
       have r₂ := eq560 x x
       grind)
    | exact resolve eq3693 eq560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560 eq3693
  have eq4049 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (k x X0)) := by
    intro X0
    first
    | (have i₁ := eq15 x X0
       have i₂ := eq3557 (σ X0)
       grind)
    | exact superpose eq3557 eq15
    | exact resolve eq15 eq3557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3557
  have eq4094 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq4049 X0
       have i₂ := eq3749 X0
       grind)
    | exact superpose eq3749 eq4049
    | exact resolve eq4049 eq3749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3749 eq4049
  have eq4922 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4094 y
       grind)
    | exact superpose eq4094 eq16
    | (have r₁ := eq16
       have r₂ := eq4094 y
       grind)
    | exact resolve eq16 eq4094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4094
  have eq4983 : False := by grind
  exact eq4983

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pxy_pyy_pxy_pyy_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq58 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq57 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq59 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq56 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq56 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq56 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq56 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq60 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq58 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq58 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq58 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq58 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq117 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq59 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq59 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq59
    | (have j0 := eq59 X1 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq59 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq59 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq59 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq124 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq117 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq127 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq124 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq124 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq124 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq124 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq129 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq127 X0 X1
       have i₂ := eq21 X1
       grind)
    | exact superpose eq21 eq127
    | (have j0 := eq127 X0 X1
       grind)
    | exact resolve eq127 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq127
  have eq155 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq60 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq159 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq155 X0 X1
       have j1 := eq129 X0 X1
       grind)
    | (have r₁ := eq155 X0 X1
       have r₂ := eq129 X0 X1
       grind)
    | (have r₁ := eq155 X1 X1
       have r₂ := eq129 X1 X1
       grind)
    | exact resolve eq155 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq155
  have eq444 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq159 (σ X0) (σ X1)
       grind)
    | exact superpose eq159 eq15
    | exact resolve eq15 eq159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq451 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq444 X0 X1
       have i₂ := eq159 X0 X1
       grind)
    | exact superpose eq159 eq444
    | exact resolve eq444 eq159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159 eq444
  have eq454 : False := by grind
  exact eq454

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pxy_x_pxy_x_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
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
  have eq50 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X1 (M.op X0 X0)) X2 X0
       have i₂ := eq14 X0 (M.op X1 (M.op X0 X0)) X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq61 x
       grind)
    | exact superpose eq61 eq43
    | exact resolve eq43 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq67 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq64
       have i₂ := eq61 sF2
       grind)
    | exact superpose eq61 eq64
    | exact resolve eq64 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq72 : x ≠ (M.op x y) ∨ (M.op x x) = (M.op y y) ∨ x = (k x y) := by
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
  have eq73 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
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
    | (have r₁ := eq11 (M.op X1 X1) (M.op X1 X1)
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq81 x y
       grind)
    | exact superpose eq81 eq44
    | (have j1 := eq81 x y
       grind)
    | exact resolve eq44 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq55
       have i₂ := eq81 sF2 sF3
       grind)
    | exact superpose eq81 eq55
    | (have j1 := eq81 (σ x) (σ y)
       grind)
    | exact resolve eq55 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq118 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq117
    | exact resolve eq117 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq120 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq112
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq112
    | exact resolve eq112 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq122 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq118
    | exact resolve eq118 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq123 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq120
    | exact resolve eq120 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq124 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq123
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq123
    | exact resolve eq123 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq142 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq143 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq164 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq143 eq16
    | exact resolve eq16 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq124 eq81
    | (have j0 := eq81 (σ x) (σ y)
       grind)
    | exact resolve eq81 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq192 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq191
    | exact resolve eq191 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq195 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq192
       have r₂ := eq27
       grind)
    | exact resolve eq192 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq197 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq195
    | exact resolve eq195 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq199 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq197 eq27
    | exact resolve eq27 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq483 : ∀ X0 : G, (M.op X0 (M.op y y)) = (M.op (M.op X0 (M.op y y)) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq50 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq50
    | (have j0 := eq50 y X0 x
       grind)
    | exact resolve eq50 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq492 : (k (σ x) (σ y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq122
       grind)
    | exact superpose eq122 eq44
    | exact resolve eq44 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq122
  have eq495 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq492
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq492
    | exact resolve eq492 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492
  have eq602 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq197 eq73
    | (have r₁ := eq73
       have r₂ := eq197
       grind)
    | exact resolve eq73 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq197
  have eq603 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq602
  have eq607 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ x) (σ x)) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq603 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq603
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq603
       grind)
    | exact resolve eq13 eq603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603
  have eq732 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j0 := eq607 (σ x)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607
  have eq735 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq732
    | exact resolve eq732 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq732
  have eq741 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq124 eq735
    | exact resolve eq735 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq735
  have eq749 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq741
  have eq752 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq749
       have r₂ := eq199
       grind)
    | exact resolve eq749 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199 eq749
  have eq753 : x = (M.op x y) := by
    first
    | (have r₁ := eq752
       have r₂ := eq27
       grind)
    | exact resolve eq752 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq752
  have eq754 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq753 eq20
    | exact resolve eq20 eq753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq756 : x ≠ x ∨ (M.op x x) = (M.op y y) ∨ x = (k x y) := by
    first
    | exact superpose eq753 eq72
    | (have r₁ := eq72
       have r₂ := eq753
       grind)
    | exact resolve eq72 eq753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq763 : (M.op x x) = (M.op y y) ∨ x = (k x y) := by grind
  clear eq756
  have eq771 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq754
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq754
    | exact resolve eq754 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq754
  have eq815 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq771 eq495
    | exact resolve eq495 eq771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq495
  have eq821 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have r₁ := eq815
       have r₂ := eq27
       grind)
    | exact resolve eq815 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq815
  have eq840 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) y) := by
    first
    | exact superpose eq821 eq164
    | exact resolve eq164 eq821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164
  have eq842 : (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq753 eq840
    | exact resolve eq840 eq753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq840
  have eq990 : ∀ X0 : G, (M.op X0 (M.op y y)) = (M.op (M.op X0 (M.op y y)) x) := by
    intro X0
    first
    | exact superpose eq753 eq483
    | exact resolve eq483 eq753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483 eq753
  have eq1053 : ∀ X0 X1 : G, (M.op X1 (M.op x x)) = (M.op (M.op X1 (M.op x x)) (M.op X0 (M.op y y))) := by
    intro X0 X1
    first
    | (have i₁ := eq50 x X1 (M.op X0 (M.op y y))
       have i₂ := eq990 X0
       grind)
    | exact superpose eq990 eq50
    | exact resolve eq50 eq990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq1082 : (M.op x x) = (M.op y y) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq763
       have i₂ := eq842
       grind)
    | exact superpose eq842 eq763
    | exact resolve eq763 eq842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763 eq842
  have eq1087 : ∀ X0 X1 : G, y = (M.op y (M.op X0 (M.op X1 (M.op x x)))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 y X0 X1
       have i₂ := eq1082
       grind)
    | exact superpose eq1082 eq14
    | exact resolve eq14 eq1082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13240 : ∀ X0 : G, y = (M.op y (M.op X0 (M.op x x))) := by
    intro X0
    first
    | (have i₁ := eq14 y (M.op X0 (M.op x x)) x
       have i₂ := eq1053 x X0
       grind)
    | exact superpose eq1053 eq14
    | exact resolve eq14 eq1053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1053
  have eq13278 : y = (M.op y y) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1087 y x
       have i₂ := eq13240 x
       grind)
    | exact superpose eq13240 eq1087
    | exact resolve eq1087 eq13240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1087
  have eq13327 : y = (M.op x x) ∨ x = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1082
       have i₂ := eq13278
       grind)
    | exact superpose eq13278 eq1082
    | exact resolve eq1082 eq13278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13278
  have eq13366 : y = (M.op x x) ∨ x = (τ (M.op (σ x) (σ y))) := by grind
  clear eq13327
  have eq13391 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq67
       have i₂ := eq13366
       grind)
    | exact superpose eq13366 eq67
    | exact resolve eq67 eq13366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq13411 : ∀ X0 : G, y = (M.op y (M.op X0 y)) ∨ x = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq13240 X0
       have i₂ := eq13366
       grind)
    | exact superpose eq13366 eq13240
    | exact resolve eq13240 eq13366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13240
  have eq13465 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq771 eq13391
    | exact resolve eq13391 eq771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13391
  have eq13481 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq13465
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq13465
    | exact resolve eq13465 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13465
  have eq14012 : y = (M.op y (M.op x x)) ∨ x = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq13411 y
       have i₂ := eq1082
       grind)
    | exact superpose eq1082 eq13411
    | exact resolve eq13411 eq1082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1082 eq13411
  have eq14038 : y = (M.op y (M.op x x)) ∨ x = (τ (M.op (σ x) (σ y))) := by grind
  clear eq14012
  have eq14273 : ∀ X0 : G, x = (M.op x (M.op X0 y)) ∨ x = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq14038
       grind)
    | exact superpose eq14038 eq14
    | exact resolve eq14 eq14038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14038
  have eq14552 : x = (M.op x x) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq990 x
       have i₂ := eq14273 y
       grind)
    | exact superpose eq14273 eq990
    | exact resolve eq990 eq14273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq990 eq14273
  have eq14585 : x = y ∨ x = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq13366
       have i₂ := eq14552
       grind)
    | exact superpose eq14552 eq13366
    | exact resolve eq13366 eq14552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13366 eq14552
  have eq14614 : x = (τ (M.op (σ x) (σ y))) ∨ x = y := by grind
  clear eq14585
  have eq14675 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq14614 eq15
    | exact resolve eq15 eq14614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14614
  have eq14746 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq14675
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq14675
    | exact resolve eq14675 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14675
  have eq14776 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq771 eq14746
    | exact resolve eq14746 eq771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14746
  have eq14791 : x = y := by
    first
    | (have r₁ := eq14776
       have r₂ := eq27
       grind)
    | exact resolve eq14776 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14776
  have eq14797 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq14791
       grind)
    | exact superpose eq14791 eq24
    | exact resolve eq24 eq14791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq14804 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq143
       have i₂ := eq14791
       grind)
    | exact superpose eq14791 eq143
    | exact resolve eq143 eq14791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143 eq14791
  have eq14895 : (M.op (σ x) (σ y)) = (σ (k (M.op x y) x)) := by
    first
    | exact superpose eq821 eq14804
    | exact resolve eq14804 eq821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821 eq14804
  have eq14902 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq14797
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq14797
    | exact resolve eq14797 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14797
  have eq14919 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq142 eq14895
    | exact resolve eq14895 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq14895
  have eq14926 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq771 eq14902
    | exact resolve eq14902 eq771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14902
  have eq14929 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq771 eq14919
    | exact resolve eq14919 eq771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14919
  have eq14934 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq14929
       have i₂ := eq61 sF1
       grind)
    | exact superpose eq61 eq14929
    | exact resolve eq14929 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq14929
  have eq15657 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq14934 eq13481
    | exact resolve eq13481 eq14934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13481 eq14934
  have eq15691 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq14926 eq15657
    | exact resolve eq15657 eq14926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14926 eq15657
  have eq15709 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq15691
       have r₂ := eq27
       grind)
    | exact resolve eq15691 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15691
  have eq15793 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15709 eq15
    | exact resolve eq15 eq15709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15709
  have eq15875 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15793
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15793
    | exact resolve eq15793 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq15793
  have eq15921 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq771 eq15875
    | exact resolve eq15875 eq771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771 eq15875
  have eq15956 : False := by grind
  exact eq15956
