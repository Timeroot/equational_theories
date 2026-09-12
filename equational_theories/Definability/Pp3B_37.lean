import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2739`: `x = ((y ◇ y) ◇ (x ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_y_pyx_x_pxy_Equation2739 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2739 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2739.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ b ∨ k a b = a :=
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
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op X0 X2)) X0) = X0 := by
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
  clear eq35
  have eq53 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (M.op (M.op X0 X1) (M.op X0 X1)) X1
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq53 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq53
    | (have j0 := eq53 x y
       grind)
    | exact resolve eq53 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq26 eq53
    | (have j0 := eq53 (σ x) (σ y)
       grind)
    | exact resolve eq53 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq55 eq53
    | exact resolve eq53 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (M.op X0 X1)
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq13
    | (have r₁ := eq13 X0 (M.op X0 X1)
       have r₂ := eq53 X0 X1
       grind)
    | exact resolve eq13 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : x ≠ x ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq54 eq13
    | (have r₁ := eq13 x (M.op x y)
       have r₂ := eq54
       grind)
    | exact resolve eq13 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq55 eq13
    | (have r₁ := eq13 (σ x) (M.op (σ x) (σ y))
       have r₂ := eq55
       grind)
    | exact resolve eq13 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by grind
  clear eq69
  have eq71 : x = (k x (M.op x y)) := by grind
  clear eq67
  have eq72 : ∀ X0 X1 : G, (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq65 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq74 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq60 eq13
    | (have r₁ := eq13 (M.op x y) x
       have r₂ := eq60
       grind)
    | exact resolve eq13 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq77 : (M.op x y) = (k (M.op x y) x) := by grind
  clear eq74
  have eq78 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq62 eq13
    | (have r₁ := eq13 (M.op (σ x) (σ y)) (σ x)
       have r₂ := eq62
       grind)
    | exact resolve eq13 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq81 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) := by grind
  clear eq78
  have eq96 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq120 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ y) X0) := by
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
  have eq122 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq123 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq124 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq11 sF3 (σ X0)
       grind)
    | exact superpose eq11 eq36
    | (have j1 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq36 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
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
  have eq133 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq127
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq127
    | exact resolve eq127 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq134 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq133
    | exact resolve eq133 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq135 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq134
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq134
    | exact resolve eq134 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq136 : (σ x) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq71 eq45
    | exact resolve eq45 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq71
  have eq137 : (σ x) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq136
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq136
    | exact resolve eq136 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq138 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq137
       have i₂ := eq11 sF2 sF1
       grind)
    | exact superpose eq11 eq137
    | (have j1 := eq11 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq137 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq140 : ∀ X0 : G, (σ (k (M.op x y) (τ X0))) = (k (σ (M.op x y)) X0) := by
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
  have eq143 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  have eq145 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq146 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ X0) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq11 sF1 (σ X0)
       grind)
    | exact superpose eq11 eq37
    | (have j1 := eq11 (σ (M.op x y)) (σ X0)
       grind)
    | exact resolve eq37 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq77 eq143
    | exact resolve eq143 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq143
  have eq149 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq20 eq148
    | exact resolve eq148 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq150 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq149
       have i₂ := eq11 sF1 sF2
       grind)
    | exact superpose eq11 eq149
    | (have j1 := eq11 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq149 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq158 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq122
       grind)
    | exact superpose eq122 eq16
    | exact resolve eq16 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq162 : (σ (k y (k y y))) = (k (σ y) (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq36 (k y y)
       have i₂ := eq123
       grind)
    | exact superpose eq123 eq36
    | exact resolve eq36 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq186 : (σ (k (M.op x y) (k y (M.op x y)))) = (k (σ (M.op x y)) (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq124 eq37
    | exact resolve eq37 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq124
  have eq309 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq350 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (k y (τ X0))
       have i₂ := eq120 X0
       grind)
    | exact superpose eq120 eq16
    | exact resolve eq16 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq402 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq658 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (k X0 X1)) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (σ X0) (σ X1)
       have i₂ := eq96 X0 X1
       grind)
    | exact superpose eq96 eq53
    | (have j1 := eq96 X0 X1
       grind)
    | exact resolve eq53 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq847 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq402 X0 (M.op (σ X0) X1)
       have i₂ := eq72 (σ X0) X1
       grind)
    | exact superpose eq72 eq402
    | exact resolve eq402 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402
  have eq877 : ∀ X0 X1 : G, (k X0 (τ (M.op (σ X0) X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq847 X0 X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq847
    | exact resolve eq847 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq847
  have eq5735 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq125 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq125
    | (have j0 := eq125 y
       grind)
    | exact resolve eq125 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq5756 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq5735
  have eq5762 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq5756
       have i₂ := eq123
       grind)
    | exact superpose eq123 eq5756
    | exact resolve eq5756 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5756
  have eq5784 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq5762
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq5762 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5762
  have eq5957 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq146
    | (have j0 := eq146 (M.op x y)
       grind)
    | exact resolve eq146 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq5977 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq5957
  have eq5982 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq145 eq5977
    | exact resolve eq5977 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5977
  have eq6011 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq5982
       have r₂ := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq5982 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5982
  have eq8993 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq135 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8994 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq8993
    | exact resolve eq8993 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8993
  have eq9005 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq8994
       have r₂ := eq27
       grind)
    | exact resolve eq8994 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8994
  have eq9009 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq9005
    | exact resolve eq9005 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9005
  have eq9015 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq9009 eq53
    | exact resolve eq53 eq9009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9009
  have eq9032 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq9015
    | exact resolve eq9015 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9015
  have eq9033 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq9032
  have eq9040 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq53 y x
       have i₂ := eq9033
       grind)
    | exact superpose eq9033 eq53
    | exact resolve eq53 eq9033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9033
  have eq9057 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9040
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9040
    | exact resolve eq9040 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9040
  have eq9058 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq9057
  have eq9067 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9058 eq70
    | exact resolve eq70 eq9058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq9068 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9058 eq81
    | exact resolve eq81 eq9058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq9058
  have eq9189 : (σ y) = (M.op (k (σ y) (σ x)) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq658 y x
       have i₂ := eq122
       grind)
    | exact superpose eq122 eq658
    | (have j0 := eq658 y x
       grind)
    | exact resolve eq658 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq658
  have eq9349 : (σ y) = (M.op (k (σ y) (σ x)) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9189
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq9189
    | exact resolve eq9189 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9189
  have eq9460 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (k (σ y) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9349
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq9349
    | exact resolve eq9349 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9349
  have eq9565 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (k (σ y) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9460
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq9460
    | exact resolve eq9460 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9460
  have eq9650 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (k (σ y) (σ x)) (σ y)) := by
    first
    | (have i₁ := eq9565
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq9565
    | exact resolve eq9565 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9565
  have eq9732 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (k (σ y) (σ x)) (σ y)) := by
    first
    | (have i₁ := eq9650
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq9650
    | exact resolve eq9650 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9650
  have eq9802 : (σ y) = (M.op (k (σ y) (σ x)) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq9732
    | exact resolve eq9732 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9732
  have eq9884 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9067 eq135
    | exact resolve eq135 eq9067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135 eq9067
  have eq9894 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq9884
  have eq9908 : (τ (σ y)) = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9068 eq158
    | exact resolve eq158 eq9068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158 eq9068
  have eq9924 : y = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq9908
    | exact resolve eq9908 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9908
  have eq9972 : y = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq9924
       grind)
    | exact superpose eq9924 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq9924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9924
  have eq9973 : y = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq9972
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9972
    | exact resolve eq9972 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9972
  have eq9974 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq9973
  have eq11797 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq53 y x
       have i₂ := eq9894
       grind)
    | exact superpose eq9894 eq53
    | exact resolve eq53 eq9894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9894
  have eq11815 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq11797
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11797
    | exact resolve eq11797 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11797
  have eq11816 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq11815
  have eq11889 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11816 eq28
    | exact resolve eq28 eq11816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq11816
  have eq12009 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq11889
    | exact resolve eq11889 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11889
  have eq12022 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12009 eq20
    | exact resolve eq20 eq12009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12032 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ (M.op x y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq12009 eq140
    | exact resolve eq140 eq12009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq12036 : (σ (k y y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12009 eq145
    | exact resolve eq145 eq12009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq12041 : (σ (k y (k y y))) = (k (σ (M.op x y)) (k (σ y) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12009 eq186
    | exact resolve eq186 eq12009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186 eq12009
  have eq12104 : (k (σ y) (k (σ y) (σ y))) = (k (σ (M.op x y)) (k (σ y) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12041
       have i₂ := eq162
       grind)
    | exact superpose eq162 eq12041
    | exact resolve eq12041 eq162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162 eq12041
  have eq12109 : (σ (k y y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6011 eq12036
    | exact resolve eq12036 eq6011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12036
  have eq12113 : ∀ X0 : G, (k (σ y) X0) = (k (σ (M.op x y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq12032 X0
       have i₂ := eq120 X0
       grind)
    | exact superpose eq120 eq12032
    | exact resolve eq12032 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq12032
  have eq12116 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12022
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12022
    | exact resolve eq12022 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12022
  have eq12134 : (k (σ (M.op x y)) (k (σ y) (σ (M.op x y)))) = (k (σ y) (M.op (σ y) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5784 eq12104
    | exact resolve eq12104 eq5784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12104
  have eq12138 : (k (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12109
       have i₂ := eq123
       grind)
    | exact superpose eq123 eq12109
    | exact resolve eq12109 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq12109
  have eq12156 : (σ y) = (k (σ (M.op x y)) (k (σ y) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12134
       have i₂ := eq72 sF3 sF3
       grind)
    | exact superpose eq72 eq12134
    | exact resolve eq12134 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq12134
  have eq12159 : (M.op (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5784 eq12138
    | exact resolve eq12138 eq5784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5784 eq12138
  have eq12289 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12116 eq26
    | exact resolve eq26 eq12116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19687 : ∀ X0 : G, (k (τ (σ y)) X0) = (τ (k (σ (M.op x y)) (σ X0))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq12113 eq309
    | exact resolve eq309 eq12113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12113
  have eq19786 : ∀ X0 : G, (k (τ (σ (M.op x y))) X0) = (k (τ (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq19687 x
       have i₂ := eq309 sF1 x
       grind)
    | exact superpose eq309 eq19687
    | exact resolve eq19687 eq309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309 eq19687
  have eq19818 : ∀ X0 : G, (k y X0) = (k (τ (σ (M.op x y))) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29 eq19786
    | exact resolve eq19786 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq19786
  have eq19831 : ∀ X0 : G, (k y X0) = (k (M.op x y) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq30 eq19818
    | exact resolve eq19818 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq19818
  have eq20142 : (σ y) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12159 eq53
    | exact resolve eq53 eq12159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12159
  have eq23140 : ∀ X0 : G, (M.op x y) = (k y (τ (M.op (σ (M.op x y)) X0))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq19831 eq877
    | exact resolve eq877 eq19831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq877 eq19831
  have eq23240 : ∀ X0 : G, (M.op x y) = (τ (k (σ y) (M.op (σ (M.op x y)) X0))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq23140 X0
       have i₂ := eq350 (M.op (σ sF0) X0)
       grind)
    | exact superpose eq350 eq23140
    | exact resolve eq23140 eq350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350 eq23140
  have eq23288 : ∀ X0 : G, (M.op x y) = (τ (k (σ y) (M.op (σ (M.op x y)) X0))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq20 eq23240
    | (have j0 := eq23240 X0
       grind)
    | exact resolve eq23240 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23240
  have eq34202 : ∀ X0 : G, (σ (M.op x y)) = (k (σ y) (M.op (σ (M.op x y)) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq23288 eq15
    | exact resolve eq15 eq23288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23288
  have eq34260 : ∀ X0 : G, (σ (M.op x y)) = (k (σ y) (M.op (σ (M.op x y)) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq20 eq34202
    | (have j0 := eq34202 X0
       grind)
    | exact resolve eq34202 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34202
  have eq34472 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12289 eq138
    | exact resolve eq138 eq12289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq34507 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq34472
       have r₂ := eq27
       grind)
    | exact resolve eq34472 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34472
  have eq34537 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq34507 eq53
    | exact resolve eq53 eq34507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34507
  have eq34907 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq34537 eq12289
    | exact resolve eq12289 eq34537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34537
  have eq34935 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq34907
  have eq34937 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq34935
       have r₂ := eq27
       grind)
    | exact resolve eq34935 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34935
  have eq35322 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq34937 eq55
    | exact resolve eq55 eq34937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq35807 : ∀ X0 X1 : G, (M.op (M.op (σ x) (M.op X0 X1)) X0) = X0 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq35322 eq14
    | exact resolve eq14 eq35322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35322
  have eq41460 : (σ (M.op x y)) = (M.op (k (σ (M.op x y)) (σ x)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12116 eq9802
    | exact resolve eq9802 eq12116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9802
  have eq41493 : (σ (M.op x y)) = (M.op (k (σ (M.op x y)) (σ x)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq41460
       have r₂ := eq27
       grind)
    | exact resolve eq41460 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41460
  have eq41495 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq149 eq41493
    | exact resolve eq41493 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149 eq41493
  have eq481773 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20142 eq35807
    | exact resolve eq35807 eq20142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20142 eq35807
  have eq482077 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by grind
  clear eq481773
  have eq482104 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq482077
    | exact resolve eq482077 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482077
  have eq617542 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq34937 eq482104
    | exact resolve eq482104 eq34937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34937 eq482104
  have eq617648 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by grind
  clear eq617542
  have eq805304 : y = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq53 y x
       have i₂ := eq9974
       grind)
    | exact superpose eq9974 eq53
    | exact resolve eq53 eq9974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9974
  have eq837243 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq41495 eq53
    | exact resolve eq53 eq41495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41495
  have eq956185 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq837243 eq12289
    | exact resolve eq12289 eq837243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12289 eq837243
  have eq956356 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq956185
  have eq956359 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq956356
       have r₂ := eq27
       grind)
    | exact resolve eq956356 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq956356
  have eq956453 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq956359 eq34260
    | exact resolve eq34260 eq956359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34260 eq956359
  have eq957315 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq956453
  have eq959022 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq957315 eq12156
    | exact resolve eq12156 eq957315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12156 eq957315
  have eq959156 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq959022
  have eq959177 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6011 eq959156
    | exact resolve eq959156 eq6011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6011 eq959156
  have eq964191 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq959177 eq617648
    | exact resolve eq617648 eq959177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617648 eq959177
  have eq965107 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq964191
  have eq965132 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq965107
    | exact resolve eq965107 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq965107
  have eq965149 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq965132 eq27
    | exact resolve eq27 eq965132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq965132
  have eq965644 : x = (M.op x y) := by
    first
    | (have r₁ := eq965149
       have r₂ := eq12116
       grind)
    | exact resolve eq965149 eq12116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12116 eq965149
  have eq967114 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq965644 eq20
    | exact resolve eq20 eq965644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq967116 : x = (M.op x x) := by
    first
    | exact superpose eq965644 eq54
    | exact resolve eq54 eq965644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq968240 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq967114
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq967114
    | exact resolve eq967114 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq967114
  have eq968283 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq968240 eq26
    | exact resolve eq26 eq968240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq968302 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq968240 eq150
    | exact resolve eq150 eq968240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150
  have eq969484 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq968302
  have eq972016 : ∀ X0 X1 : G, (M.op (M.op x (M.op X0 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 x X1
       have i₂ := eq967116
       grind)
    | exact superpose eq967116 eq14
    | exact resolve eq14 eq967116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq967116
  have eq1012938 : y = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq972016 y y
       have i₂ := eq805304
       grind)
    | exact superpose eq805304 eq972016
    | exact resolve eq972016 eq805304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq805304 eq972016
  have eq1013236 : y = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1012938
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1012938
    | exact resolve eq1012938 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1012938
  have eq1013666 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq965644 eq1013236
    | exact resolve eq1013236 eq965644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1013236
  have eq1013950 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1013666
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1013666
    | exact resolve eq1013666 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1013666
  have eq1013951 : y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq1013950
  have eq1014104 : x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq965644 eq1013951
    | exact resolve eq1013951 eq965644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1013951
  have eq1014375 : y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq53 y x
       have i₂ := eq1014104
       grind)
    | exact superpose eq1014104 eq53
    | exact resolve eq53 eq1014104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq1014104
  have eq1014519 : y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1014375
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1014375
    | exact resolve eq1014375 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1014375
  have eq1014540 : x = y ∨ x = y := by
    first
    | exact superpose eq965644 eq1014519
    | exact resolve eq1014519 eq965644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq965644 eq1014519
  have eq1014541 : x = y := by grind
  clear eq1014540
  have eq1014555 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1014541
       grind)
    | exact superpose eq1014541 eq24
    | exact resolve eq24 eq1014541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1014541
  have eq1015288 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1014555
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1014555
    | exact resolve eq1014555 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1014555
  have eq1015439 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq968240 eq1015288
    | exact resolve eq1015288 eq968240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq968240 eq1015288
  have eq1016464 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1015439 eq968283
    | exact resolve eq968283 eq1015439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq968283 eq1015439
  have eq1016484 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq969484 eq1016464
    | exact resolve eq1016464 eq969484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq969484 eq1016464
  have eq1016879 : False := by grind
  exact eq1016879

/-- `Equation2739`: `x = ((y ◇ y) ◇ (x ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_y_pxy_pyx_pxy_Equation2739 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2739 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2739.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op X0 X2)) X0) = X0 := by
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
  clear eq35
  have eq53 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (M.op (M.op X0 X1) (M.op X0 X1)) X1
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq53 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq53
    | (have j0 := eq53 x y
       grind)
    | exact resolve eq53 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq26 eq53
    | (have j0 := eq53 (σ x) (σ y)
       grind)
    | exact resolve eq53 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (M.op X0 X1) X0
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op (M.op X1 X1) X0) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 X2) X1 X0
       have i₂ := eq53 X0 X2
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq55 eq53
    | exact resolve eq53 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 (M.op X0 X1)) = (k X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (M.op X0 X1)
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq13
    | (have j0 := eq13 X1 X0
       grind)
    | exact resolve eq13 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : x ≠ (M.op x y) ∨ (k y x) = (M.op y x) := by
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
  have eq68 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X1 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq82 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq82
    | (have j0 := eq82 (σ X0) (σ X1)
       grind)
    | exact resolve eq82 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq82 x y
       grind)
    | exact superpose eq82 eq44
    | (have j1 := eq82 x y
       grind)
    | exact resolve eq44 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq94
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq94
    | exact resolve eq94 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq101 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq99
    | exact resolve eq99 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq102 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq101
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq101
    | exact resolve eq101 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq107 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq102 eq82
    | (have j0 := eq82 (σ x) (σ y)
       grind)
    | exact resolve eq82 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq107
    | exact resolve eq107 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq111 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq108
       have r₂ := eq27
       grind)
    | exact resolve eq108 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq113 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq111
    | exact resolve eq111 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq116 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq113 eq55
    | exact resolve eq55 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq117 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq113 eq27
    | exact resolve eq27 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 (M.op X0 X1)) = X0 ∨ (M.op X0 (M.op X0 X1)) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X1) X0
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq12
    | (have j0 := eq12 (M.op X0 X1) X0
       grind)
    | (have r₁ := eq12 (M.op X0 X1) X0
       have r₂ := eq53 X0 X1
       grind)
    | exact resolve eq12 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = X0 ∨ (M.op X0 (M.op X0 X1)) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq120 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq142 : (σ x) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq116 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq144 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op X0 X0) (σ x)) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq116 eq14
    | exact resolve eq14 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq147 : (σ x) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq142
    | exact resolve eq142 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq154 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  clear eq36
  have eq163 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (M.op (M.op X0 X0) (σ x))) ∨ (M.op (σ y) (M.op (M.op X0 X0) (σ x))) = (k (M.op (M.op X0 X0) (σ x)) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq144 eq12
    | (have j0 := eq12 (M.op (M.op X0 X0) (σ x)) (σ y)
       grind)
    | (have r₁ := eq12 (M.op (M.op X0 X0) (σ x)) (σ y)
       have r₂ := eq144 X0
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq144 X0
       grind)
    | exact resolve eq12 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq167 : ∀ X0 : G, (M.op (σ y) (M.op (M.op X0 X0) (σ x))) = (k (M.op (M.op X0 X0) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ y) (M.op (M.op X0 X0) (σ x))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq163 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq392 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq167 sF2
       have i₂ := eq53 sF2 sF2
       grind)
    | exact superpose eq53 eq167
    | exact resolve eq167 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq398 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq392 eq102
    | exact resolve eq102 eq392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392
  have eq401 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by grind
  clear eq398
  have eq407 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq116 eq401
    | exact resolve eq401 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq401
  have eq416 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq407
  have eq425 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq416 eq102
    | exact resolve eq102 eq416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq429 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq416 eq147
    | (have r₁ := eq147
       have r₂ := eq416
       grind)
    | exact resolve eq147 eq416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147 eq416
  have eq471 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq429
  have eq472 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq471
  have eq476 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq425
  have eq809 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq476 eq472
    | exact resolve eq472 eq476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472 eq476
  have eq812 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq809
  have eq815 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq812
       have r₂ := eq27
       grind)
    | exact resolve eq812 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq812
  have eq818 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq815 eq28
    | exact resolve eq28 eq815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq824 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq815 eq62
    | exact resolve eq62 eq815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq815
  have eq877 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq818
    | exact resolve eq818 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq818
  have eq936 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq89 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq942 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq877 eq20
    | exact resolve eq20 eq877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq943 : (σ (k x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq877 eq45
    | exact resolve eq45 eq877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq945 : x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq877 eq54
    | exact resolve eq54 eq877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq949 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq877
  have eq953 : (k (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq943
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq943
    | exact resolve eq943 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq943
  have eq954 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq942
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq942
    | exact resolve eq942 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq942
  have eq956 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq954 eq26
    | exact resolve eq26 eq954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq959 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq954 eq40
    | exact resolve eq40 eq954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq995 : ∀ X0 : G, (σ (k X0 y)) = (σ (k X0 (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq41 eq959
    | exact resolve eq959 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq959
  have eq1070 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq113 eq824
    | exact resolve eq824 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq824
  have eq1077 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1070
  have eq1144 : x ≠ x ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq945
       grind)
    | exact superpose eq945 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq945
       grind)
    | exact resolve eq12 eq945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1148 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) := by grind
  clear eq1144
  have eq1150 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1148
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1148
    | exact resolve eq1148 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1148
  have eq1151 : x = (M.op x y) ∨ (M.op x y) = (k y x) := by grind
  clear eq1150
  have eq1152 : (M.op x y) = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1151
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1151
    | exact resolve eq1151 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1151
  have eq1248 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq154
       have i₂ := eq1152
       grind)
    | exact superpose eq1152 eq154
    | exact resolve eq154 eq1152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1152
  have eq1250 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq1248
    | exact resolve eq1248 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1248
  have eq1324 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq953 eq82
    | (have j0 := eq82 (σ x) (σ y)
       grind)
    | exact resolve eq82 eq953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq953
  have eq1325 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1324
    | exact resolve eq1324 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1324
  have eq1328 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1325
    | exact resolve eq1325 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1325
  have eq1570 : (k x (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1328 eq86
    | exact resolve eq86 eq1328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1328
  have eq1853 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op X0 X0) (σ x)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq956 eq59
    | (have j0 := eq59 (σ x) X0 (σ y)
       grind)
    | exact resolve eq59 eq956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq956
  have eq2622 : ∀ X0 : G, (k X0 (M.op x y)) = (τ (σ (k X0 y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq995 eq16
    | exact resolve eq16 eq995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2641 : ∀ X0 : G, (k X0 y) = (k X0 (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq2622 X0
       have i₂ := eq16 (k X0 y)
       grind)
    | exact superpose eq16 eq2622
    | exact resolve eq2622 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2622
  have eq3777 : (σ (k x y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1570 eq995
    | exact resolve eq995 eq1570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq995 eq1570
  have eq3781 : (σ (k x y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq3777
  have eq3787 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3781
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq3781
    | exact resolve eq3781 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3781
  have eq3791 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3787
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq3787
    | exact resolve eq3787 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq3787
  have eq3794 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq954 eq3791
    | exact resolve eq3791 eq954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3791
  have eq3817 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by grind
  clear eq3794
  have eq3819 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq3817
       have r₂ := eq27
       grind)
    | exact resolve eq3817 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3817
  have eq3829 : (k x (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3819 eq86
    | exact resolve eq86 eq3819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq3819
  have eq3842 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3829 eq2641
    | exact resolve eq2641 eq3829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2641 eq3829
  have eq3848 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq3842
  have eq4963 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq65 X0 X1
       have i₂ := eq57 X0 X1
       grind)
    | exact superpose eq57 eq65
    | (have j0 := eq65 X0 X1
       grind)
    | exact resolve eq65 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq7034 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 (M.op X0 X1)) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq131 X0 X1
       have i₂ := eq57 X0 X1
       grind)
    | exact superpose eq57 eq131
    | (have j0 := eq131 X0 X1
       grind)
    | exact resolve eq131 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq7035 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7034 X0 X1
       have i₂ := eq57 X0 X1
       grind)
    | exact superpose eq57 eq7034
    | (have j0 := eq7034 X0 X1
       grind)
    | exact resolve eq7034 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq7034
  have eq7070 : x = (k x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7035 y x
       have i₂ := eq945
       grind)
    | exact superpose eq945 eq7035
    | (have j0 := eq7035 x y
       grind)
    | exact resolve eq7035 eq945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq945
  have eq7072 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1077 eq7035
    | exact resolve eq7035 eq1077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1077 eq7035
  have eq7133 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq7072
       have r₂ := eq117
       grind)
    | exact resolve eq7072 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq7072
  have eq7134 : x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq7070
       have r₂ := eq949
       grind)
    | exact resolve eq7070 eq949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq949 eq7070
  have eq7266 : x = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3848
       have i₂ := eq7134
       grind)
    | exact superpose eq7134 eq3848
    | exact resolve eq3848 eq7134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3848 eq7134
  have eq7272 : x = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq7266
  have eq7289 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7272 eq15
    | exact resolve eq15 eq7272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7272
  have eq7306 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7289
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq7289
    | exact resolve eq7289 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7289
  have eq7402 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7306 eq27
    | exact resolve eq27 eq7306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7406 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7306 eq68
    | (have r₁ := eq68
       have r₂ := eq7306
       grind)
    | exact resolve eq68 eq7306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq7425 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq7406
  have eq8600 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7425 eq1250
    | exact resolve eq1250 eq7425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1250 eq7425
  have eq8608 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq8600
  have eq8664 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq954 eq8608
    | exact resolve eq8608 eq954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8676 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8608 eq53
    | exact resolve eq53 eq8608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq8608
  have eq8687 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq8664
  have eq8692 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq954 eq8676
    | exact resolve eq8676 eq954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq954 eq8676
  have eq8713 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq8692
  have eq8861 : (M.op (σ x) (σ y)) = (M.op (M.op (σ (M.op x y)) (σ x)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8713 eq1853
    | exact resolve eq1853 eq8713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1853 eq8713
  have eq8877 : (M.op (σ x) (σ y)) = (M.op (M.op (σ (M.op x y)) (σ x)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq8861
  have eq11598 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8687 eq8877
    | exact resolve eq8877 eq8687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8877
  have eq11619 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq11598
  have eq11620 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7306 eq11619
    | exact resolve eq11619 eq7306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7306 eq11619
  have eq11641 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq11620
  have eq11847 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11641 eq8687
    | exact resolve eq8687 eq11641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8687 eq11641
  have eq11864 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq11847
  have eq11868 : x = (M.op x y) := by
    first
    | (have r₁ := eq11864
       have r₂ := eq7402
       grind)
    | exact resolve eq11864 eq7402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7402 eq11864
  have eq11873 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq11868 eq20
    | exact resolve eq20 eq11868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq11876 : x = (M.op x x) := by
    first
    | exact superpose eq11868 eq54
    | exact resolve eq54 eq11868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq11878 : x ≠ x ∨ (k y x) = (M.op y x) := by
    first
    | exact superpose eq11868 eq66
    | (have r₁ := eq66
       have r₂ := eq11868
       grind)
    | exact resolve eq66 eq11868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq11904 : (k y x) = (M.op y x) := by grind
  clear eq11878
  have eq11915 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq11873
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11873
    | exact resolve eq11873 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11873
  have eq11916 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq11915 eq26
    | exact resolve eq26 eq11915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq12025 : ∀ X0 X1 : G, (M.op (M.op x (M.op X0 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 x X1
       have i₂ := eq11876
       grind)
    | exact superpose eq11876 eq14
    | exact resolve eq14 eq11876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12108 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq4963 x x
       have i₂ := eq11876
       grind)
    | exact superpose eq11876 eq4963
    | (have r₁ := eq4963 x x
       have r₂ := eq11876
       grind)
    | exact resolve eq4963 eq11876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4963 eq11876
  have eq12109 : x = (k x x) := by grind
  clear eq12108
  have eq12711 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq936 x x
       have i₂ := eq12109
       grind)
    | exact superpose eq12109 eq936
    | (have j0 := eq936 x x
       grind)
    | exact resolve eq936 eq12109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936 eq12109
  have eq12714 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq12711
  have eq12721 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq12714
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq12714
    | exact resolve eq12714 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12714
  have eq12731 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq11915 eq12721
    | exact resolve eq12721 eq11915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12721
  have eq14485 : (k (σ y) (σ x)) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq154
       have i₂ := eq11904
       grind)
    | exact superpose eq11904 eq154
    | exact resolve eq154 eq11904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154 eq11904
  have eq14498 : (k (σ y) (σ (M.op x y))) = (σ (M.op y x)) := by
    first
    | exact superpose eq11915 eq14485
    | exact resolve eq14485 eq11915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14485
  have eq14915 : (M.op y x) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq16 (M.op y x)
       have i₂ := eq14498
       grind)
    | exact superpose eq14498 eq16
    | exact resolve eq16 eq14498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14498
  have eq15345 : (τ (σ y)) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq7133 eq14915
    | exact resolve eq14915 eq7133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7133 eq14915
  have eq15378 : y = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq15345
    | exact resolve eq15345 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq15345
  have eq15379 : y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq11868 eq15378
    | exact resolve eq15378 eq11868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15378
  have eq17392 : y = (M.op (M.op x y) y) ∨ x = y := by
    first
    | (have i₁ := eq12025 y x
       have i₂ := eq15379
       grind)
    | exact superpose eq15379 eq12025
    | exact resolve eq12025 eq15379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12025 eq15379
  have eq17481 : y = (M.op (M.op x y) y) ∨ x = y := by
    first
    | (have i₁ := eq17392
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17392
    | exact resolve eq17392 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17392
  have eq17518 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq11868 eq17481
    | exact resolve eq17481 eq11868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17481
  have eq17534 : y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq17518
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17518
    | exact resolve eq17518 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq17518
  have eq17537 : x = y ∨ x = y := by
    first
    | exact superpose eq11868 eq17534
    | exact resolve eq17534 eq11868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11868 eq17534
  have eq17538 : x = y := by grind
  clear eq17537
  have eq17540 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq17538
       grind)
    | exact superpose eq17538 eq24
    | exact resolve eq24 eq17538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq17538
  have eq17586 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq17540
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq17540
    | exact resolve eq17540 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq17540
  have eq17598 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq11915 eq17586
    | exact resolve eq17586 eq11915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11915 eq17586
  have eq18312 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq17598 eq11916
    | exact resolve eq11916 eq17598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11916 eq17598
  have eq18329 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12731 eq18312
    | exact resolve eq18312 eq12731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12731 eq18312
  have eq18370 : False := by grind
  exact eq18370

/-- `Equation2739`: `x = ((y ◇ y) ◇ (x ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxx_pyx_pxy_Equation2739 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2739 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2739.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op X0 X2)) X0) = X0 := by
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
  have eq44 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq45 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq44
  have eq48 : (σ (k x x)) = (k (σ x) (σ x)) := by
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
  have eq49 : (σ (k x y)) = (k (σ x) (σ y)) := by
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
  clear eq36
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq56 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (M.op (M.op X0 X1) (M.op X0 X1)) X1
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq56 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq56
    | (have j0 := eq56 x y
       grind)
    | exact resolve eq56 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq27 eq56
    | (have j0 := eq56 (σ x) (σ y)
       grind)
    | exact resolve eq56 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq57 eq56
    | exact resolve eq56 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op X0 X0) x) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq57 eq14
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq65 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq58 eq56
    | exact resolve eq56 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op X0 X0) (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq58 eq14
    | exact resolve eq14 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq67 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq75 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq49
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq49 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq75
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq75
    | exact resolve eq75 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq81 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq21 eq80
    | exact resolve eq80 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq83 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (M.op X0 X1)
       have i₂ := eq56 X0 X1
       grind)
    | exact superpose eq56 eq12
    | (have j0 := eq12 (M.op X0 X1) X0
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X1)
       have r₂ := eq56 X0 X1
       grind)
    | exact resolve eq12 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq63 eq12
    | (have j0 := eq12 x (M.op x y)
       grind)
    | (have r₁ := eq12 (M.op x y) x
       have r₂ := eq63
       grind)
    | exact resolve eq12 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq88 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq65 eq12
    | (have j0 := eq12 (σ x) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq12 (M.op (σ x) (σ y)) (σ x)
       have r₂ := eq65
       grind)
    | exact resolve eq12 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq91 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq88
  have eq93 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) := by grind
  clear eq85
  have eq94 : ∀ X0 X1 : G, (k X0 (M.op X0 X1)) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq83 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq104 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq112 : (k (σ y) (σ x)) = (σ (k y x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq114 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq117 : (σ (k y y)) = (M.op (σ y) (σ y)) := by grind
  clear eq113
  have eq118 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq117
  have eq124 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq112
       grind)
    | exact superpose eq112 eq16
    | exact resolve eq16 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq114 eq16
    | exact resolve eq16 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq144 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq38 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq38
    | (have j0 := eq38 x
       grind)
    | exact resolve eq38 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq157 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq144 eq16
    | exact resolve eq16 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq891 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (k X0 X1)) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq56 (σ X0) (σ X1)
       have i₂ := eq67 X0 X1
       grind)
    | exact superpose eq67 eq56
    | (have j1 := eq67 X0 X1
       grind)
    | exact resolve eq56 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq13418 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq81 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13419 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq27 eq13418
    | exact resolve eq13418 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13418
  have eq13430 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq13419
       have r₂ := eq28
       grind)
    | exact resolve eq13419 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13419
  have eq14282 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq13430 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq13430
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq13430
       grind)
    | exact resolve eq12 eq13430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14285 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq13430 eq56
    | exact resolve eq56 eq13430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13430
  have eq14302 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = y := by grind
  clear eq14282
  have eq14303 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by grind
  clear eq14302
  have eq14304 : x = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq27 eq14285
    | exact resolve eq14285 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14285
  have eq14305 : x ≠ x ∨ x = y ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq14304
       grind)
    | exact superpose eq14304 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq14304
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq14304
       grind)
    | exact resolve eq12 eq14304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14308 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq56 y x
       have i₂ := eq14304
       grind)
    | exact superpose eq14304 eq56
    | exact resolve eq56 eq14304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14312 : y = (k y x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq94 y x
       have i₂ := eq14304
       grind)
    | exact superpose eq14304 eq94
    | exact resolve eq94 eq14304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq14304
  have eq14324 : y = (k y x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq14312
  have eq14325 : x ≠ x ∨ x = y ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq14305
  have eq14326 : x = (k x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq14325
  have eq14327 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq14308
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14308
    | exact resolve eq14308 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14308
  have eq14335 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq14327 eq91
    | exact resolve eq91 eq14327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14327
  have eq14353 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq14335
  have eq14487 : (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq112
       have i₂ := eq14324
       grind)
    | exact superpose eq14324 eq112
    | exact resolve eq112 eq14324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14498 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq891 y x
       have i₂ := eq14324
       grind)
    | exact superpose eq14324 eq891
    | (have j0 := eq891 y x
       grind)
    | exact resolve eq891 eq14324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq891 eq14324
  have eq14503 : (σ y) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14498
       have i₂ := eq45 y
       grind)
    | exact superpose eq45 eq14498
    | exact resolve eq14498 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq14498
  have eq14513 : (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14487
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq14487
    | exact resolve eq14487 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14487
  have eq14515 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14503
       have i₂ := eq118
       grind)
    | exact superpose eq118 eq14503
    | exact resolve eq14503 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq14503
  have eq14521 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14515
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq14515
    | exact resolve eq14515 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14515
  have eq14525 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14521
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq14521
    | exact resolve eq14521 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14521
  have eq14531 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14525
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq14525
    | exact resolve eq14525 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14525
  have eq14536 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq14531
    | exact resolve eq14531 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14531
  have eq14537 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq14536
  have eq14543 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14537
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq14537
    | exact resolve eq14537 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14537
  have eq14546 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14543
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq14543
    | exact resolve eq14543 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14543
  have eq14547 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq14546
  have eq14549 : (σ x) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq49
       have i₂ := eq14326
       grind)
    | exact superpose eq14326 eq49
    | exact resolve eq49 eq14326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq14326
  have eq14574 : (σ x) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14549
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq14549
    | exact resolve eq14549 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14549
  have eq14819 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14513 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq14513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14513
  have eq14820 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq14819
  have eq14822 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq14820
    | exact resolve eq14820 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14820
  have eq14823 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq14822
  have eq14852 : (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq14547 eq66
    | exact resolve eq66 eq14547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq14547
  have eq15127 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14574 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq14574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14574
  have eq15128 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq15127
  have eq15132 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq15128
    | exact resolve eq15128 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15128
  have eq16517 : (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq14303 eq81
    | exact resolve eq81 eq14303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq14303
  have eq16531 : x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq16517
  have eq16551 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq56 y x
       have i₂ := eq16531
       grind)
    | exact superpose eq16531 eq56
    | exact resolve eq56 eq16531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16531
  have eq16573 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16551
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq16551
    | exact resolve eq16551 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16551
  have eq16696 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq16573 eq30
    | exact resolve eq30 eq16573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16573
  have eq16813 : x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq16696
    | exact resolve eq16696 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16696
  have eq16814 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq16813
  have eq16834 : x = (τ (σ (M.op x y))) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq16814 eq29
    | exact resolve eq29 eq16814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16856 : (k y x) = (τ (k (σ y) (σ (M.op x y)))) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq16814 eq124
    | exact resolve eq124 eq16814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16933 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq16814 eq14353
    | exact resolve eq14353 eq16814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14353 eq16814
  have eq16942 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq16933
  have eq17001 : (k y x) = (k y (M.op x y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq131 eq16856
    | exact resolve eq16856 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16856
  have eq17013 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq16834
    | exact resolve eq16834 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16834
  have eq17028 : (σ y) = (σ (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq17013 eq21
    | exact resolve eq21 eq17013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17013
  have eq17186 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17028
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq17028
    | exact resolve eq17028 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17028
  have eq17342 : (k y x) = (τ (k (σ (M.op x y)) (σ x))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq17186 eq124
    | exact resolve eq124 eq17186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq17186
  have eq17474 : (k y x) = (k (M.op x y) x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq157 eq17342
    | exact resolve eq17342 eq157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157 eq17342
  have eq20032 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq17474 eq93
    | exact resolve eq93 eq17474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq17474
  have eq20063 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq20032
  have eq20114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq112
       have i₂ := eq20063
       grind)
    | exact superpose eq20063 eq112
    | exact resolve eq112 eq20063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq20063
  have eq20150 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq21 eq20114
    | exact resolve eq20114 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20114
  have eq21953 : (τ (σ y)) = (k y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq16942 eq131
    | exact resolve eq131 eq16942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq16942
  have eq21985 : y = (k y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq21953
    | exact resolve eq21953 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21953
  have eq22647 : y = (k y x) ∨ x = y ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq21985 eq17001
    | exact resolve eq17001 eq21985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17001 eq21985
  have eq22659 : y = (k y x) ∨ x = y ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq22647
  have eq23885 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = y ∨ x = y ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq22659
       grind)
    | exact superpose eq22659 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq22659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22659
  have eq23886 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq23885
  have eq23890 : y = (M.op x y) ∨ y = (M.op y x) ∨ x = y ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq23886
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq23886
    | exact resolve eq23886 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23886
  have eq23891 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq23890
  have eq25097 : y = (M.op y y) ∨ y = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq56 y x
       have i₂ := eq23891
       grind)
    | exact superpose eq23891 eq56
    | exact resolve eq56 eq23891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26063 : (M.op x y) = (M.op (M.op y x) (M.op x y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq64 y
       have i₂ := eq25097
       grind)
    | exact superpose eq25097 eq64
    | exact resolve eq64 eq25097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq25097
  have eq77846 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq14823 eq14852
    | exact resolve eq14852 eq14823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14852
  have eq77880 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq77846
  have eq78322 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq77880 eq56
    | exact resolve eq56 eq77880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77880
  have eq112785 : (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq26063
       have i₂ := eq23891
       grind)
    | exact superpose eq23891 eq26063
    | exact resolve eq26063 eq23891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23891 eq26063
  have eq112823 : (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq112785
  have eq112832 : y = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq112823 eq56
    | exact resolve eq56 eq112823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq112823
  have eq123222 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15132 eq14823
    | exact resolve eq14823 eq15132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14823 eq15132
  have eq123265 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq123222
  have eq123273 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq123265 eq28
    | exact resolve eq28 eq123265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123280 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq123265 eq91
    | exact resolve eq91 eq123265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq123265
  have eq123394 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq123280
  have eq123604 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20150 eq123394
    | exact resolve eq123394 eq20150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20150 eq123394
  have eq123687 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq123604
  have eq123710 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq123687
       have r₂ := eq123273
       grind)
    | exact resolve eq123687 eq123273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123273 eq123687
  have eq123787 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq123710 eq78322
    | exact resolve eq78322 eq123710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78322
  have eq123816 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq123787
  have eq123858 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq123816
    | exact resolve eq123816 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123816
  have eq123944 : (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq123858 eq123710
    | exact resolve eq123710 eq123858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123710 eq123858
  have eq123945 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq123944
  have eq124011 : y = (τ (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq123945 eq30
    | exact resolve eq30 eq123945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123945
  have eq124448 : x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq124011
    | exact resolve eq124011 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq124011
  have eq124449 : x = (M.op x y) ∨ x = y := by grind
  clear eq124448
  have eq124680 : y = (M.op x y) ∨ x = y ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq124449 eq112832
    | exact resolve eq112832 eq124449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112832
  have eq124681 : y = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq124680
  have eq124736 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq124681
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq124681
    | exact resolve eq124681 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124681
  have eq128132 : y = (τ (σ (M.op x y))) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq124736 eq30
    | exact resolve eq30 eq124736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq124736
  have eq128558 : y = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq128132
    | exact resolve eq128132 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq128132
  have eq128559 : y = (M.op x y) ∨ x = y := by grind
  clear eq128558
  have eq128917 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq128559 eq124449
    | exact resolve eq124449 eq128559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124449 eq128559
  have eq128920 : x = y := by grind
  clear eq128917
  have eq129185 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq128920
       grind)
    | exact superpose eq128920 eq19
    | exact resolve eq19 eq128920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq129186 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq128920
       grind)
    | exact superpose eq128920 eq25
    | exact resolve eq25 eq128920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq128920
  have eq129448 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq129186
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq129186
    | exact resolve eq129186 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq129186
  have eq129479 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq129448 eq27
    | exact resolve eq27 eq129448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq129448
  have eq130101 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq129479 eq104
    | exact resolve eq104 eq129479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq129479
  have eq130316 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq130101
       have i₂ := eq129185
       grind)
    | exact superpose eq129185 eq130101
    | exact resolve eq130101 eq129185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129185 eq130101
  have eq130332 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq130316 eq15
    | exact resolve eq15 eq130316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130316
  have eq130592 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq130332
    | exact resolve eq130332 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq130332
  have eq130677 : False := by grind
  exact eq130677

/-- `Equation2755`: `x = ((y ◇ y) ◇ (z ◇ x)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxy_pxx_pyx_Equation2755 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2755 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2755.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op X2 X0)) X2) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq28 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq43 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op (M.op X0 X1) (M.op X0 X1)) X0
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq43 (M.op X1 X0) X1
       have i₂ := eq43 X1 X0
       grind)
    | exact superpose eq43 eq43
    | exact resolve eq43 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) X0 X1
       have i₂ := eq45 (M.op X0 X0) X1
       grind)
    | exact superpose eq45 eq9
    | exact resolve eq9 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq100 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq98 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq98
    | (have j0 := eq98 X0 X1
       grind)
    | exact resolve eq98 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq135 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X1 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq54
    | exact resolve eq54 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq139 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq45 (σ X0) (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq45
    | exact resolve eq45 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq333 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ (k X0 X1)) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq43 (σ X1) (σ X0)
       have i₂ := eq100 X1 X0
       grind)
    | exact superpose eq100 eq43
    | (have j1 := eq100 X1 X0
       grind)
    | exact resolve eq43 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq100
  have eq474 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq28
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq7446 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ (k X0 X1)) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq45 (σ X0) (σ X1)
       have i₂ := eq333 X0 X1
       grind)
    | exact superpose eq333 eq45
    | (have j1 := eq333 X0 X1
       grind)
    | exact resolve eq45 eq333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333
  have eq7457 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ (k X0 X1)) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq7446 X0 X1
       have i₂ := eq139 X0
       grind)
    | exact superpose eq139 eq7446
    | (have j0 := eq7446 X0 X1
       grind)
    | exact resolve eq7446 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139 eq7446
  have eq7458 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (k X0 X1)) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq7457 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7457
  have eq14480 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ (k X0 X1))) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7458 (τ X0) (τ X1)
       have i₂ := eq474 X1 X0
       grind)
    | exact superpose eq474 eq7458
    | (have j0 := eq7458 (τ X0) (τ X1)
       grind)
    | exact resolve eq7458 eq474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474
  have eq14546 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq45 (σ X1) (σ (k X0 X1))
       have i₂ := eq7458 X0 X1
       grind)
    | exact superpose eq7458 eq45
    | (have j1 := eq7458 X0 X1
       grind)
    | exact resolve eq45 eq7458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7458
  have eq14589 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ (k X0 X1))) X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14480 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq14480
    | (have j0 := eq14480 X0 X1
       grind)
    | exact resolve eq14480 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14480
  have eq14602 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (k X0 X1) X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14589 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq14589
    | (have j0 := eq14589 X0 X1
       grind)
    | exact resolve eq14589 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14589
  have eq14607 : ∀ X0 X1 : G, (M.op (k X0 X1) X1) = X0 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14602 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq14602
    | (have j0 := eq14602 X0 X1
       grind)
    | exact resolve eq14602 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14602
  have eq14610 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op (k X0 X1) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14607 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq14607
    | (have j0 := eq14607 X0 X1
       grind)
    | exact resolve eq14607 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14607
  have eq14612 : ∀ X0 X1 : G, (M.op (k X0 X1) X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14610 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq14610
    | (have j0 := eq14610 X0 X1
       grind)
    | exact resolve eq14610 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14610
  have eq14647 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq45 X1 (k X0 X1)
       have i₂ := eq14612 X0 X1
       grind)
    | exact superpose eq14612 eq45
    | (have j1 := eq14612 (k X0 X1) (M.op X1 X0)
       grind)
    | exact resolve eq45 eq14612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq14612
  have eq14874 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14647 X1 (τ X0)
       grind)
    | exact superpose eq14647 eq19
    | (have j1 := eq14647 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq14647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq14647
  have eq106540 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14874 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq14874
    | exact resolve eq14874 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14874
  have eq106740 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq106540 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq106540
    | (have j0 := eq106540 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq106540 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106540
  have eq325332 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14546 y x
       grind)
    | exact superpose eq14546 eq16
    | (have j1 := eq14546 x y
       grind)
    | exact resolve eq16 eq14546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14546
  have eq325631 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq325332
       have i₂ := eq106740 x y
       grind)
    | exact superpose eq106740 eq325332
    | (have j1 := eq106740 (σ x) (σ y)
       grind)
    | (have r₁ := eq325332
       have r₂ := eq106740 x y
       grind)
    | (have r₁ := eq325332
       have r₂ := eq106740 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq325332
       have r₂ := eq106740 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq325332 eq106740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106740 eq325332
  have eq325634 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq325631
  have eq327189 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq325634
       grind)
    | exact superpose eq325634 eq16
    | exact resolve eq16 eq325634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325634
  have eq327190 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq327189
       have r₂ := eq135 x (σ x)
       grind)
    | exact resolve eq327189 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135 eq327189
  have eq327191 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq327190
       grind)
    | exact superpose eq327190 eq16
    | exact resolve eq16 eq327190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq327192 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq327190
       grind)
    | exact superpose eq327190 eq10
    | exact resolve eq10 eq327190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327190
  have eq327385 : x = y := by
    first
    | (have i₁ := eq327192
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq327192
    | exact resolve eq327192 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327192
  have eq327386 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq327191
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq327191
    | exact resolve eq327191 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq327191
  have eq327388 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq327386
       have i₂ := eq327385
       grind)
    | exact superpose eq327385 eq327386
    | exact resolve eq327386 eq327385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327385 eq327386
  have eq327389 : False := by grind
  exact eq327389

/-- `Equation2755`: `x = ((y ◇ y) ◇ (z ◇ x)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_y_pxx_x_pxy_Equation2755 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2755 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2755.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op X2 X0)) X2) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq22
  have eq44 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op (M.op X0 X1) (M.op X0 X1)) X0
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq44 (M.op X1 X0) X1
       have i₂ := eq44 X1 X0
       grind)
    | exact superpose eq44 eq44
    | exact resolve eq44 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op X0 X0)
       have i₂ := eq44 (M.op X0 X0) (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq44 eq9
    | exact resolve eq9 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq55 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) X0 X1
       have i₂ := eq46 (M.op X0 X0) X1
       grind)
    | exact superpose eq46 eq9
    | exact resolve eq9 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq46 (M.op X1 X1) X0
       have i₂ := eq49 X1 (M.op X0 (M.op X1 X1))
       grind)
    | exact superpose eq49 eq46
    | exact resolve eq46 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq94 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq96 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq94 X0 X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq94
    | (have j0 := eq94 X0 X1
       grind)
    | exact resolve eq94 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq126 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq66 X1 (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq66
    | exact resolve eq66 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X1 (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq55
    | exact resolve eq55 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq129 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq49 (σ X0) X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq49
    | exact resolve eq49 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq49
  have eq272 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq129 X0 (σ (M.op X1 X1))
       have i₂ := eq126 X1 (σ (M.op X0 X0))
       grind)
    | exact superpose eq126 eq129
    | exact resolve eq129 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126 eq129
  have eq307 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq96 x y
       grind)
    | exact superpose eq96 eq16
    | (have j1 := eq96 x y
       grind)
    | exact resolve eq16 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq370 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq128 X1 X0
       grind)
    | exact superpose eq128 eq10
    | exact resolve eq10 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5536 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq307
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq307
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq307
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq307
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq307 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307
  have eq5537 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq5536
  have eq45667 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5537
       grind)
    | exact superpose eq5537 eq16
    | exact resolve eq16 eq5537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5537
  have eq45668 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq45667
       have r₂ := eq128 x (σ x)
       grind)
    | exact resolve eq45667 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45667
  have eq588738 : y = (τ (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq45668
       grind)
    | exact superpose eq45668 eq10
    | exact resolve eq10 eq45668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45668
  have eq589046 : x = y ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq588738
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq588738
    | exact resolve eq588738 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588738
  have eq589056 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq589046
       grind)
    | exact superpose eq589046 eq16
    | exact resolve eq16 eq589046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589046
  have eq589057 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq589056
       have r₂ := eq128 x (σ x)
       grind)
    | exact resolve eq589056 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq589056
  have eq589275 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq589057
       grind)
    | exact superpose eq589057 eq10
    | exact resolve eq10 eq589057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589057
  have eq589755 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq589275
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq589275
    | exact resolve eq589275 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589275
  have eq589756 : y = (M.op x x) := by grind
  clear eq589755
  have eq590759 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq66 X0 x
       have i₂ := eq589756
       grind)
    | exact superpose eq589756 eq66
    | exact resolve eq66 eq589756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq590771 : ∀ X0 : G, (σ y) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq272 x X0
       have i₂ := eq589756
       grind)
    | exact superpose eq589756 eq272
    | exact resolve eq272 eq589756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq590777 : ∀ X0 : G, (M.op X0 X0) = (τ y) := by
    intro X0
    first
    | (have i₁ := eq370 x X0
       have i₂ := eq589756
       grind)
    | exact superpose eq589756 eq370
    | exact resolve eq370 eq589756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370 eq589756
  have eq591556 : (σ y) = (σ (τ y)) := by
    first
    | (have i₁ := eq590771 x
       have i₂ := eq590777 x
       grind)
    | exact superpose eq590777 eq590771
    | exact resolve eq590771 eq590777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590771 eq590777
  have eq591612 : y = (σ y) := by
    first
    | (have i₁ := eq591556
       have i₂ := eq11 y
       grind)
    | exact superpose eq11 eq591556
    | exact resolve eq591556 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591556
  have eq591669 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq591612
       grind)
    | exact superpose eq591612 eq16
    | exact resolve eq16 eq591612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591612
  have eq592199 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq591669
       have i₂ := eq590759 (σ x)
       grind)
    | exact superpose eq590759 eq591669
    | exact resolve eq591669 eq590759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591669
  have eq592436 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq592199
       have i₂ := eq590759 x
       grind)
    | exact superpose eq590759 eq592199
    | exact resolve eq592199 eq590759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590759 eq592199
  have eq592437 : False := by grind
  exact eq592437

/-- `Equation2755`: `x = ((y ◇ y) ◇ (z ◇ x)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(Y,X) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxy_pxx_pxy_Equation2755 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2755 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2755.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op X2 X0)) X2) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq28 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq43 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op (M.op X0 X1) (M.op X0 X1)) X0
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq43 (M.op X1 X0) X1
       have i₂ := eq43 X1 X0
       grind)
    | exact superpose eq43 eq43
    | exact resolve eq43 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) X0 X1
       have i₂ := eq45 (M.op X0 X0) X1
       grind)
    | exact superpose eq45 eq9
    | exact resolve eq9 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) (τ X1)) = (M.op (τ X1) X0) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq133 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X1 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq54
    | exact resolve eq54 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq136 : ∀ X0 X1 X2 : G, (M.op (M.op (σ (M.op X0 X0)) (M.op X1 X2)) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5168 : ∀ X0 X1 : G, (M.op (τ X1) (τ X1)) = (M.op (τ X1) (M.op (τ X1) X0)) ∨ (σ X0) = (k (σ (M.op (τ X1) X0)) X1) ∨ (τ X1) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq95 (M.op (τ X1) X0) X1
       have i₂ := eq43 (τ X1) X0
       grind)
    | exact superpose eq43 eq95
    | (have j0 := eq95 (M.op (τ X1) X0) X1
       grind)
    | exact resolve eq95 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq95
  have eq76962 : ∀ X0 X1 X2 : G, (M.op (τ X0) X2) = (M.op (M.op (σ (M.op X1 X1)) (M.op (τ X0) (τ X0))) (τ X0)) ∨ (σ X2) = (k (σ (M.op (τ X0) X2)) X0) ∨ (τ X0) = (M.op (τ X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq136 X1 (τ X0) (M.op (τ X0) X2)
       have i₂ := eq5168 X2 X0
       grind)
    | exact superpose eq5168 eq136
    | (have j1 := eq5168 X2 X0
       grind)
    | exact resolve eq136 eq5168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5168
  have eq76970 : ∀ X0 X2 : G, (τ X0) = (M.op (τ X0) X2) ∨ (σ X2) = (k (σ (M.op (τ X0) X2)) X0) ∨ (τ X0) = (M.op (τ X0) X2) := by
    intro X0 X2
    first
    | (have i₁ := eq76962 X0 x X2
       have i₂ := eq136 x (τ X0) (τ X0)
       grind)
    | exact superpose eq136 eq76962
    | (have j0 := eq76962 X0 x X2
       grind)
    | exact resolve eq76962 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136 eq76962
  have eq76971 : ∀ X0 X2 : G, (σ X2) = (k (σ (M.op (τ X0) X2)) X0) ∨ (τ X0) = (M.op (τ X0) X2) := by
    intro X0 X2
    first
    | (have j0 := eq76970 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76970
  have eq631278 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq76971 X0 (M.op X1 (τ X0))
       have i₂ := eq45 (τ X0) X1
       grind)
    | exact superpose eq45 eq76971
    | exact resolve eq76971 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq631707 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ (M.op (τ (σ X1)) X0))) X1) ∨ (τ (σ X1)) = (M.op (τ (σ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq28 (σ (M.op (τ (σ X1)) X0)) X1
       have i₂ := eq76971 (σ X1) X0
       grind)
    | exact superpose eq76971 eq28
    | (have j1 := eq76971 (σ X1) X0
       grind)
    | exact resolve eq28 eq76971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq76971
  have eq632073 : ∀ X0 X1 : G, (τ (σ X0)) = (k (M.op (τ (σ X1)) X0) X1) ∨ (τ (σ X1)) = (M.op (τ (σ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq631707 X0 X1
       have i₂ := eq10 (M.op (τ (σ X1)) X0)
       grind)
    | exact superpose eq10 eq631707
    | (have j0 := eq631707 X0 X1
       grind)
    | exact resolve eq631707 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631707
  have eq632447 : ∀ X0 X1 : G, (τ (σ X0)) = (k (M.op X1 X0) X1) ∨ (τ (σ X1)) = (M.op (τ (σ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq632073 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq632073
    | (have j0 := eq632073 X0 X1
       grind)
    | exact resolve eq632073 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632073
  have eq632621 : ∀ X0 X1 : G, (k (M.op X1 X0) X1) = X0 ∨ (τ (σ X1)) = (M.op (τ (σ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq632447 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq632447
    | (have j0 := eq632447 X0 X1
       grind)
    | exact resolve eq632447 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632447
  have eq632686 : ∀ X0 X1 : G, (k (M.op X1 X0) X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq632621 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq632621
    | (have j0 := eq632621 X0 X1
       grind)
    | exact resolve eq632621 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632621
  have eq632755 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq632686 (M.op X1 X0) X0
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq632686
    | exact resolve eq632686 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq632686
  have eq634738 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq632755 (σ X0) (σ X1)
       grind)
    | exact superpose eq632755 eq15
    | (have j1 := eq632755 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq632755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632755
  have eq636370 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq631278 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq631278
    | exact resolve eq631278 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631278
  have eq636805 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq636370 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq636370
    | (have j0 := eq636370 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq636370 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636370
  have eq653068 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq634738 x y
       grind)
    | exact superpose eq634738 eq16
    | (have j1 := eq634738 x y
       grind)
    | exact resolve eq16 eq634738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634738
  have eq653425 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq653068
       have i₂ := eq636805 y x
       grind)
    | exact superpose eq636805 eq653068
    | (have j1 := eq636805 (σ x) (σ y)
       grind)
    | (have r₁ := eq653068
       have r₂ := eq636805 y x
       grind)
    | (have r₁ := eq653068
       have r₂ := eq636805 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq653068
       have r₂ := eq636805 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq653068 eq636805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636805 eq653068
  have eq653428 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq653425
  have eq654589 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq653428
       grind)
    | exact superpose eq653428 eq16
    | exact resolve eq16 eq653428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653428
  have eq654590 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq654589
       have r₂ := eq133 x (σ x)
       grind)
    | exact resolve eq654589 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq654589
  have eq654591 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq654590
       grind)
    | exact superpose eq654590 eq16
    | exact resolve eq16 eq654590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq654592 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq654590
       grind)
    | exact superpose eq654590 eq10
    | exact resolve eq10 eq654590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654590
  have eq654832 : x = y := by
    first
    | (have i₁ := eq654592
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq654592
    | exact resolve eq654592 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654592
  have eq654833 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq654591
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq654591
    | exact resolve eq654591 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq654591
  have eq654834 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq654833
       have i₂ := eq654832
       grind)
    | exact superpose eq654832 eq654833
    | exact resolve eq654833 eq654832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654832 eq654833
  have eq654835 : False := by grind
  exact eq654835

/-- `Equation2860`: `x = ((x ◇ (x ◇ y)) ◇ z) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(Y,X) = m(Y,Y) then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pyx_pyy_pxy_y_pyx_Equation2860 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2860 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2860.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op b a ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X0 X1)) X2) X2) = X0 := by
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
  clear eq35
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
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X0 X1)) X2) = (M.op (M.op (M.op (M.op (M.op X0 (M.op X0 X1)) X2) X0) X3) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 (M.op X0 X1)) X2) X2 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op (M.op X0 (M.op X0 X1)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 (M.op X0 X1)) X2 (M.op (M.op X0 (M.op X0 X1)) X2)
       have i₂ := eq14 X0 X1 (M.op (M.op X0 (M.op X0 X1)) X2)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq65 (σ X0)
       grind)
    | exact superpose eq65 eq10
    | exact resolve eq10 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq65 x
       grind)
    | exact superpose eq65 eq43
    | exact resolve eq43 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq69 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq65 sF2
       grind)
    | exact superpose eq65 eq49
    | exact resolve eq49 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq70 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq69
       have i₂ := eq65 x
       grind)
    | exact superpose eq65 eq69
    | exact resolve eq69 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq71 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq68
       have i₂ := eq65 sF2
       grind)
    | exact superpose eq65 eq68
    | exact resolve eq68 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq72 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq67 X0
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq67
    | exact resolve eq67 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq76 : (M.op x y) ≠ (M.op x x) ∨ (M.op x y) = (M.op y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq99 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  clear eq36
  have eq108 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq99
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq99
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq99 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq99
       grind)
    | exact superpose eq99 eq16
    | exact resolve eq16 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq108
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq108
    | exact resolve eq108 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq20 eq114
    | exact resolve eq114 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq116 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq115
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq115
    | exact resolve eq115 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq116
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq116
    | exact resolve eq116 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq404 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X1)) (M.op (M.op X0 (M.op X0 X1)) X2)) = (M.op (M.op X0 (M.op X0 X1)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 (M.op X0 (M.op X0 X1)) X2 (M.op (M.op X0 (M.op X0 X1)) X2)
       have i₂ := eq14 X0 X1 (M.op (M.op X0 (M.op X0 X1)) X2)
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq646 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = (M.op (M.op X0 X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X0 X1 X0 X2
       have i₂ := eq14 X0 X1 X0
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq845 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq84 X0 X1
       have i₂ := eq72 X1
       grind)
    | exact superpose eq72 eq84
    | (have j0 := eq84 X0 X1
       grind)
    | exact resolve eq84 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq878 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (M.op (σ X0) (σ y)) = (M.op (σ y) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq845 y X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq845
    | (have j0 := eq845 y X0
       grind)
    | exact resolve eq845 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq845
  have eq1048 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X3) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq646 X0 x X3
       have i₂ := eq646 X0 x X1
       grind)
    | exact superpose eq646 eq646
    | exact resolve eq646 eq646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1063 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 x X0
       have i₂ := eq646 X0 x X1
       grind)
    | exact superpose eq646 eq14
    | exact resolve eq14 eq646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1076 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X2)) = (M.op X0 (M.op (M.op X0 (M.op X0 X1)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 X2 (M.op X0 X2)
       have i₂ := eq646 X0 X1 (M.op X0 X2)
       grind)
    | exact superpose eq646 eq53
    | exact resolve eq53 eq646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646
  have eq1087 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1076 X0 X2 X1
       have i₂ := eq53 X0 X2 X0
       grind)
    | exact superpose eq53 eq1076
    | exact resolve eq1076 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1076
  have eq1101 : x = (M.op (M.op (M.op x y) y) x) := by
    first
    | (have i₁ := eq1063 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1063
    | (have j0 := eq1063 x y
       grind)
    | exact resolve eq1063 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1103 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) := by
    first
    | exact superpose eq26 eq1063
    | (have j0 := eq1063 (σ x) (σ y)
       grind)
    | exact resolve eq1063 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1108 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1063 (M.op X0 X0) X0
       have i₂ := eq1063 X0 X0
       grind)
    | exact superpose eq1063 eq1063
    | exact resolve eq1063 eq1063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1134 : ∀ X0 : G, (M.op (M.op (M.op x y) y) x) = (M.op (M.op (M.op x y) y) (M.op (M.op (M.op (M.op x y) y) x) X0)) := by
    intro X0
    first
    | exact superpose eq1101 eq53
    | exact resolve eq53 eq1101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1142 : ∀ X0 : G, x = (M.op (M.op (M.op x y) y) (M.op x X0)) := by
    intro X0
    first
    | exact superpose eq1101 eq1134
    | exact resolve eq1134 eq1101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1134
  have eq1149 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) X0) X0) := by
    intro X0
    first
    | exact superpose eq1103 eq14
    | exact resolve eq14 eq1103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1151 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) X0)) := by
    intro X0
    first
    | exact superpose eq1103 eq53
    | exact resolve eq53 eq1103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1159 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq1103 eq1151
    | exact resolve eq1151 eq1103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1151
  have eq1161 : ∀ X0 : G, (M.op (M.op (σ x) X0) X0) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq1103 eq1149
    | exact resolve eq1149 eq1103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1149
  have eq1244 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1108 (σ X0)
       have i₂ := eq72 X0
       grind)
    | exact superpose eq72 eq1108
    | exact resolve eq1108 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1250 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0 X0 x
       have i₂ := eq1108 X0
       grind)
    | exact superpose eq1108 eq53
    | exact resolve eq53 eq1108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1251 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X0 X1
       have i₂ := eq1108 X0
       grind)
    | exact superpose eq1108 eq14
    | exact resolve eq14 eq1108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1559 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ (M.op X0 X0)) X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1251 (σ X0) X1
       have i₂ := eq72 X0
       grind)
    | exact superpose eq72 eq1251
    | exact resolve eq1251 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1817 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X1) X1) X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1048 (M.op (M.op X0 X1) X1) X0 X2
       have i₂ := eq1063 X0 X1
       grind)
    | exact superpose eq1063 eq1048
    | exact resolve eq1048 eq1063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1823 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) y) X0) X0) := by
    intro X0
    first
    | exact superpose eq1101 eq1048
    | exact resolve eq1048 eq1101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1828 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) X0) := by
    intro X0
    first
    | exact superpose eq1103 eq1048
    | exact resolve eq1048 eq1103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2074 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq1087 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1087
    | (have j0 := eq1087 x y X0
       grind)
    | exact resolve eq1087 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2078 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq1087
    | (have j0 := eq1087 (σ x) (σ y) X0
       grind)
    | exact resolve eq1087 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2082 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1087 X0 X0 X1
       have i₂ := eq1108 X0
       grind)
    | exact superpose eq1108 eq1087
    | exact resolve eq1087 eq1108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1087
  have eq2224 : (M.op x (M.op x y)) = (M.op x x) := by
    first
    | (have i₁ := eq2074 x
       have i₂ := eq1108 x
       grind)
    | exact superpose eq1108 eq2074
    | exact resolve eq2074 eq1108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2074
  have eq2263 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (M.op (M.op x y) x) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq2224 eq12
    | (have j0 := eq12 x x
       grind)
    | (have r₁ := eq12 (M.op x y) x
       have r₂ := eq2224
       grind)
    | exact resolve eq12 eq2224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2224
  have eq2275 : (M.op x x) = (M.op (M.op x y) x) ∨ x = (k (M.op x y) x) := by grind
  clear eq2263
  have eq2341 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2078 sF2
       have i₂ := eq1108 sF2
       grind)
    | exact superpose eq1108 eq2078
    | exact resolve eq2078 eq1108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1108 eq2078
  have eq2380 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq2341 eq12
    | (have j0 := eq12 (σ x) (σ x)
       grind)
    | (have r₁ := eq12 (M.op (σ x) (σ y)) (σ x)
       have r₂ := eq2341
       grind)
    | exact resolve eq12 eq2341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2341
  have eq2392 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (k (M.op (σ x) (σ y)) (σ x)) := by grind
  clear eq2380
  have eq2531 : (M.op (M.op (M.op x y) y) x) = (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) := by
    first
    | exact superpose eq1142 eq2082
    | exact resolve eq2082 eq1142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1142
  have eq2536 : (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq1159 eq2082
    | exact resolve eq2082 eq1159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1159
  have eq2617 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq1103 eq2536
    | exact resolve eq2536 eq1103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1103 eq2536
  have eq2621 : x = (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) := by
    first
    | exact superpose eq1101 eq2531
    | exact resolve eq2531 eq1101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1101 eq2531
  have eq4966 : ∀ X0 X2 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X0) (M.op (M.op X0 X0) X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq404 X0 x X2
       have i₂ := eq2082 X0 x
       grind)
    | exact superpose eq2082 eq404
    | exact resolve eq404 eq2082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404
  have eq4967 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq4966 X0 x
       have i₂ := eq2082 (M.op X0 X0) x
       grind)
    | exact superpose eq2082 eq4966
    | exact resolve eq4966 eq2082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2082 eq4966
  have eq5065 : ∀ X0 : G, (σ (M.op (M.op x y) y)) = (M.op (M.op (σ x) X0) X0) := by
    intro X0
    first
    | exact superpose eq2621 eq1559
    | exact resolve eq1559 eq2621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1559 eq2621
  have eq5143 : ∀ X0 : G, (σ (M.op (M.op x y) y)) = (M.op (M.op (σ x) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq5065 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5065
    | (have j0 := eq5065 X0
       grind)
    | exact resolve eq5065 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5065
  have eq5156 : (σ (M.op (M.op x y) y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq1161 eq5143
    | (have j0 := eq5143 (σ y)
       grind)
    | exact resolve eq5143 eq1161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1161 eq5143
  have eq8000 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq878 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq878
    | (have j0 := eq878 x
       grind)
    | exact resolve eq878 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq878
  have eq8033 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq8000
       have i₂ := eq99
       grind)
    | exact superpose eq99 eq8000
    | exact resolve eq8000 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8000
  have eq8057 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | exact superpose eq26 eq8033
    | exact resolve eq8033 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8033
  have eq8067 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | exact superpose eq26 eq8057
    | exact resolve eq8057 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8057
  have eq8075 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq8067
       have i₂ := eq71
       grind)
    | exact superpose eq71 eq8067
    | exact resolve eq8067 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8067
  have eq8081 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq8075
    | exact resolve eq8075 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8075
  have eq19347 : ∀ X0 : G, (σ X0) = (M.op (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1063 (σ X0) (σ (M.op X0 X0))
       have i₂ := eq1244 X0
       grind)
    | exact superpose eq1244 eq1063
    | exact resolve eq1063 eq1244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1244
  have eq19365 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op (M.op X0 X0) (M.op X0 X0))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq19347 X0
       have i₂ := eq72 (M.op X0 X0)
       grind)
    | exact superpose eq72 eq19347
    | exact resolve eq19347 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq19347
  have eq19417 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op (M.op X0 X0) X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq19365 X0
       have i₂ := eq4967 X0
       grind)
    | exact superpose eq4967 eq19365
    | exact resolve eq19365 eq4967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4967 eq19365
  have eq21880 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op (M.op X0 X1) X1)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq19417 X0
       have i₂ := eq1048 X0 X0 X1
       grind)
    | (have i₁ := eq19417 X0
       have i₂ := eq1048 X0 X1 X0
       grind)
    | exact superpose eq1048 eq19417
    | exact resolve eq19417 eq1048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1048 eq19417
  have eq30939 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) y) := by
    first
    | exact superpose eq1823 eq1817
    | exact resolve eq1817 eq1823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30941 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    first
    | exact superpose eq1828 eq1817
    | exact resolve eq1817 eq1828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31561 : x = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq1251 x y
       have i₂ := eq30939
       grind)
    | exact superpose eq30939 eq1251
    | exact resolve eq1251 eq30939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31887 : (M.op (M.op x y) x) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq31561 eq1250
    | exact resolve eq1250 eq31561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32237 : x = (M.op (M.op (M.op x y) x) y) := by
    first
    | exact superpose eq31887 eq31561
    | exact resolve eq31561 eq31887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31561
  have eq32246 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op (M.op x y) x) X0) X0) := by
    intro X0
    first
    | exact superpose eq31887 eq1251
    | exact resolve eq1251 eq31887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32317 : x = (M.op (M.op x x) y) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq2275 eq32237
    | exact resolve eq32237 eq2275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2275 eq32237
  have eq32354 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) x) := by
    first
    | (have i₁ := eq32317
       have i₂ := eq30939
       grind)
    | exact superpose eq30939 eq32317
    | exact resolve eq32317 eq30939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30939 eq32317
  have eq32357 : x = (k (M.op x y) x) ∨ x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq31887 eq32354
    | exact resolve eq32354 eq31887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31887 eq32354
  have eq32727 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq30941 eq1251
    | exact resolve eq1251 eq30941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32779 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq32727 eq1250
    | exact resolve eq1250 eq32727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1250
  have eq33124 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) := by
    first
    | exact superpose eq32779 eq32727
    | exact resolve eq32727 eq32779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32727
  have eq33133 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0) X0) := by
    intro X0
    first
    | exact superpose eq32779 eq1251
    | exact resolve eq1251 eq32779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33463 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ (σ x) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq2392 eq33124
    | exact resolve eq33124 eq2392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2392
  have eq33500 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq30941 eq33463
    | exact resolve eq33463 eq30941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30941 eq33463
  have eq33502 : (σ x) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq32779 eq33500
    | exact resolve eq33500 eq32779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32779 eq33500
  have eq35152 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq117 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35153 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq35152
    | exact resolve eq35152 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35152
  have eq35164 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq35153
       have r₂ := eq27
       grind)
    | exact resolve eq35153 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35153
  have eq35168 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq35164
    | exact resolve eq35164 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35164
  have eq35172 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq35168
    | exact resolve eq35168 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35168
  have eq35190 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0) X0) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    intro X0
    first
    | exact superpose eq35172 eq1817
    | exact resolve eq1817 eq35172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35172
  have eq35199 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq33133 eq35190
    | exact resolve eq35190 eq33133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33133 eq35190
  have eq36236 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) X0) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    intro X0
    first
    | exact superpose eq35199 eq1817
    | exact resolve eq1817 eq35199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35199
  have eq36249 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq1828 eq36236
    | exact resolve eq36236 eq1828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1828 eq36236
  have eq36250 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq36249
  have eq36272 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq36250 eq77
    | (have r₁ := eq77
       have r₂ := eq36250
       grind)
    | exact resolve eq77 eq36250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq36250
  have eq36373 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq36272
  have eq46305 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq36373 eq1063
    | exact resolve eq1063 eq36373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36373
  have eq46322 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq33124 eq46305
    | exact resolve eq46305 eq33124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46305
  have eq46637 : (τ (σ x)) = (k y x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq46322 eq113
    | exact resolve eq113 eq46322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq46638 : (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq46322 eq117
    | exact resolve eq117 eq46322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq46322
  have eq46647 : (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq46638
  have eq46656 : x = (k y x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq28 eq46637
    | exact resolve eq46637 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46637
  have eq46663 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have r₁ := eq46656
       have r₂ := eq76
       grind)
    | exact resolve eq46656 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq46656
  have eq46681 : ∀ X0 : G, (M.op y y) = (M.op (M.op (M.op (M.op x y) x) X0) X0) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    intro X0
    first
    | (have i₁ := eq1817 y x X0
       have i₂ := eq46663
       grind)
    | exact superpose eq46663 eq1817
    | exact resolve eq1817 eq46663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46663
  have eq46690 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | exact superpose eq32246 eq46681
    | exact resolve eq46681 eq32246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46681
  have eq47139 : (σ y) = (M.op (σ (M.op (M.op x y) y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq21880 y y
       have i₂ := eq46690
       grind)
    | exact superpose eq46690 eq21880
    | exact resolve eq21880 eq46690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21880 eq46690
  have eq47143 : (σ y) = (M.op (σ (M.op (M.op x y) y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq47139
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq47139
    | exact resolve eq47139 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47139
  have eq47171 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | exact superpose eq5156 eq47143
    | exact resolve eq47143 eq5156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5156 eq47143
  have eq53085 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) = (M.op (M.op (M.op (σ y) (σ y)) X0) X0) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    intro X0
    first
    | exact superpose eq47171 eq1817
    | exact resolve eq1817 eq47171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47171
  have eq53100 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq53085 x
       have i₂ := eq1251 sF3 x
       grind)
    | exact superpose eq1251 eq53085
    | exact resolve eq53085 eq1251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1251 eq53085
  have eq53116 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | exact superpose eq2617 eq53100
    | exact resolve eq53100 eq2617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2617 eq53100
  have eq53117 : x = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq53116
  have eq53434 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq99
       have i₂ := eq53117
       grind)
    | exact superpose eq53117 eq99
    | exact resolve eq99 eq53117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq53117
  have eq53456 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq53434
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq53434
    | exact resolve eq53434 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53434
  have eq53465 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq8081 eq53456
    | exact resolve eq53456 eq8081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8081 eq53456
  have eq87530 : ∀ X0 : G, (M.op y y) = (M.op (M.op (M.op (M.op x y) x) X0) X0) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq1817 y x X0
       have i₂ := eq46647
       grind)
    | exact superpose eq46647 eq1817
    | exact resolve eq1817 eq46647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46647
  have eq87539 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq32246 eq87530
    | exact resolve eq87530 eq32246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32246 eq87530
  have eq88771 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op (M.op x y) y) X0) X0) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq1817 y y x
       have i₂ := eq87539
       grind)
    | exact superpose eq87539 eq1817
    | exact resolve eq1817 eq87539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1817 eq87539
  have eq88784 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1823 eq88771
    | exact resolve eq88771 eq1823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1823 eq88771
  have eq88785 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq88784
  have eq88829 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq71
       have i₂ := eq88785
       grind)
    | exact superpose eq88785 eq71
    | exact resolve eq71 eq88785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88785
  have eq88987 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq88829
    | exact resolve eq88829 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88829
  have eq169992 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq53465 eq1063
    | exact resolve eq1063 eq53465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1063 eq53465
  have eq170015 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq33124 eq169992
    | exact resolve eq169992 eq33124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33124 eq169992
  have eq170016 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq170015
  have eq170076 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq170016 eq88987
    | exact resolve eq88987 eq170016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq170214 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq170076
  have eq170267 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq170214
       have r₂ := eq27
       grind)
    | exact resolve eq170214 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170214
  have eq170332 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq170267 eq33502
    | exact resolve eq33502 eq170267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33502 eq170267
  have eq170567 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq170332
       have i₂ := eq65 sF2
       grind)
    | exact superpose eq65 eq170332
    | exact resolve eq170332 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170332
  have eq170568 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq170567
  have eq171233 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq170568 eq88987
    | exact resolve eq88987 eq170568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88987 eq170568
  have eq171380 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq171233
  have eq171493 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq171380 eq29
    | exact resolve eq29 eq171380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq171704 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq28 eq171493
    | exact resolve eq171493 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171493
  have eq171738 : x = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq171704 eq28
    | exact resolve eq28 eq171704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171704
  have eq172121 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq171738
    | exact resolve eq171738 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq171738
  have eq172365 : x = (k x x) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq172121 eq32357
    | exact resolve eq32357 eq172121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32357 eq172121
  have eq172472 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq172365
       have i₂ := eq65 x
       grind)
    | exact superpose eq65 eq172365
    | exact resolve eq172365 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq172365
  have eq172473 : x = (M.op x x) ∨ x = y := by grind
  clear eq172472
  have eq174636 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq71
       have i₂ := eq172473
       grind)
    | exact superpose eq172473 eq71
    | exact resolve eq71 eq172473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq172473
  have eq174879 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq174636
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq174636
    | exact resolve eq174636 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174636
  have eq181136 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq174879 eq170016
    | exact resolve eq170016 eq174879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170016 eq174879
  have eq181250 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq181136
  have eq194654 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq181250 eq27
    | exact resolve eq27 eq181250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181250
  have eq195034 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq194654
       have r₂ := eq171380
       grind)
    | exact resolve eq194654 eq171380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171380 eq194654
  have eq195086 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq195034 eq29
    | exact resolve eq29 eq195034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq195034
  have eq195297 : x = y ∨ x = y := by
    first
    | exact superpose eq28 eq195086
    | exact resolve eq195086 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq195086
  have eq195298 : x = y := by grind
  clear eq195297
  have eq195330 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq195298
       grind)
    | exact superpose eq195298 eq18
    | exact resolve eq18 eq195298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq195331 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq195298
       grind)
    | exact superpose eq195298 eq24
    | exact resolve eq24 eq195298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq195298
  have eq195802 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq195331
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq195331
    | exact resolve eq195331 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq195331
  have eq195870 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq195802 eq26
    | exact resolve eq26 eq195802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq195802
  have eq196406 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq195870 eq70
    | exact resolve eq70 eq195870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq195870
  have eq196629 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq196406
       have i₂ := eq195330
       grind)
    | exact superpose eq195330 eq196406
    | exact resolve eq196406 eq195330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195330 eq196406
  have eq196676 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq196629 eq15
    | exact resolve eq15 eq196629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196629
  have eq197093 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq196676
    | exact resolve eq196676 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq196676
  have eq197217 : False := by grind
  exact eq197217

/-- `Equation2865`: `x = ((x ◇ (y ◇ x)) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(Y,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pxy_x_pyx_x_pxy_Equation2865 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2865 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2865.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq62 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq62 (σ X0)
       grind)
    | exact superpose eq62 eq15
    | exact resolve eq15 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq65 X0
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq65
    | exact resolve eq65 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq65
  have eq87 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq245 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq258 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq245 X0 X1
       have i₂ := eq76 X1
       grind)
    | exact superpose eq76 eq245
    | (have j0 := eq245 X0 X1
       grind)
    | exact resolve eq245 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245
  have eq266 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq258 X0 X1
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq258
    | (have j0 := eq258 X0 X1
       grind)
    | exact resolve eq258 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258
  have eq422 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq266 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq266
    | (have j0 := eq266 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | exact resolve eq266 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq556 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq87 X1 (σ X0)
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq87
    | (have j0 := eq87 X1 (σ X0)
       grind)
    | (have r₁ := eq87 X0 (σ X0)
       have r₂ := eq76 X0
       grind)
    | exact resolve eq87 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq561 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq556 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq556
    | (have j0 := eq556 X0 X1
       grind)
    | exact resolve eq556 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556
  have eq17455 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq422 x y
       grind)
    | exact superpose eq422 eq16
    | (have j1 := eq422 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq422 x y
       grind)
    | exact resolve eq16 eq422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422
  have eq17483 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq17455
  have eq17606 : (M.op y y) = (τ (σ (M.op x x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq17483
       grind)
    | exact superpose eq17483 eq10
    | exact resolve eq10 eq17483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17483
  have eq17769 : (M.op x x) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq17606
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq17606
    | exact resolve eq17606 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17606
  have eq17770 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq17769
  have eq17772 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17770
       grind)
    | exact superpose eq17770 eq16
    | exact resolve eq16 eq17770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17777 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq17770
       grind)
    | exact superpose eq17770 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq17770
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq17770
       grind)
    | exact resolve eq13 eq17770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17770
  have eq17783 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq17777
  have eq17790 : (σ (M.op x x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17783
       have i₂ := eq76 x
       grind)
    | exact superpose eq76 eq17783
    | exact resolve eq17783 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17783
  have eq17791 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17790
       have i₂ := eq76 y
       grind)
    | exact superpose eq76 eq17790
    | exact resolve eq17790 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq17790
  have eq17792 : (σ x) = (σ (k x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17791
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq17791
    | exact resolve eq17791 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17791
  have eq17793 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14 eq17792
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq17792 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17792
  have eq17794 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq17793
       have r₂ := eq17772
       grind)
    | exact resolve eq17793 eq17772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17772 eq17793
  have eq17853 : (M.op y y) = (τ (σ (M.op x x))) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq17794
       grind)
    | exact superpose eq17794 eq10
    | exact resolve eq10 eq17794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17794
  have eq18016 : (M.op x x) = (M.op y y) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17853
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq17853
    | exact resolve eq17853 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17853
  have eq18017 : (M.op x x) = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq18016
  have eq18018 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (k y X0) = (M.op X0 y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq12 y X0
       have i₂ := eq18017
       grind)
    | exact superpose eq18017 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq18017
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq18017
       grind)
    | exact resolve eq12 eq18017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18043 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq561 y X0
       have i₂ := eq18017
       grind)
    | exact superpose eq18017 eq561
    | (have j0 := eq561 X0 x
       grind)
    | exact resolve eq561 eq18017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18017
  have eq18178 : (M.op x y) = (k y x) ∨ x = (M.op x y) := by
    first
    | (have j0 := eq18018 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18018
  have eq18625 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have j0 := eq18043 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18043
  have eq18628 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18178 eq18625
    | exact resolve eq18625 eq18178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18178 eq18625
  have eq18637 : x = (M.op x y) := by
    first
    | (have r₁ := eq18628
       have r₂ := eq16
       grind)
    | exact resolve eq18628 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18628
  have eq18642 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq18637
       grind)
    | exact superpose eq18637 eq16
    | exact resolve eq16 eq18637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18644 : x ≠ x ∨ (M.op x x) = (M.op y y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq18637
       grind)
    | exact superpose eq18637 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq18637
       grind)
    | exact resolve eq13 eq18637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18651 : (M.op x x) = (M.op y y) ∨ x = (k x y) := by grind
  clear eq18644
  have eq18661 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (k y X0) = (M.op X0 y) ∨ x = (k x y) := by
    intro X0
    first
    | (have i₁ := eq12 y X0
       have i₂ := eq18651
       grind)
    | exact superpose eq18651 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq18651
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq18651
       grind)
    | exact resolve eq12 eq18651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18687 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ x = (k x y) := by
    intro X0
    first
    | (have i₁ := eq561 y X0
       have i₂ := eq18651
       grind)
    | exact superpose eq18651 eq561
    | (have j0 := eq561 X0 x
       grind)
    | exact resolve eq561 eq18651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18651
  have eq18865 : (M.op x y) = (k y x) ∨ x = (k x y) := by
    first
    | (have j0 := eq18661 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18661
  have eq18868 : x = (k y x) ∨ x = (k x y) := by
    first
    | (have i₁ := eq18865
       have i₂ := eq18637
       grind)
    | exact superpose eq18637 eq18865
    | exact resolve eq18865 eq18637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18865
  have eq19238 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = (k x y) := by
    first
    | (have j0 := eq18687 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18687
  have eq19241 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x y) := by
    first
    | exact superpose eq18868 eq19238
    | exact resolve eq19238 eq18868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18868 eq19238
  have eq19250 : x = (k x y) := by
    first
    | (have r₁ := eq19241
       have r₂ := eq18642
       grind)
    | exact resolve eq19241 eq18642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19241
  have eq19259 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq266 x y
       have i₂ := eq19250
       grind)
    | exact superpose eq19250 eq266
    | (have j0 := eq266 x y
       grind)
    | exact resolve eq266 eq19250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266 eq19250
  have eq19262 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq19259
  have eq19267 : (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq19262
       have r₂ := eq18642
       grind)
    | exact resolve eq19262 eq18642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19262
  have eq19277 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (σ (k y X0)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq561 y X0
       have i₂ := eq19267
       grind)
    | exact superpose eq19267 eq561
    | (have j0 := eq561 X0 x
       grind)
    | (have r₁ := eq561 x y
       have r₂ := eq19267
       grind)
    | (have r₁ := eq561 y x
       have r₂ := eq19267
       grind)
    | exact resolve eq561 eq19267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561
  have eq19327 : (M.op y y) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq19267
       grind)
    | exact superpose eq19267 eq10
    | exact resolve eq10 eq19267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19267
  have eq19490 : (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq19327
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq19327
    | exact resolve eq19327 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19327
  have eq19494 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (k y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq12 y X0
       have i₂ := eq19490
       grind)
    | exact superpose eq19490 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq19490
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq19490
       grind)
    | exact resolve eq12 eq19490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19490
  have eq19680 : (M.op x y) = (k y x) := by
    first
    | (have j0 := eq19494 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19494
  have eq19682 : x = (k y x) := by
    first
    | (have i₁ := eq19680
       have i₂ := eq18637
       grind)
    | exact superpose eq18637 eq19680
    | exact resolve eq19680 eq18637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18637 eq19680
  have eq20035 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have j0 := eq19277 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19277
  have eq20037 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20035
       have i₂ := eq19682
       grind)
    | exact superpose eq19682 eq20035
    | exact resolve eq20035 eq19682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19682 eq20035
  have eq20046 : False := by grind
  exact eq20046
