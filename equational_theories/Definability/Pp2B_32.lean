import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxy_pxx_pxy_Equation2712 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
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
  have eq25 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
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
  have eq29 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq25 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25
    | exact resolve eq25 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq30 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq29
  have eq45 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq527 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (σ X0) = X1 ∨ (σ (M.op X0 X0)) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq13
    | (have j0 := eq13 (σ X0) X1
       grind)
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1847 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) ∨ (τ X1) = X0 := by
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
  have eq1850 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq1873 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1850 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq1850
    | (have j0 := eq1850 X0 X1
       grind)
    | exact resolve eq1850 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1850
  have eq1955 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1873 x y
       grind)
    | exact superpose eq1873 eq16
    | (have j1 := eq1873 x y
       grind)
    | exact resolve eq16 eq1873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1978 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq1873 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1873
  have eq25361 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1847 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1847
    | exact resolve eq1847 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1847
  have eq25676 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq25361 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq25361
    | (have j0 := eq25361 X0 X1
       grind)
    | exact resolve eq25361 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25361
  have eq73623 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq1955
       have i₂ := eq25676 y x
       grind)
    | exact superpose eq25676 eq1955
    | (have j1 := eq25676 y x
       grind)
    | (have r₁ := eq1955
       have r₂ := eq25676 y x
       grind)
    | (have r₁ := eq1955
       have r₂ := eq25676 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq1955
       have r₂ := eq25676 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq1955 eq25676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1955 eq25676
  have eq73624 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq73623
  have eq81886 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1978 (τ X0) (τ X1)
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq1978
    | (have j0 := eq1978 (τ X0) (τ X1)
       grind)
    | exact resolve eq1978 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq82006 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq81886 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq81886
    | (have j0 := eq81886 X0 X1
       grind)
    | exact resolve eq81886 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81886
  have eq82053 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq82006 X0 X1
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq82006
    | (have j0 := eq82006 X0 X1
       grind)
    | exact resolve eq82006 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82006
  have eq82096 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq82053 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq82053
    | (have j0 := eq82053 X0 X1
       grind)
    | exact resolve eq82053 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82053
  have eq82131 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq82096 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq82096
    | (have j0 := eq82096 X0 X1
       grind)
    | exact resolve eq82096 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82096
  have eq82157 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq82131 X0 X1
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq82131
    | (have j0 := eq82131 X0 X1
       grind)
    | exact resolve eq82131 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq82131
  have eq82177 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) ≠ (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq82157 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq82157
    | (have j0 := eq82157 X0 X1
       grind)
    | exact resolve eq82157 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82157
  have eq82191 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq82177 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq82177
    | (have j0 := eq82177 X0 X1
       grind)
    | exact resolve eq82177 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82177
  have eq345705 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq73624
       grind)
    | exact superpose eq73624 eq16
    | exact resolve eq16 eq73624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73624
  have eq345706 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq345705
       have r₂ := eq22 x
       grind)
    | exact resolve eq345705 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345705
  have eq345709 : (M.op x x) ≠ (M.op x x) ∨ x = y ∨ (k x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq345706
       grind)
    | exact superpose eq345706 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq345706
       grind)
    | exact resolve eq13 eq345706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345706
  have eq345811 : x = y ∨ (k x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq345709
  have eq426965 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq345811
       grind)
    | exact superpose eq345811 eq16
    | exact resolve eq16 eq345811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345811
  have eq426966 : (k x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq426965
       have r₂ := eq22 x
       grind)
    | exact resolve eq426965 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426965
  have eq426976 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq1978 x y
       have i₂ := eq426966
       grind)
    | exact superpose eq426966 eq1978
    | (have j0 := eq1978 x y
       grind)
    | exact resolve eq1978 eq426966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1978 eq426966
  have eq427017 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by grind
  clear eq426976
  have eq427018 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by grind
  clear eq427017
  have eq427029 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq427018
       grind)
    | exact superpose eq427018 eq16
    | exact resolve eq16 eq427018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq427039 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq527 x (σ y)
       have i₂ := eq427018
       grind)
    | exact superpose eq427018 eq527
    | (have j0 := eq527 x (σ y)
       grind)
    | (have r₁ := eq527 x (σ y)
       have r₂ := eq427018
       grind)
    | exact resolve eq527 eq427018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527 eq427018
  have eq427236 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) := by grind
  clear eq427039
  have eq427237 : (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) := by grind
  clear eq427236
  have eq427313 : (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq427237
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq427237
    | exact resolve eq427237 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427237
  have eq427366 : y = (τ (σ x)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq427313
       grind)
    | exact superpose eq427313 eq10
    | exact resolve eq10 eq427313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427313
  have eq427738 : x = y ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq427366
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq427366
    | exact resolve eq427366 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427366
  have eq427740 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq427738
       grind)
    | exact superpose eq427738 eq16
    | exact resolve eq16 eq427738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427738
  have eq427741 : (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq427740
       have r₂ := eq22 x
       grind)
    | exact resolve eq427740 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427740
  have eq427760 : (k x y) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq427741
       grind)
    | exact superpose eq427741 eq10
    | exact resolve eq10 eq427741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427741
  have eq428136 : (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq427760
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq427760
    | exact resolve eq427760 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427760
  have eq428170 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq82191 x y
       have i₂ := eq428136
       grind)
    | exact superpose eq428136 eq82191
    | (have j0 := eq82191 x y
       grind)
    | (have r₁ := eq82191 x y
       have r₂ := eq428136
       grind)
    | exact resolve eq82191 eq428136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82191 eq428136
  have eq428190 : x = y ∨ (M.op x y) = (M.op x x) := by grind
  clear eq428170
  have eq428194 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq428190
       grind)
    | exact superpose eq428190 eq16
    | exact resolve eq16 eq428190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428190
  have eq428197 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq428194
       have r₂ := eq22 x
       grind)
    | exact resolve eq428194 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428194
  have eq428198 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq427029
       have i₂ := eq428197
       grind)
    | exact superpose eq428197 eq427029
    | exact resolve eq427029 eq428197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427029
  have eq428340 : (σ x) = (σ y) := by grind
  clear eq428198
  have eq428358 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq428340
       grind)
    | exact superpose eq428340 eq16
    | exact resolve eq16 eq428340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428340
  have eq428735 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq428358
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq428358
    | exact resolve eq428358 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq428358
  have eq428737 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq428735
       have i₂ := eq428197
       grind)
    | exact superpose eq428197 eq428735
    | exact resolve eq428735 eq428197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428197 eq428735
  have eq428738 : False := by grind
  exact eq428738

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxx_y_pyx_Equation2712 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  clear eq36
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq53 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y x X0
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : y ≠ (M.op x y) ∨ x = y ∨ x = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  clear eq37
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq90
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq90
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq90 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq90
       grind)
    | exact superpose eq90 eq16
    | exact resolve eq16 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq97
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq97
    | exact resolve eq97 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq21 eq103
    | exact resolve eq103 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq105 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq104
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq104
    | exact resolve eq104 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq120 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq123 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq120
  have eq124 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by grind
  clear eq123
  have eq163 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq124 eq16
    | exact resolve eq16 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq214 : y = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq53 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq53
    | (have j0 := eq53 y
       grind)
    | exact resolve eq53 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq223 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq27 eq54
    | (have j0 := eq54 (σ y)
       grind)
    | exact resolve eq54 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq234 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op x X0) (M.op x y)) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq255 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq35
  have eq266 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq255 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq255
    | exact resolve eq255 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq267 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq266
  have eq587 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq267 X0
       grind)
    | exact superpose eq267 eq16
    | exact resolve eq16 eq267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq710 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq55 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq774 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op (M.op (M.op (M.op x X0) (M.op x y)) X1) X0) X2) X1) X2) = X2 := by
    intro X0 X1 X2
    first
    | exact superpose eq56 eq58
    | exact resolve eq58 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq823 : ∀ X0 : G, (τ X0) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq710 (τ X0)
       have i₂ := eq587 X0
       grind)
    | exact superpose eq587 eq710
    | exact resolve eq710 eq587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587
  have eq989 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq105 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq990 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq989
    | exact resolve eq989 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq989
  have eq993 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq990
       have r₂ := eq28
       grind)
    | exact resolve eq990 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq990
  have eq995 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq993
    | exact resolve eq993 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq993
  have eq1000 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq995 eq72
    | (have r₁ := eq72
       have r₂ := eq995
       grind)
    | exact resolve eq72 eq995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq995
  have eq1003 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq1000
  have eq1004 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq1003
  have eq1053 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1004 eq105
    | exact resolve eq105 eq1004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq1054 : (τ (σ x)) = (k y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1004 eq102
    | exact resolve eq102 eq1004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq1004
  have eq1057 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1053
  have eq1061 : x = (k y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq1054
    | exact resolve eq1054 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1054
  have eq1064 : x = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1061
       have r₂ := eq71
       grind)
    | exact resolve eq1061 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq1061
  have eq1081 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq90
       have i₂ := eq1064
       grind)
    | exact superpose eq1064 eq90
    | exact resolve eq90 eq1064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq1064
  have eq1086 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1081
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1081
    | exact resolve eq1081 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1081
  have eq1094 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1086 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq1086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1086
  have eq1095 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1094
  have eq1099 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq1095
    | exact resolve eq1095 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1095
  have eq1102 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq1099
    | exact resolve eq1099 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1099
  have eq1105 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1057 eq30
    | exact resolve eq30 eq1057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1057
  have eq1126 : x = y ∨ y = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq29 eq1105
    | exact resolve eq1105 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1105
  have eq1127 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq1126
  have eq1145 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1127 eq29
    | exact resolve eq29 eq1127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1152 : (M.op x x) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1127 eq70
    | exact resolve eq70 eq1127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1127
  have eq1163 : (M.op x x) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq163 eq1152
    | exact resolve eq1152 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1152
  have eq1168 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq1145
    | exact resolve eq1145 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1145
  have eq1171 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1168 eq21
    | exact resolve eq21 eq1168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1168
  have eq1198 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1171
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1171
    | exact resolve eq1171 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1171
  have eq1202 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1198 eq27
    | exact resolve eq27 eq1198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1406 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1102 eq28
    | exact resolve eq28 eq1102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1102
  have eq1435 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1198 eq1406
    | (have r₁ := eq1406
       have r₂ := eq1198
       grind)
    | exact resolve eq1406 eq1198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1406
  have eq1436 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq1435
  have eq1437 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq1436
  have eq1444 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq1437 eq223
    | exact resolve eq223 eq1437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq1536 : y = (M.op (M.op x x) y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1163 eq214
    | exact resolve eq214 eq1163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq1537 : (σ (M.op x x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1163 eq124
    | exact resolve eq124 eq1163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq1550 : (M.op x y) = (M.op (M.op x x) (M.op x y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1163 eq710
    | exact resolve eq710 eq1163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710 eq1163
  have eq1553 : (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1537
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq1537
    | exact resolve eq1537 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq1537
  have eq1746 : ∀ X0 : G, (M.op (M.op (M.op (M.op x y) X0) x) X0) = X0 ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1550 eq234
    | exact resolve eq234 eq1550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234 eq1550
  have eq1787 : (τ (σ x)) = (M.op (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) (τ (σ x))) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1553 eq823
    | exact resolve eq823 eq1553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq823 eq1553
  have eq1790 : x = (M.op (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq1787
    | exact resolve eq1787 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1787
  have eq1792 : x = (M.op (M.op (M.op x y) (M.op x y)) x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq163 eq1790
    | exact resolve eq1790 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163 eq1790
  have eq5064 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op x X0) (M.op x y)) X0) X1) = (M.op X0 (M.op (M.op (M.op (M.op x X0) (M.op x y)) X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq774 X0 X0 (M.op (M.op (M.op (M.op x X0) sF0) X0) x)
       have i₂ := eq14 X0 (M.op (M.op (M.op x X0) sF0) X0) x
       grind)
    | exact superpose eq14 eq774
    | exact resolve eq774 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq774
  have eq5076 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | exact superpose eq56 eq5064
    | exact resolve eq5064 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq5064
  have eq5701 : (M.op x y) = (M.op x (M.op x y)) ∨ y = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1792 eq1746
    | exact resolve eq1746 eq1792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1746 eq1792
  have eq5713 : (M.op x y) = (M.op x (M.op x y)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq5701
  have eq28855 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1202 eq5076
    | (have j0 := eq5076 (σ x) (σ y)
       grind)
    | exact resolve eq5076 eq1202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1202 eq5076
  have eq29169 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq1437 eq28855
    | exact resolve eq28855 eq1437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1437 eq28855
  have eq29246 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq29169
  have eq31575 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq29246 eq1444
    | exact resolve eq1444 eq29246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1444 eq29246
  have eq31632 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq31575
  have eq31633 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq31632
    | exact resolve eq31632 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31632
  have eq31635 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq31633 eq28
    | exact resolve eq28 eq31633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31633
  have eq31694 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq31635
       have r₂ := eq1198
       grind)
    | exact resolve eq31635 eq1198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1198 eq31635
  have eq31696 : x = (τ (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq31694 eq29
    | exact resolve eq29 eq31694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq31694
  have eq31822 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq31696
    | exact resolve eq31696 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq31696
  have eq31823 : x = (M.op x y) ∨ x = y := by grind
  clear eq31822
  have eq31880 : x = (M.op x x) ∨ x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq31823 eq5713
    | exact resolve eq5713 eq31823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5713
  have eq31913 : x = (M.op x x) ∨ x = y := by grind
  clear eq31880
  have eq32093 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq1536
       have i₂ := eq31913
       grind)
    | exact superpose eq31913 eq1536
    | exact resolve eq1536 eq31913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1536 eq31913
  have eq32187 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq32093
  have eq32220 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq32187
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq32187
    | exact resolve eq32187 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32187
  have eq32221 : y = (M.op x y) ∨ x = y := by grind
  clear eq32220
  have eq32304 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq32221 eq31823
    | exact resolve eq31823 eq32221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31823 eq32221
  have eq32305 : x = y := by grind
  clear eq32304
  have eq32352 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq32305
       grind)
    | exact superpose eq32305 eq19
    | exact resolve eq19 eq32305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq32353 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq32305
       grind)
    | exact superpose eq32305 eq25
    | exact resolve eq25 eq32305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq32305
  have eq32391 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq32353
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq32353
    | exact resolve eq32353 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq32353
  have eq32395 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq32391 eq27
    | exact resolve eq27 eq32391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq32391
  have eq32631 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq32395 eq70
    | exact resolve eq70 eq32395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq32395
  have eq32728 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq32631
       have i₂ := eq32352
       grind)
    | exact superpose eq32352 eq32631
    | exact resolve eq32631 eq32352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32352 eq32631
  have eq32736 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32728 eq15
    | exact resolve eq15 eq32728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32728
  have eq32784 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq32736
    | exact resolve eq32736 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq32736
  have eq32793 : False := by grind
  exact eq32793

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then X else if m(Y,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_x_x_pxy_pyx_Equation2712 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : (M.op x y) = (M.op x y) := by grind
  have eq20 : (M.op x y) = (M.op x y) := by grind
  clear eq19
  have eq21 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq22 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq21
  have eq23 : (σ x) = (σ x) := by grind
  have eq24 : (σ x) = (σ x) := by grind
  clear eq23
  have eq25 : (σ y) = (σ y) := by grind
  have eq26 : (σ y) = (σ y) := by grind
  clear eq25
  have eq27 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq28 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq27
  have eq29 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq30 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq16
    | (have j0 := eq16 y
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq22 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq38 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq10
    | (have j0 := eq10 y X0
       grind)
    | exact resolve eq10 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq22 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq41 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 X0 x
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq14
    | (have j0 := eq14 y x X0
       grind)
    | exact resolve eq14 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq28 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq28 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq38 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq38
    | (have j0 := eq38 x
       grind)
    | exact resolve eq38 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq86 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq79
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq79
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq79 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq86
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq86
    | exact resolve eq86 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq22 eq92
    | exact resolve eq92 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq110 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq39
    | (have j0 := eq39 x
       grind)
    | exact resolve eq39 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq177 : y = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq52 y
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq52
    | (have j0 := eq52 y
       grind)
    | exact resolve eq52 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq182 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq28 eq53
    | (have j0 := eq53 (σ y)
       grind)
    | exact resolve eq53 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq248 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq36 X1 X0
       have i₂ := eq11 (τ X1) X0
       grind)
    | exact superpose eq11 eq36
    | (have j1 := eq11 (τ X1) X0
       grind)
    | exact resolve eq36 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq251 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k (τ X0) X1)
       have i₂ := eq36 X0 X1
       grind)
    | exact superpose eq36 eq16
    | exact resolve eq16 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq295 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    grind
  clear eq40
  have eq373 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq54 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq376 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X1)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq54 X1 X0 X1 (M.op X0 X1)
       have i₂ := eq373 (M.op X0 X1)
       grind)
    | exact superpose eq373 eq54
    | exact resolve eq54 eq373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq379 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq373 X0
       grind)
    | exact superpose eq373 eq14
    | exact resolve eq14 eq373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq399 : y = (M.op (M.op y (M.op x y)) y) := by
    first
    | (have i₁ := eq376 x y
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq376
    | (have j0 := eq376 x y
       grind)
    | exact resolve eq376 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376
  have eq451 : ∀ X0 : G, y = (M.op (M.op y (M.op (M.op y (M.op x y)) X0)) y) := by
    intro X0
    first
    | exact superpose eq399 eq14
    | exact resolve eq14 eq399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399
  have eq775 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq379 X0 (M.op X0 X1)
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq379
    | exact resolve eq379 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq778 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq55 eq379
    | exact resolve eq379 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq781 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq56 eq379
    | exact resolve eq379 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379
  have eq4857 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq93 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4858 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq28 eq4857
    | exact resolve eq4857 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4857
  have eq4869 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq4858
       have r₂ := eq29
       grind)
    | exact resolve eq4858 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4858
  have eq4895 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq4869 eq775
    | exact resolve eq775 eq4869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4898 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq4869 eq373
    | exact resolve eq373 eq4869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4899 : (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by grind
  clear eq4869
  have eq4900 : (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by grind
  clear eq4899
  have eq4901 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq28 eq4895
    | exact resolve eq4895 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4895
  have eq5016 : x = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq373 x
       have i₂ := eq4901
       grind)
    | exact superpose eq4901 eq373
    | exact resolve eq373 eq4901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5017 : (M.op y x) = (k y x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq4901
  have eq5018 : (M.op y x) = (k y x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq5017
  have eq5431 : (σ (M.op y x)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq79
       have i₂ := eq5018
       grind)
    | exact superpose eq5018 eq79
    | exact resolve eq79 eq5018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq5018
  have eq5628 : (σ x) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq5431
       have i₂ := eq5016
       grind)
    | exact superpose eq5016 eq5431
    | exact resolve eq5431 eq5016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5016 eq5431
  have eq5659 : (σ x) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq5628
  have eq5665 : (σ x) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5659
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq5659
    | exact resolve eq5659 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5659
  have eq5678 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5665 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq5665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5665
  have eq5679 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq5678
  have eq5683 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq5679
    | exact resolve eq5679 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5679
  have eq5985 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5683 eq775
    | exact resolve eq775 eq5683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5683
  have eq5991 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq5985
    | exact resolve eq5985 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5985
  have eq5992 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5991
  have eq5995 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq5992 eq29
    | exact resolve eq29 eq5992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5992
  have eq6076 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq4900 eq93
    | exact resolve eq93 eq4900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq4900
  have eq6091 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq6076
  have eq6096 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y ∨ y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq6091 eq4898
    | exact resolve eq4898 eq6091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4898 eq6091
  have eq6113 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq6096
  have eq6145 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq775 x x
       have i₂ := eq6113
       grind)
    | exact superpose eq6113 eq775
    | exact resolve eq775 eq6113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6113
  have eq6151 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq6145
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq6145
    | exact resolve eq6145 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6145
  have eq6154 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq6151 eq31
    | exact resolve eq31 eq6151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq6151
  have eq6255 : x = y ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq30 eq6154
    | exact resolve eq6154 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6154
  have eq6256 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq6255
  have eq6284 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq6256 eq30
    | exact resolve eq30 eq6256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6256
  have eq6401 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq32 eq6284
    | exact resolve eq6284 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6284
  have eq6426 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq6401 eq22
    | exact resolve eq22 eq6401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6401
  have eq6538 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq6426
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq6426
    | exact resolve eq6426 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6426
  have eq6628 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq6538 eq5995
    | (have r₁ := eq5995
       have r₂ := eq6538
       grind)
    | exact resolve eq5995 eq6538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5995
  have eq6633 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq6628
  have eq6634 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq6633
  have eq7341 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq6634 eq182
    | exact resolve eq182 eq6634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq7362 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq6634 eq781
    | exact resolve eq781 eq6634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6634
  have eq10265 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq295 X0
       have i₂ := eq373 (τ X0)
       grind)
    | exact superpose eq373 eq295
    | (have j0 := eq295 X0
       grind)
    | exact resolve eq295 eq373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295 eq373
  have eq10266 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq10265 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10265
    | (have j0 := eq10265 X0
       grind)
    | exact resolve eq10265 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10265
  have eq10356 : (σ x) = (k (σ (M.op x x)) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq30 eq10266
    | exact resolve eq10266 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10383 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq251 (σ (M.op (τ (σ X0)) (τ (σ X0)))) X0
       have i₂ := eq10266 (σ X0)
       grind)
    | exact superpose eq10266 eq251
    | (have j1 := eq10266 (σ X0)
       grind)
    | exact resolve eq251 eq10266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251 eq10266
  have eq10398 : ∀ X0 : G, (τ (σ X0)) = (k (M.op (τ (σ X0)) (τ (σ X0))) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq10383 X0
       have i₂ := eq16 (M.op (τ (σ X0)) (τ (σ X0)))
       grind)
    | exact superpose eq16 eq10383
    | (have j0 := eq10383 X0
       grind)
    | exact resolve eq10383 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10383
  have eq10420 : (σ x) = (σ (k (M.op x x) x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq41 eq10356
    | exact resolve eq10356 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq10356
  have eq10431 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq10398 X0
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq10398
    | (have j0 := eq10398 X0
       grind)
    | exact resolve eq10398 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10398
  have eq10452 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10431 X0
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq10431
    | (have j0 := eq10431 X0
       grind)
    | exact resolve eq10431 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10431
  have eq114699 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq7362 eq7341
    | exact resolve eq7341 eq7362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7341 eq7362
  have eq114762 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq114699
  have eq114768 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq114762
    | exact resolve eq114762 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114762
  have eq114770 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq114768 eq29
    | exact resolve eq29 eq114768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114768
  have eq114857 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq114770
       have r₂ := eq6538
       grind)
    | exact resolve eq114770 eq6538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6538 eq114770
  have eq114859 : x = (τ (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq114857 eq30
    | exact resolve eq30 eq114857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114857
  have eq115292 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq32 eq114859
    | exact resolve eq114859 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114859
  have eq115293 : x = (M.op x y) ∨ x = y := by grind
  clear eq115292
  have eq116045 : y = (M.op (M.op x x) y) ∨ x = y := by
    first
    | exact superpose eq115293 eq177
    | exact resolve eq177 eq115293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq116084 : x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq115293 eq778
    | exact resolve eq778 eq115293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121424 : y = (M.op x y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq116045
       have i₂ := eq116084
       grind)
    | exact superpose eq116084 eq116045
    | exact resolve eq116045 eq116084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116045 eq116084
  have eq121475 : y = (M.op x y) ∨ x = y := by grind
  clear eq121424
  have eq121488 : y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq121475
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq121475
    | exact resolve eq121475 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121475
  have eq121737 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq121488 eq115293
    | exact resolve eq115293 eq121488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115293 eq121488
  have eq121748 : x = y := by grind
  clear eq121737
  have eq122045 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq20
       have i₂ := eq121748
       grind)
    | exact superpose eq121748 eq20
    | exact resolve eq20 eq121748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq122046 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq26
       have i₂ := eq121748
       grind)
    | exact superpose eq121748 eq26
    | exact resolve eq26 eq121748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq122102 : ∀ X0 : G, x = (M.op (M.op x (M.op (M.op x (M.op x y)) X0)) x) := by
    intro X0
    first
    | (have i₁ := eq451 X0
       have i₂ := eq121748
       grind)
    | exact superpose eq121748 eq451
    | exact resolve eq451 eq121748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451 eq121748
  have eq122244 : ∀ X0 : G, x = (M.op (M.op x (M.op (M.op x y) X0)) x) := by
    intro X0
    first
    | exact superpose eq778 eq122102
    | exact resolve eq122102 eq778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778 eq122102
  have eq122285 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq122046
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq122046
    | exact resolve eq122046 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122046
  have eq122322 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq122285 eq28
    | exact resolve eq28 eq122285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq122285
  have eq122649 : (σ x) = (σ (k (M.op x y) x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10420
       have i₂ := eq122045
       grind)
    | exact superpose eq122045 eq10420
    | exact resolve eq10420 eq122045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10420
  have eq122736 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq110 eq122649
    | exact resolve eq122649 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq122649
  have eq122836 : (σ x) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq122322 eq10452
    | exact resolve eq10452 eq122322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10452
  have eq127644 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq122736 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq11 eq122736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122736
  have eq127665 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq122322 eq127644
    | exact resolve eq127644 eq122322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127644
  have eq127677 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq127665
       have r₂ := eq29
       grind)
    | exact resolve eq127665 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127665
  have eq148845 : (σ (M.op x y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq127677 eq56
    | exact resolve eq56 eq127677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq148893 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq127677 eq775
    | exact resolve eq775 eq127677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148908 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq122322 eq148893
    | exact resolve eq148893 eq122322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122322 eq148893
  have eq148938 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq781 eq148845
    | exact resolve eq148845 eq781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781 eq148845
  have eq149196 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq148908 eq148938
    | exact resolve eq148938 eq148908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148908 eq148938
  have eq149246 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq149196
  have eq149251 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq149246 eq127677
    | exact resolve eq127677 eq149246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127677 eq149246
  have eq149315 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq149251
  have eq149399 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq149315 eq30
    | exact resolve eq30 eq149315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq149315
  have eq149743 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32 eq149399
    | exact resolve eq149399 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq149399
  have eq149744 : x = (M.op x y) := by grind
  clear eq149743
  have eq149829 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq149744 eq22
    | exact resolve eq22 eq149744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq149832 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq149744 eq55
    | exact resolve eq55 eq149744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq150095 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | exact superpose eq149744 eq122244
    | exact resolve eq122244 eq149744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122244
  have eq150202 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq150095 X0
       have i₂ := eq775 x X0
       grind)
    | exact superpose eq775 eq150095
    | exact resolve eq150095 eq775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775 eq150095
  have eq150338 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq149829
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq149829
    | exact resolve eq149829 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149829
  have eq150780 : (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq150338 eq122836
    | exact resolve eq122836 eq150338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122836
  have eq150789 : (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq150780
       have r₂ := eq29
       grind)
    | exact resolve eq150780 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150780
  have eq156085 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq149832 X0
       have i₂ := eq150202 X0
       grind)
    | exact superpose eq150202 eq149832
    | exact resolve eq149832 eq150202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149832 eq150202
  have eq156273 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ x)) ∨ (τ X0) = (M.op x x) ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq248 x X0
       have i₂ := eq156085 (τ X0)
       grind)
    | exact superpose eq156085 eq248
    | (have j0 := eq248 x X0
       grind)
    | exact resolve eq248 eq156085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248 eq156085
  have eq156293 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ x)) ∨ (τ X0) = (M.op x x) ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq156273 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq156273
    | (have j0 := eq156273 X0
       grind)
    | exact resolve eq156273 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156273
  have eq156400 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op x y))) ∨ (τ X0) = (M.op x x) ∨ (τ X0) = x := by
    intro X0
    first
    | exact superpose eq150338 eq156293
    | (have j0 := eq156293 X0
       grind)
    | exact resolve eq156293 eq150338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156293
  have eq156449 : ∀ X0 : G, (k X0 (σ (M.op x y))) = X0 ∨ (τ X0) = (M.op x x) ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq156400 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq156400
    | (have j0 := eq156400 X0
       grind)
    | exact resolve eq156400 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156400
  have eq156477 : ∀ X0 : G, (τ X0) = (M.op x y) ∨ (k X0 (σ (M.op x y))) = X0 ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq156449 X0
       have i₂ := eq122045
       grind)
    | exact superpose eq122045 eq156449
    | (have j0 := eq156449 X0
       grind)
    | exact resolve eq156449 eq122045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122045 eq156449
  have eq156495 : ∀ X0 : G, (τ X0) = x ∨ (k X0 (σ (M.op x y))) = X0 ∨ (τ X0) = x := by
    intro X0
    first
    | exact superpose eq149744 eq156477
    | (have j0 := eq156477 X0
       grind)
    | exact resolve eq156477 eq149744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149744 eq156477
  have eq156496 : ∀ X0 : G, (k X0 (σ (M.op x y))) = X0 ∨ (τ X0) = x := by
    intro X0
    first
    | (have j0 := eq156495 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156495
  have eq168243 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq156496 eq150789
    | (have j1 := eq156496 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq150789 eq156496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150789 eq156496
  have eq168250 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq168243
       have r₂ := eq29
       grind)
    | exact resolve eq168243 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168243
  have eq168842 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq168250 eq15
    | exact resolve eq15 eq168250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168250
  have eq169200 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq168842
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq168842
    | exact resolve eq168842 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq168842
  have eq169314 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq150338 eq169200
    | exact resolve eq169200 eq150338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150338 eq169200
  have eq169409 : False := by grind
  exact eq169409

/-- `Equation2725`: `x = ((y ◇ x) ◇ (z ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_pyy_pxy_pyx_pxy_Equation2725 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2725 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2725.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X2)) X1) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 := by
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
  have eq19 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op (M.op X1 X0) (M.op X2 X2))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 (M.op (M.op X1 X0) (M.op X2 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X2 X2) (M.op (M.op X1 X1) X0) X1
       have i₂ := eq9 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq23 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq23 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq23 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq27 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X2)) X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X1 X2
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X1 X0 X2
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X3) (M.op X0 X1)) X2) = X3 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 X2 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X0 X1 X1
       have i₂ := eq14 X1 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq39 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq28 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq40 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq42 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X3) (M.op X0 X1)) X2) = X3 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq36 X0 X1 X2 X3
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq36 X0 X1 X0 X0
       have r₂ := eq12 X0 (M.op (M.op X0 X0) (M.op X0 X1))
       grind)
    | (have r₁ := eq36 X0 X1 X2 X3
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq36 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq44 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X2)) X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq34 X0 X1 X2
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq34 X0 X0 X2
       have r₂ := eq12 X0 (M.op (M.op X0 X0) (M.op X2 X2))
       grind)
    | (have r₁ := eq34 X0 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq34 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq45 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq33 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq33 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq46 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq38 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq38 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq38 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq50 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq40 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq40 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq52 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq45 X0 X1
       have i₂ := eq24 X1
       grind)
    | exact superpose eq24 eq45
    | (have j0 := eq45 X0 X1
       grind)
    | exact resolve eq45 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq53 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq46 X0 X1
       have i₂ := eq24 X1
       grind)
    | exact superpose eq24 eq46
    | (have j0 := eq46 X0 X1
       grind)
    | exact resolve eq46 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq55 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       have j1 := eq52 X0 X1
       grind)
    | (have r₁ := eq53 X0 X1
       have r₂ := eq52 X0 X1
       grind)
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq53
  have eq57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq24 (σ X0)
       grind)
    | exact superpose eq24 eq15
    | exact resolve eq15 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq57 X0
       have i₂ := eq24 X0
       grind)
    | exact superpose eq24 eq57
    | exact resolve eq57 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq57
  have eq75 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  clear eq18
  have eq89 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq20 x x X1
       have i₂ := eq20 x x X0
       grind)
    | exact superpose eq20 eq20
    | exact resolve eq20 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X1) X0)) = (M.op X2 X3) ∨ (M.op X2 X3) = (k X2 X3) ∨ (M.op X3 X2) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X3
       have i₂ := eq20 X0 X1 X3
       grind)
    | exact superpose eq20 eq14
    | (have j0 := eq14 X2 X3
       grind)
    | exact resolve eq14 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 (M.op X1 X1)
       have i₂ := eq20 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq20 eq9
    | exact resolve eq9 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X1) X0)) = (M.op X2 X3) ∨ (M.op X2 X3) = (k X2 X3) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq93 X0 X1 X2 X3
       have j1 := eq12 X2 X3
       grind)
    | (have r₁ := eq93 X1 X1 (M.op X1 X1) X1
       have r₂ := eq12 (M.op (M.op X1 X1) X1) X1
       grind)
    | (have r₁ := eq93 X0 X1 X1 (M.op X0 (M.op (M.op X1 X1) X0))
       have r₂ := eq12 (M.op X0 (M.op (M.op X1 X1) X0)) X1
       grind)
    | (have r₁ := eq93 X0 X1 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq93 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq120 : ∀ X0 X2 X3 : G, (M.op X0 X0) = (M.op X2 X3) ∨ (M.op X2 X3) = (k X2 X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq106 X0 x X2 X3
       have i₂ := eq99 x X0
       grind)
    | exact superpose eq99 eq106
    | (have j0 := eq106 X0 x X2 X3
       grind)
    | exact resolve eq106 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq129 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq50 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq50
    | exact resolve eq50 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq50 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq161 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq55 (σ X0) (σ X1)
       grind)
    | exact superpose eq55 eq15
    | (have j1 := eq55 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq166 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq161 X0 X1
       have i₂ := eq58 X1
       grind)
    | exact superpose eq58 eq161
    | (have j0 := eq161 X0 X1
       grind)
    | exact resolve eq161 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161
  have eq177 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X2 (M.op X0 (M.op X1 X1))) (M.op X3 X3))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 (M.op X0 (M.op X1 X1)) X2 X3 (M.op X0 X0)
       have i₂ := eq19 X0 X0 X0 X1
       grind)
    | exact superpose eq19 eq19
    | exact resolve eq19 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 (M.op X4 X4)) = (M.op (M.op (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X3 X3)) (M.op X0 (M.op X5 X5))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq19 (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X1 (M.op X4 X4)) X5 X3
       have i₂ := eq19 X1 X0 X2 X4
       grind)
    | exact superpose eq19 eq19
    | exact resolve eq19 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq198 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X2)) (M.op X0 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X1 X1 (M.op X1 X1) X2
       have i₂ := eq20 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq20 eq19
    | exact resolve eq19 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq214 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X3 X3)) = (M.op (M.op X0 (M.op X4 X4)) (M.op X1 (M.op X2 X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op X3 X3)) (M.op X1 (M.op X2 X2)) X4
       have i₂ := eq19 X1 X0 X3 X2
       grind)
    | exact superpose eq19 eq9
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq232 : ∀ X0 X1 X4 X5 : G, (M.op X1 (M.op X4 X4)) = (M.op (M.op X0 X1) (M.op X0 (M.op X5 X5))) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq186 X0 X1 x x X4 X5
       have i₂ := eq198 x (M.op X0 X1) x
       grind)
    | exact superpose eq198 eq186
    | exact resolve eq186 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq261 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X2) X1) = (M.op (M.op (M.op X0 X0) (M.op X3 X4)) X1) ∨ (M.op X3 X4) = (k X3 X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq42 X3 X4 X1 (M.op (M.op X2 X2) X1)
       have i₂ := eq20 X1 X2 X0
       grind)
    | exact superpose eq20 eq42
    | (have j0 := eq42 X3 X4 X2 X3
       grind)
    | exact resolve eq42 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq302 : ∀ X1 X2 X3 X4 : G, (M.op (M.op X2 X2) X1) = (M.op (M.op X3 X4) X1) ∨ (M.op X3 X4) = (k X3 X4) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq261 x X1 X2 X3 X4
       have i₂ := eq99 x (M.op X3 X4)
       grind)
    | exact superpose eq99 eq261
    | (have j0 := eq261 x X1 X2 X3 X4
       grind)
    | exact resolve eq261 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261
  have eq310 : ∀ X1 X3 X4 : G, (M.op (M.op X3 X4) X1) = X1 ∨ (M.op X3 X4) = (k X3 X4) := by
    intro X1 X3 X4
    first
    | (have i₁ := eq302 X1 x X3 X4
       have i₂ := eq99 x X1
       grind)
    | exact superpose eq99 eq302
    | (have j0 := eq302 X1 x X3 X4
       grind)
    | exact resolve eq302 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302
  have eq346 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X3 X4)) (M.op (M.op X1 X0) (M.op X2 X2))) = X0 ∨ (M.op X3 X4) = (k X3 X4) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq42 X3 X4 (M.op (M.op X1 X0) (M.op X2 X2)) X0
       have i₂ := eq44 X1 X0 X2
       grind)
    | exact superpose eq44 eq42
    | (have j0 := eq42 X3 X4 X2 X3
       have j1 := eq44 X3 X4 X2
       grind)
    | exact resolve eq42 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq44
  have eq903 : ∀ X0 X1 : G, (M.op (σ X1) (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq27 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq27
    | exact resolve eq27 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq1017 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq903 X0 X1
       have i₂ := eq58 X1
       grind)
    | exact superpose eq58 eq903
    | (have j0 := eq903 X0 X1
       grind)
    | exact resolve eq903 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903
  have eq1033 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1017 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq1017
    | (have j0 := eq1017 X0 X1
       grind)
    | exact resolve eq1017 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1017
  have eq1040 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1033 X0 X1
       have j1 := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq1033 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq1033 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1033
  have eq1201 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq89 (σ X0) X1
       have i₂ := eq58 X0
       grind)
    | exact superpose eq58 eq89
    | exact resolve eq89 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq1202 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq99 (σ X0) X1
       have i₂ := eq58 X0
       grind)
    | exact superpose eq58 eq99
    | exact resolve eq99 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1203 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ (M.op X0 X0)) (M.op X1 X1)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) (σ X0) X1
       have i₂ := eq58 X0
       grind)
    | exact superpose eq58 eq9
    | exact resolve eq9 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq1834 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op X0 X0) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq120 X0 (σ x) (σ y)
       grind)
    | exact superpose eq120 eq16
    | (have j1 := eq120 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1848 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op X0 X0) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    intro X0
    first
    | (have i₁ := eq1834 X0
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq1834
    | (have j0 := eq1834 X0
       grind)
    | exact resolve eq1834 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1834
  have eq2528 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X0 (M.op X1 (M.op X2 X2))) (M.op X0 (M.op X4 X4))) = X1 := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq177 (M.op X0 (M.op X1 (M.op X2 X2))) x X1 X4
       have i₂ := eq177 X1 X2 X0 x
       grind)
    | exact superpose eq177 eq177
    | exact resolve eq177 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq2763 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X4 X4)) = (M.op (M.op X5 X3) (M.op X5 (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X2 X2))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq232 X5 X3 X4 (M.op X1 X1)
       have i₂ := eq232 X0 (M.op X1 X1) X1 X2
       grind)
    | exact superpose eq232 eq232
    | exact resolve eq232 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2831 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X2 X2))) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq99 (M.op X1 X1) X3
       have i₂ := eq232 X0 (M.op X1 X1) X1 X2
       grind)
    | exact superpose eq232 eq99
    | exact resolve eq99 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq2922 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 X3)) = (M.op (M.op (M.op X0 (M.op X1 X1)) (M.op X4 X4)) (M.op X2 X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 (M.op X2 (M.op X3 X3)) (M.op X2 X0) X4
       have i₂ := eq232 X2 X0 X1 X3
       grind)
    | exact superpose eq232 eq9
    | exact resolve eq9 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq2946 : ∀ X0 X2 X3 : G, (M.op X2 (M.op X3 X3)) = (M.op X0 (M.op X2 X0)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq2922 X0 x X2 X3 x
       have i₂ := eq198 x X0 x
       grind)
    | exact superpose eq198 eq2922
    | exact resolve eq2922 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2922
  have eq3975 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X1))) = (k X0 (τ (σ X1))) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq75 X0 (σ X1)
       have i₂ := eq1040 (σ X0) X1
       grind)
    | exact superpose eq1040 eq75
    | (have j1 := eq1040 (σ X0) X1
       grind)
    | exact resolve eq75 eq1040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq1040
  have eq4036 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3975 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq3975
    | (have j0 := eq3975 X0 X1
       grind)
    | exact resolve eq3975 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3975
  have eq4610 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X0)) (M.op X2 X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X0 X1 x x
       have i₂ := eq214 X0 (M.op X1 X0) x X2 x
       grind)
    | (have i₁ := eq19 X0 X0 X0 x
       have i₂ := eq214 X0 (M.op x x) X2 (M.op X0 X0) x
       grind)
    | exact superpose eq214 eq19
    | exact resolve eq19 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5351 : ∀ X0 X1 X2 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X2 X2) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq129 X2 x
       have i₂ := eq120 X0 X2 x
       grind)
    | exact superpose eq120 eq129
    | (have j1 := eq120 X2 X0 X1
       grind)
    | exact resolve eq129 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq5354 : ∀ X0 X1 X2 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op (M.op X0 X1) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq129 x x
       have i₂ := eq310 X1 x x
       grind)
    | exact superpose eq310 eq129
    | (have j1 := eq310 X2 X0 X1
       grind)
    | exact resolve eq129 eq310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq310
  have eq5808 : ∀ X0 X1 X2 X3 X4 : G, (M.op (σ (M.op X0 X0)) (M.op X2 X2)) = (M.op (M.op (σ X1) (M.op X3 X3)) (M.op (σ X0) (M.op X4 X4))) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq214 (σ X1) (σ X0) X4 X2 X3
       have i₂ := eq166 X1 X0
       grind)
    | exact superpose eq166 eq214
    | (have j1 := eq166 X1 X0
       grind)
    | exact resolve eq214 eq166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166
  have eq5852 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X2) = (M.op (M.op (σ X1) (M.op X3 X3)) (M.op (σ X0) (M.op X4 X4))) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq5808 X0 X1 X2 X3 X4
       have i₂ := eq1202 X0 (M.op X2 X2)
       grind)
    | exact superpose eq1202 eq5808
    | (have j0 := eq5808 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq5808 eq1202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1202 eq5808
  have eq30204 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op (M.op X1 (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X2 X2))) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq346 X1 X0 X2 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346
  have eq30205 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X2 X2))) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq30204 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30204
  have eq82294 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    intro X0
    first
    | (have i₁ := eq1848 x
       have i₂ := eq1201 X0 x
       grind)
    | exact superpose eq1201 eq1848
    | exact resolve eq1848 eq1201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1848
  have eq82482 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X2)) (σ (M.op X0 X0))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X1 X1 X1 X2
       have i₂ := eq1201 X0 (M.op X1 X1)
       grind)
    | exact superpose eq1201 eq19
    | exact resolve eq19 eq1201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq82491 : ∀ X0 X1 X2 X3 : G, (σ (M.op X0 X0)) = (M.op (M.op X1 (M.op X2 X2)) (M.op X1 (M.op X3 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq214 X1 X1 X3 X1 X2
       have i₂ := eq1201 X0 (M.op X1 X1)
       grind)
    | exact superpose eq1201 eq214
    | exact resolve eq214 eq1201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq600785 : ∀ X0 X1 X3 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X0 (M.op X1 X0)) (M.op X3 X3))) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq2528 (M.op X0 (M.op X1 X0)) (M.op X1 X0) x X3
       have i₂ := eq30205 X1 X0 x
       grind)
    | exact superpose eq30205 eq2528
    | (have j1 := eq30205 X1 X0 x
       grind)
    | exact resolve eq2528 eq30205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2528 eq30205
  have eq601403 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq600785 X0 X1 x
       have i₂ := eq4610 X0 X1 x
       grind)
    | exact superpose eq4610 eq600785
    | (have j0 := eq600785 X0 X1 x
       grind)
    | exact resolve eq600785 eq4610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4610 eq600785
  have eq601680 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq601403 X0 X1
       have j1 := eq137 X1 X0
       grind)
    | (have r₁ := eq601403 X0 X1
       have r₂ := eq137 X0 X1
       grind)
    | (have r₁ := eq601403 X1 X0
       have r₂ := eq137 X0 X1
       grind)
    | exact resolve eq601403 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137 eq601403
  have eq644449 : ∀ X0 X1 X2 X3 X4 X5 : G, (σ (M.op X1 X1)) = (M.op (M.op (σ (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op (M.op X2 (M.op X3 X3)) (M.op X2 (M.op X4 X4)))))) (M.op X5 X5)) (σ (M.op X1 X1))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq1203 (M.op X1 X1) X5
       have i₂ := eq2763 X2 X3 X4 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq2763 eq1203
    | exact resolve eq1203 eq2763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1203
  have eq644604 : ∀ X0 X1 X2 X3 X4 : G, (σ (M.op x y)) ≠ (σ (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op (M.op X2 (M.op X3 X3)) (M.op X2 (M.op X4 X4)))))) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq82294 (M.op X1 X1)
       have i₂ := eq2763 X2 X3 X4 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq2763 eq82294
    | exact resolve eq82294 eq2763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2763 eq82294
  have eq646141 : ∀ X0 X1 X2 X3 X4 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op (M.op X2 (M.op X3 X3)) (M.op X2 (M.op X4 X4)))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq644604 X0 X1 X2 X3 X4
       have i₂ := eq601680 y x
       grind)
    | exact superpose eq601680 eq644604
    | (have j0 := eq644604 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq644604 eq601680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644604
  have eq646226 : ∀ X0 X1 X2 X3 X4 : G, (σ (M.op X1 X1)) = (σ (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op (M.op X2 (M.op X3 X3)) (M.op X2 (M.op X4 X4)))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq644449 X0 X1 X2 X3 X4 x
       have i₂ := eq82482 X1 (σ (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op (M.op X2 (M.op X3 X3)) (M.op X2 (M.op X4 X4)))))) x
       grind)
    | exact superpose eq82482 eq644449
    | exact resolve eq644449 eq82482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82482 eq644449
  have eq647531 : ∀ X0 X1 X2 X3 X4 : G, (σ (M.op x y)) ≠ (σ (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op (M.op X2 (M.op X3 X3)) (M.op X2 (M.op X4 X4)))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have j0 := eq646141 X0 X1 X2 X3 X4
       grind)
    | (have r₁ := eq646141 X0 X1 X2 X3 X4
       have r₂ := eq16
       grind)
    | exact resolve eq646141 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646141
  have eq647939 : ∀ X1 : G, (σ (M.op x y)) ≠ (σ (M.op X1 X1)) := by
    intro X1
    first
    | (have i₁ := eq647531 x X1 x x x
       have i₂ := eq646226 x X1 x x x
       grind)
    | exact superpose eq646226 eq647531
    | exact resolve eq647531 eq646226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646226 eq647531
  have eq709762 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq647939 x
       have i₂ := eq1201 x X0
       grind)
    | exact superpose eq1201 eq647939
    | exact resolve eq647939 eq1201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1201
  have eq762130 : ∀ X0 X1 X2 : G, (σ (M.op x y)) ≠ (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq709762 (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X2 X2)))
       have i₂ := eq2831 X0 X1 X2 (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X2 X2)))
       grind)
    | exact superpose eq2831 eq709762
    | exact resolve eq709762 eq2831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2831 eq709762
  have eq1358287 : ∀ X0 X1 X3 : G, (σ (M.op x y)) ≠ (M.op (M.op X0 (M.op X1 X0)) (M.op X1 (M.op X3 X3))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq762130 X1 x X3
       have i₂ := eq2946 X0 X1 x
       grind)
    | (have i₁ := eq762130 X0 X0 x
       have i₂ := eq2946 X0 X0 X3
       grind)
    | exact superpose eq2946 eq762130
    | exact resolve eq762130 eq2946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2946
  have eq1677415 : ∀ X0 X1 X2 X3 : G, (σ (M.op X0 X0)) ≠ (M.op (M.op X1 (M.op X2 X2)) (M.op X1 (M.op X3 X3))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq762130 X1 X2 X3
       have i₂ := eq5351 x y X0
       grind)
    | exact superpose eq5351 eq762130
    | (have j1 := eq5351 x y X2
       grind)
    | exact resolve eq762130 eq5351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5351 eq762130
  have eq1678193 : ∀ X0 X1 X2 X3 : G, (σ (M.op X0 X0)) ≠ (M.op (M.op X1 (M.op X2 X2)) (M.op X1 (M.op X3 X3))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq1677415 X0 X1 X2 X3
       grind)
    | (have r₁ := eq1677415 X0 X1 X2 X3
       have r₂ := eq16
       grind)
    | exact resolve eq1677415 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1677415
  have eq1681076 : (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq1678193 x x x x
       have r₂ := eq82491 x x x x
       grind)
    | exact resolve eq1678193 eq82491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82491 eq1678193
  have eq1725397 : ∀ X0 X1 X2 X3 X4 X5 : G, (σ (M.op x y)) ≠ (M.op (M.op (M.op (σ X1) (M.op X2 X2)) (M.op X0 X0)) (M.op (M.op (σ X3) (M.op X4 X4)) (M.op X5 X5))) ∨ (σ (k X3 X1)) = (M.op (σ X3) (σ X1)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq1358287 (M.op (σ X1) (M.op X2 X2)) (M.op (σ X3) (M.op X4 X4)) X5
       have i₂ := eq5852 X1 X3 X0 X4 X2
       grind)
    | (have i₁ := eq1358287 X2 X2 X3
       have i₂ := eq5852 X0 X1 X2 X3 X4
       grind)
    | exact superpose eq5852 eq1358287
    | (have j1 := eq5852 X1 X3 X2 X3 X4
       grind)
    | exact resolve eq1358287 eq5852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5852 eq1358287
  have eq1725452 : ∀ X0 X1 X2 X3 : G, (σ (M.op x y)) ≠ (M.op (M.op (M.op (σ X1) (M.op X2 X2)) (M.op X0 X0)) (σ X3)) ∨ (σ (k X3 X1)) = (M.op (σ X3) (σ X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1725397 X0 X1 X2 X3 x x
       have i₂ := eq198 x (σ X3) x
       grind)
    | exact superpose eq198 eq1725397
    | (have j0 := eq1725397 X0 X1 X2 X3 x x
       grind)
    | exact resolve eq1725397 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1725397
  have eq1727949 : ∀ X1 X3 : G, (σ (M.op x y)) ≠ (M.op (σ X1) (σ X3)) ∨ (σ (k X3 X1)) = (M.op (σ X3) (σ X1)) := by
    intro X1 X3
    first
    | (have i₁ := eq1725452 x X1 x X3
       have i₂ := eq198 x (σ X1) x
       grind)
    | exact superpose eq198 eq1725452
    | (have j0 := eq1725452 x X1 x X3
       grind)
    | exact resolve eq1725452 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198 eq1725452
  have eq1729664 : ∀ X1 X3 : G, (M.op (σ X3) (σ X1)) = (σ (M.op X3 X1)) ∨ (σ (M.op x y)) ≠ (M.op (σ X1) (σ X3)) := by
    intro X1 X3
    first
    | (have i₁ := eq1727949 X1 X3
       have i₂ := eq601680 X1 X3
       grind)
    | exact superpose eq601680 eq1727949
    | (have j0 := eq1727949 X1 X3
       grind)
    | exact resolve eq1727949 eq601680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1727949
  have eq1758457 : (k y x) = (τ (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq4036 y x
       have i₂ := eq1681076
       grind)
    | exact superpose eq1681076 eq4036
    | exact resolve eq4036 eq1681076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4036 eq1681076
  have eq1758874 : (k y x) = (τ (σ (M.op x y))) := by
    first
    | (have r₁ := eq1758457
       have r₂ := eq647939 x
       grind)
    | exact resolve eq1758457 eq647939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1758457
  have eq1758987 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq1758874
       have i₂ := eq10 (M.op x y)
       grind)
    | exact superpose eq10 eq1758874
    | exact resolve eq1758874 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1758874
  have eq1759047 : (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq1758987
       have i₂ := eq601680 x y
       grind)
    | exact superpose eq601680 eq1758987
    | exact resolve eq1758987 eq601680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601680 eq1758987
  have eq1889570 : ∀ X0 : G, (M.op (M.op x y) X0) = X0 ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq5354 y x x
       have i₂ := eq1759047
       grind)
    | exact superpose eq1759047 eq5354
    | (have j0 := eq5354 x y X0
       grind)
    | exact resolve eq5354 eq1759047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5354 eq1759047
  have eq1889724 : ∀ X0 : G, (M.op (M.op x y) X0) = X0 ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq1889570 X0
       have j1 := eq1729664 y x
       grind)
    | (have r₁ := eq1889570 X0
       have r₂ := eq1729664 x y
       grind)
    | (have r₁ := eq1889570 X0
       have r₂ := eq1729664 y x
       grind)
    | exact resolve eq1889570 eq1729664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1729664 eq1889570
  have eq1889794 : ∀ X0 : G, (M.op (M.op x y) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1889724 X0
       grind)
    | (have r₁ := eq1889724 X0
       have r₂ := eq16
       grind)
    | exact resolve eq1889724 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1889724
  have eq2001377 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq647939 (M.op x y)
       have i₂ := eq1889794 (M.op x y)
       grind)
    | exact superpose eq1889794 eq647939
    | exact resolve eq647939 eq1889794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647939 eq1889794
  have eq2002026 : False := by grind
  exact eq2002026

/-- `Equation2725`: `x = ((y ◇ x) ◇ (z ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(X,X) = m(X,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pxy_y_pyx_pxy_Equation2725 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2725 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2725.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X2)) X1) = X0 := by
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
  clear eq36
  have eq47 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op X0 X0)) x) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y x X0
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) (σ x)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op (M.op X1 X0) (M.op X2 X2))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X1 (M.op (M.op X1 X0) (M.op X2 X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X2 X2) (M.op (M.op X1 X1) X0) X1
       have i₂ := eq14 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
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
  clear eq45
  have eq69 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq66
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq66
    | exact resolve eq66 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq70 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq69
    | exact resolve eq69 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq71 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq70
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq70
    | exact resolve eq70 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq213 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k (τ X0) X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq16
    | exact resolve eq16 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq329 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq50 X0 (M.op X0 X0) X1
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq50
    | exact resolve eq50 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq343 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 (M.op X1 X1)
       have i₂ := eq50 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq353 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    grind
  have eq369 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X1
       have i₂ := eq329 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq329 X0 X1
       grind)
    | exact superpose eq329 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq329 X0 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq329 X1 X1
       grind)
    | exact resolve eq12 eq329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq373 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq369 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369
  have eq419 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (M.op X1 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq39 X0 (M.op X1 X1)
       have i₂ := eq353 X1 (τ X0)
       grind)
    | exact superpose eq353 eq39
    | exact resolve eq39 eq353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq423 : ∀ X0 X1 : G, (k (σ (M.op X1 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq419 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq419
    | exact resolve eq419 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419
  have eq433 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X2 (M.op X0 (M.op X1 X1))) (M.op X3 X3))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq49 (M.op X0 (M.op X1 X1)) X2 X3 (M.op X0 X0)
       have i₂ := eq49 X0 X0 X0 X1
       grind)
    | exact superpose eq49 eq49
    | exact resolve eq49 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq440 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X0) (M.op X3 X3)) = (M.op (M.op X1 (M.op X2 X2)) (M.op X0 (M.op X4 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq49 X1 (M.op (M.op X1 X0) (M.op X3 X3)) X4 X2
       have i₂ := eq14 X0 X1 X3
       grind)
    | exact superpose eq14 eq49
    | exact resolve eq49 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq442 : ∀ X0 X1 X2 : G, (M.op (M.op x y) (M.op X1 X1)) = (M.op (M.op x (M.op X0 X0)) (M.op y (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | exact superpose eq47 eq49
    | exact resolve eq49 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq443 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) (σ y)) (M.op X1 X1)) = (M.op (M.op (σ x) (M.op X0 X0)) (M.op (σ y) (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | exact superpose eq48 eq49
    | exact resolve eq49 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq454 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X2)) (M.op X0 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49 X1 X1 (M.op X1 X1) X2
       have i₂ := eq50 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq50 eq49
    | exact resolve eq49 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq50
  have eq622 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (M.op X1 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq213 (M.op X1 X1) X0
       have i₂ := eq353 X1 (σ X0)
       grind)
    | exact superpose eq353 eq213
    | exact resolve eq213 eq353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213 eq353
  have eq644 : ∀ X0 X1 : G, (k (τ (M.op X1 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq622 X0 X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq622
    | exact resolve eq622 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622
  have eq4065 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) ∨ (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq423 (σ (M.op X1 X1)) X1
       have i₂ := eq373 X0 (σ (M.op X1 X1))
       grind)
    | exact superpose eq373 eq423
    | (have j1 := eq373 X0 (σ (M.op X1 X1))
       grind)
    | exact resolve eq423 eq373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423
  have eq4077 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) ∨ (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq644 (τ (M.op X1 X1)) X1
       have i₂ := eq373 X0 (τ (M.op X1 X1))
       grind)
    | exact superpose eq373 eq644
    | (have j1 := eq373 X0 (τ (M.op X1 X1))
       grind)
    | exact resolve eq644 eq373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373 eq644
  have eq4109 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq4077 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4077
  have eq4113 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq4065 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4065
  have eq4234 : ∀ X0 X2 : G, (M.op (τ (M.op X0 X0)) X2) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq343 x X2
       have i₂ := eq4109 x X0
       grind)
    | exact superpose eq4109 eq343
    | exact resolve eq343 eq4109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4109
  have eq4367 : ∀ X0 X2 : G, (M.op (σ (M.op X0 X0)) X2) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq343 x X2
       have i₂ := eq4113 x X0
       grind)
    | exact superpose eq4113 eq343
    | exact resolve eq343 eq4113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4113
  have eq5384 : ∀ X0 X1 X3 : G, (M.op x (M.op X1 X1)) = (M.op y (M.op (M.op (M.op x y) (M.op X0 X0)) (M.op X3 X3))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq433 y x (M.op x (M.op X1 X1)) X3
       have i₂ := eq442 X1 X0 x
       grind)
    | exact superpose eq442 eq433
    | exact resolve eq433 eq442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442
  have eq5390 : ∀ X1 : G, (M.op y (M.op x y)) = (M.op x (M.op X1 X1)) := by
    intro X1
    first
    | (have i₁ := eq5384 x X1 x
       have i₂ := eq454 x sF0 x
       grind)
    | exact superpose eq454 eq5384
    | exact resolve eq5384 eq454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5384
  have eq5550 : ∀ X0 X1 X3 : G, (M.op (σ x) (M.op X1 X1)) = (M.op (σ y) (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) (M.op X3 X3))) := by
    intro X0 X1 X3
    first
    | exact superpose eq443 eq433
    | exact resolve eq433 eq443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443
  have eq5556 : ∀ X1 : G, (M.op (σ x) (M.op X1 X1)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    intro X1
    first
    | (have i₁ := eq5550 x X1 x
       have i₂ := eq454 x sF4 x
       grind)
    | exact superpose eq454 eq5550
    | exact resolve eq5550 eq454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5550
  have eq5595 : ∀ X1 : G, (σ x) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op X1 X1)) := by
    intro X1
    first
    | exact superpose eq5556 eq454
    | exact resolve eq454 eq5556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6609 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X0 (M.op X1 X1)) (M.op (M.op X2 (M.op X3 X3)) (M.op X4 X4)))) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq433 X2 X3 X0 x
       have i₂ := eq440 (M.op X2 (M.op X3 X3)) X0 X1 x X4
       grind)
    | (have i₁ := eq433 (M.op X1 X1) X1 X1 (M.op X4 X4)
       have i₂ := eq440 (M.op X4 X4) X1 (M.op X1 X1) X3 X4
       grind)
    | exact superpose eq440 eq433
    | exact resolve eq433 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6699 : ∀ X0 X1 X2 X3 X5 : G, (M.op X0 (M.op X3 X3)) = (M.op X1 (M.op (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X5 X5))) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq433 X1 x (M.op X0 (M.op X3 X3)) X5
       have i₂ := eq440 X1 X0 X3 X2 x
       grind)
    | (have i₁ := eq433 (M.op X1 X1) X1 (M.op X1 X0) X3
       have i₂ := eq440 X0 X1 X2 (M.op X1 X1) x
       grind)
    | exact superpose eq440 eq433
    | exact resolve eq433 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433 eq440
  have eq6833 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X3 X3)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq6699 X0 X1 x X3 x
       have i₂ := eq454 x (M.op X0 X1) x
       grind)
    | exact superpose eq454 eq6699
    | exact resolve eq6699 eq454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6699
  have eq6853 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 (M.op X1 X1)) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6609 X0 X1 X2 x x
       have i₂ := eq454 x X2 x
       grind)
    | exact superpose eq454 eq6609
    | exact resolve eq6609 eq454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454 eq6609
  have eq20086 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op X1 X2) X0)) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X1 x
       have i₂ := eq6833 (M.op X1 X2) X0 x
       grind)
    | (have i₁ := eq14 X0 X1 (M.op X1 X0)
       have i₂ := eq6833 (M.op X1 X0) (M.op X1 X0) x
       grind)
    | exact superpose eq6833 eq14
    | exact resolve eq14 eq6833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20122 : ∀ X0 : G, y = (M.op (M.op X0 (M.op (M.op x y) X0)) x) := by
    intro X0
    first
    | (have i₁ := eq47 x
       have i₂ := eq6833 sF0 x x
       grind)
    | (have i₁ := eq47 sF0
       have i₂ := eq6833 sF0 sF0 x
       grind)
    | exact superpose eq6833 eq47
    | exact resolve eq47 eq6833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq20130 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq48 x
       have i₂ := eq6833 sF4 x x
       grind)
    | (have i₁ := eq48 sF4
       have i₂ := eq6833 sF4 sF4 x
       grind)
    | exact superpose eq6833 eq48
    | exact resolve eq48 eq6833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq6833
  have eq20705 : ∀ X0 : G, x = (M.op X0 (M.op (M.op y (M.op x y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq6853 x x X0
       have i₂ := eq5390 x
       grind)
    | exact superpose eq5390 eq6853
    | exact resolve eq6853 eq5390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5390
  have eq20707 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (M.op (σ y) (M.op (σ x) (σ y))) X0)) := by
    intro X0
    first
    | exact superpose eq5556 eq6853
    | exact resolve eq6853 eq5556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5556 eq6853
  have eq21088 : x = (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op y (M.op x y))) (σ x)) := by
    first
    | exact superpose eq20707 eq20705
    | exact resolve eq20705 eq20707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20705 eq20707
  have eq39067 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq71 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq39068 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq39067
    | exact resolve eq39067 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39067
  have eq39073 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq39068
       have r₂ := eq28
       grind)
    | exact resolve eq39068 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39068
  have eq39075 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq39073
    | exact resolve eq39073 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39073
  have eq39212 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq39075 eq20086
    | exact resolve eq20086 eq39075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39075
  have eq39216 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20130 eq39212
    | exact resolve eq39212 eq20130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20130 eq39212
  have eq39232 : ∀ X0 : G, (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op X0 X0) = (σ x) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq39216
       have i₂ := eq329 X0 sF3
       grind)
    | (have i₁ := eq39216
       have i₂ := eq329 sF3 x
       grind)
    | exact superpose eq329 eq39216
    | exact resolve eq39216 eq329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39216
  have eq40774 : ∀ X0 X1 : G, x = (M.op (M.op X0 (M.op (M.op x y) X0)) x) ∨ (σ x) = (σ y) ∨ (M.op X1 X1) = (σ x) ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq20086 X0 x x
       have i₂ := eq39232 X1
       grind)
    | (have i₁ := eq20086 X0 X0 X0
       have i₂ := eq39232 X0
       grind)
    | exact superpose eq39232 eq20086
    | (have j1 := eq39232 X1
       grind)
    | exact resolve eq20086 eq39232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20086 eq39232
  have eq40779 : ∀ X1 : G, x = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op X1 X1) = (σ x) ∨ x = y := by
    intro X1
    first
    | exact superpose eq20122 eq40774
    | (have j0 := eq40774 x X1
       grind)
    | exact resolve eq40774 eq20122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20122 eq40774
  have eq40846 : ∀ X0 X1 : G, (M.op x X0) = X0 ∨ (σ x) = (σ y) ∨ (M.op X1 X1) = (σ x) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq343 y X0
       have i₂ := eq40779 X1
       grind)
    | exact superpose eq40779 eq343
    | (have j1 := eq40779 X1
       grind)
    | exact resolve eq343 eq40779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343 eq40779
  have eq41928 : ∀ X0 : G, (M.op X0 X0) = (σ x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq40846 y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq40846
    | (have j0 := eq40846 y X0
       grind)
    | exact resolve eq40846 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40846
  have eq42561 : ∀ X1 : G, (M.op (τ (σ x)) X1) = X1 ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X1
    first
    | (have i₁ := eq4234 x X1
       have i₂ := eq41928 x
       grind)
    | exact superpose eq41928 eq4234
    | exact resolve eq4234 eq41928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4234 eq41928
  have eq42807 : ∀ X1 : G, (M.op x X1) = X1 ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X1
    first
    | exact superpose eq29 eq42561
    | exact resolve eq42561 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42561
  have eq43306 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq19
       have i₂ := eq42807 y
       grind)
    | exact superpose eq42807 eq19
    | (have j1 := eq42807 y
       grind)
    | exact resolve eq19 eq42807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42807
  have eq43487 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq43306
  have eq43568 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq43487 eq30
    | exact resolve eq30 eq43487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq43487
  have eq43636 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq43568
    | exact resolve eq43568 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq43568
  have eq43637 : y = (M.op x y) ∨ x = y := by grind
  clear eq43636
  have eq43912 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq43637 eq21
    | exact resolve eq21 eq43637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44002 : x = (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op y y)) (σ x)) ∨ x = y := by
    first
    | exact superpose eq43637 eq21088
    | exact resolve eq21088 eq43637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21088 eq43637
  have eq44004 : x = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq5595 eq44002
    | exact resolve eq44002 eq5595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5595 eq44002
  have eq44078 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq43912
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq43912
    | exact resolve eq43912 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43912
  have eq44080 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq44078 eq27
    | exact resolve eq27 eq44078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44078
  have eq44225 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ x = y := by
    intro X0
    first
    | exact superpose eq44004 eq4367
    | exact resolve eq4367 eq44004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44004
  have eq44341 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq44225 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq44225
    | (have j0 := eq44225 X0
       grind)
    | exact resolve eq44225 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44225
  have eq45825 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq44341 eq44080
    | exact resolve eq44080 eq44341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44080 eq44341
  have eq46007 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq45825
  have eq46075 : x = y := by
    first
    | (have r₁ := eq46007
       have r₂ := eq28
       grind)
    | exact resolve eq46007 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46007
  have eq46084 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq46075
       grind)
    | exact superpose eq46075 eq19
    | exact resolve eq19 eq46075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq46085 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq46075
       grind)
    | exact superpose eq46075 eq25
    | exact resolve eq25 eq46075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq46075
  have eq46229 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq46085
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq46085
    | exact resolve eq46085 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq46085
  have eq46235 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq46229 eq27
    | exact resolve eq27 eq46229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq46229
  have eq46323 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq46084
       have i₂ := eq329 X0 x
       grind)
    | (have i₁ := eq46084
       have i₂ := eq329 x X0
       grind)
    | exact superpose eq329 eq46084
    | exact resolve eq46084 eq329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329 eq46084
  have eq47643 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq46235 eq46323
    | exact resolve eq46323 eq46235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46235
  have eq47881 : ∀ X0 : G, (M.op x y) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4367 X0 (σ (M.op X0 X0))
       have i₂ := eq46323 (σ (M.op X0 X0))
       grind)
    | exact superpose eq46323 eq4367
    | exact resolve eq4367 eq46323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4367
  have eq47938 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq47881 x
       have i₂ := eq46323 x
       grind)
    | exact superpose eq46323 eq47881
    | exact resolve eq47881 eq46323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46323 eq47881
  have eq48161 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq21 eq47938
    | exact resolve eq47938 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq47938
  have eq48276 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq47643 eq28
    | exact resolve eq28 eq47643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq47643
  have eq48371 : False := by grind
  exact eq48371

/-- `Equation2725`: `x = ((y ◇ x) ◇ (z ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(X,X) = m(Y,X) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pyx_y_pyy_pxy_Equation2725 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2725 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2725.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X2)) X1) = X0 := by
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
  have eq174 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op (M.op X1 X0) (M.op X2 X2))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X1 (M.op (M.op X1 X0) (M.op X2 X2)) X3
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X2 X2) (M.op (M.op X1 X1) X0) X1
       have i₂ := eq16 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq343 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq393 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq38 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq174 (τ X0)
       grind)
    | exact superpose eq174 eq38
    | exact resolve eq38 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq425 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq393 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq393
    | exact resolve eq393 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393
  have eq445 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq343 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq174 (σ X0)
       grind)
    | exact superpose eq174 eq343
    | exact resolve eq343 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq343
  have eq467 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq445 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq445
    | exact resolve eq445 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445
  have eq698 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq178 x x X1
       have i₂ := eq178 x x X0
       grind)
    | exact superpose eq178 eq178
    | exact resolve eq178 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq699 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X1) X0)) ≠ X3 ∨ (k X3 X2) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X3 X2
       have i₂ := eq178 X0 X1 X2
       grind)
    | exact superpose eq178 eq13
    | (have j0 := eq13 X3 X2
       grind)
    | (have r₁ := eq13 (M.op X0 (M.op (M.op X1 X1) X0)) X2
       have r₂ := eq178 X0 X1 X2
       grind)
    | exact resolve eq13 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq706 : ∀ X0 X1 X2 : G, (k (τ (M.op X0 (M.op (M.op X1 X1) X0))) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq467 X2
       have i₂ := eq178 X0 X1 (σ X2)
       grind)
    | exact superpose eq178 eq467
    | exact resolve eq467 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467
  have eq707 : ∀ X0 X1 X2 : G, (k (σ (M.op X0 (M.op (M.op X1 X1) X0))) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq425 X2
       have i₂ := eq178 X0 X1 (τ X2)
       grind)
    | exact superpose eq178 eq425
    | exact resolve eq425 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425
  have eq709 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X1 (M.op X1 X1)
       have i₂ := eq178 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq711 : ∀ X0 X2 : G, (k (σ (M.op X0 X0)) X2) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq707 X0 x X2
       have i₂ := eq709 x X0
       grind)
    | exact superpose eq709 eq707
    | exact resolve eq707 eq709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707
  have eq712 : ∀ X0 X2 : G, (k (τ (M.op X0 X0)) X2) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq706 X0 x X2
       have i₂ := eq709 x X0
       grind)
    | exact superpose eq709 eq706
    | exact resolve eq706 eq709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706
  have eq719 : ∀ X0 X2 X3 : G, (M.op X0 X0) ≠ X3 ∨ (k X3 X2) = X2 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq699 X0 x X2 X3
       have i₂ := eq709 x X0
       grind)
    | exact superpose eq709 eq699
    | (have j0 := eq699 X0 x X2 X3
       grind)
    | (have r₁ := eq699 (M.op X0 X0) x X2 (M.op (M.op x x) (M.op X0 X0))
       have r₂ := eq709 X0 (M.op (M.op x x) (M.op X0 X0))
       grind)
    | (have r₁ := eq699 X0 x X2 (M.op (M.op X0 X0) (M.op X0 (M.op (M.op x x) X0)))
       have r₂ := eq709 X0 (M.op X0 (M.op (M.op x x) X0))
       grind)
    | exact resolve eq699 eq709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699 eq709
  have eq829 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (σ (M.op X1 X1))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 (σ (M.op X1 X1))
       have i₂ := eq711 X1 (τ X0)
       grind)
    | exact superpose eq711 eq38
    | exact resolve eq38 eq711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq842 : ∀ X0 X1 : G, (k (σ (σ (M.op X1 X1))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq829 X0 X1
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq829
    | exact resolve eq829 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829
  have eq895 : (M.op x x) = (M.op y x) ∨ (M.op x y) = (k x y) ∨ x = (M.op y y) := by
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
  have eq897 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
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
  have eq911 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X1
       have i₂ := eq698 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq698 X0 X1
       grind)
    | exact superpose eq698 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq698 X0 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq698 X1 X1
       grind)
    | exact resolve eq12 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq924 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq911 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq911
  have eq2036 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) ∨ (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq711 X1 (σ (M.op X1 X1))
       have i₂ := eq924 X0 (σ (M.op X1 X1))
       grind)
    | exact superpose eq924 eq711
    | (have j1 := eq924 X0 (σ (M.op X1 X1))
       grind)
    | exact resolve eq711 eq924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711
  have eq2037 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (σ (M.op X1 X1))) ∨ (M.op X0 X0) = (σ (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq842 (σ (σ (M.op X1 X1))) X1
       have i₂ := eq924 X0 (σ (σ (M.op X1 X1)))
       grind)
    | exact superpose eq924 eq842
    | (have j1 := eq924 X0 (σ (σ (M.op X1 X1)))
       grind)
    | exact resolve eq842 eq924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842
  have eq2046 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq924 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq924
  have eq2053 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq2037 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2037
  have eq2054 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2036 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2036
  have eq2163 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X1 X1
       have i₂ := eq2054 (M.op X1 X1) X0
       grind)
    | exact superpose eq2054 eq16
    | exact resolve eq16 eq2054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2742 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (σ (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2163 X1 (σ (M.op X1 X1))
       have i₂ := eq2053 (σ (M.op X1 X1)) X0
       grind)
    | exact superpose eq2053 eq2163
    | exact resolve eq2163 eq2053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2053 eq2163
  have eq4497 : ∀ X0 X1 : G, (k x (σ (M.op X1 X1))) = (τ (k (σ x) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq44 (σ (M.op X1 X1))
       have i₂ := eq2742 X1 X0
       grind)
    | exact superpose eq2742 eq44
    | exact resolve eq44 eq2742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2742
  have eq4513 : ∀ X0 X1 : G, (k x (σ (M.op X1 X1))) = (k x (M.op X0 X0)) := by
    intro X0 X1
    first
    | exact superpose eq44 eq4497
    | exact resolve eq4497 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq4497
  have eq5203 : ∀ X0 X1 : G, y = (M.op (M.op x (M.op X0 X0)) (M.op (M.op x x) (M.op X1 X1))) ∨ (M.op x y) = (k x y) ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq177 x y X1 X0
       have i₂ := eq895
       grind)
    | exact superpose eq895 eq177
    | exact resolve eq177 eq895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq895
  have eq5212 : (M.op x y) = (k x y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq5203 x x
       have i₂ := eq177 x x x x
       grind)
    | exact superpose eq177 eq5203
    | exact resolve eq5203 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5203
  have eq5218 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ x) (M.op X0 X0)) (M.op (M.op (σ x) (σ x)) (M.op X1 X1))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq897 eq177
    | exact resolve eq177 eq897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq897
  have eq5227 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq5218 x x
       have i₂ := eq177 sF2 sF2 x x
       grind)
    | exact superpose eq177 eq5218
    | exact resolve eq5218 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq5218
  have eq21338 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq5212
       grind)
    | exact superpose eq5212 eq40
    | exact resolve eq40 eq5212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq5212
  have eq21341 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq21338
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq21338
    | exact resolve eq21338 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21338
  have eq21343 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq21341
    | exact resolve eq21341 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21341
  have eq32760 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq21343 eq5227
    | exact resolve eq5227 eq21343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5227 eq21343
  have eq32769 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq32760
       have r₂ := eq27
       grind)
    | exact resolve eq32760 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32760
  have eq33109 : ∀ X0 : G, (k (τ (σ x)) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq32769 eq712
    | exact resolve eq712 eq32769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712 eq32769
  have eq33449 : ∀ X0 : G, (k x X0) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq29 eq33109
    | exact resolve eq33109 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33109
  have eq33527 : ∀ X0 : G, (k x X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq33449 X0
       have j1 := eq719 X0 X0 x
       grind)
    | (have r₁ := eq33449 (M.op X0 X0)
       have r₂ := eq719 X0 x (k x (M.op X0 X0))
       grind)
    | (have r₁ := eq33449 X0
       have r₂ := eq719 y x x
       grind)
    | exact resolve eq33449 eq719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719 eq33449
  have eq33670 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k x (M.op X1 X1)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq4513 X1 X0
       have i₂ := eq33527 (σ (M.op X0 X0))
       grind)
    | exact superpose eq33527 eq4513
    | exact resolve eq4513 eq33527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4513
  have eq33679 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = x ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq2046 X0 x
       have i₂ := eq33527 x
       grind)
    | exact superpose eq33527 eq2046
    | (have j0 := eq2046 X0 x
       grind)
    | (have r₁ := eq2046 X0 x
       have r₂ := eq33527 x
       grind)
    | exact resolve eq2046 eq33527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2046
  have eq33689 : ∀ X0 : G, (M.op X0 X0) = x ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq33679 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33679
  have eq33704 : ∀ X0 : G, (k x x) = (σ (M.op X0 X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq33689 eq33670
    | exact resolve eq33670 eq33689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33670
  have eq33719 : ∀ X0 : G, x = (σ (M.op X0 X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq33527 eq33704
    | exact resolve eq33704 eq33527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33527 eq33704
  have eq33731 : x = (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq33689 eq33719
    | exact resolve eq33719 eq33689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33719
  have eq33738 : (σ x) = (σ y) ∨ x = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq33731
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq33731
    | exact resolve eq33731 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33731
  have eq33741 : y = (τ (σ x)) ∨ x = (σ x) ∨ x = y := by
    first
    | exact superpose eq33738 eq31
    | exact resolve eq31 eq33738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33839 : x = y ∨ x = (σ x) ∨ x = y := by
    first
    | exact superpose eq29 eq33741
    | exact resolve eq33741 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33741
  have eq33840 : x = (σ x) ∨ x = y := by grind
  clear eq33839
  have eq33846 : (M.op x y) = (M.op (σ x) y) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq33840
       grind)
    | exact superpose eq33840 eq18
    | exact resolve eq18 eq33840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33840
  have eq34421 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq16 X0 X0 X0
       have i₂ := eq33689 (M.op X0 X0)
       grind)
    | exact superpose eq33689 eq16
    | exact resolve eq16 eq33689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33689
  have eq34486 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq33738 eq34421
    | exact resolve eq34421 eq33738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33738 eq34421
  have eq35564 : y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq34486 eq33846
    | exact resolve eq33846 eq34486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33846
  have eq35566 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq34486 eq26
    | (have j1 := eq34486 (σ y)
       grind)
    | exact resolve eq26 eq34486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34486
  have eq35798 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq35564
  have eq36471 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq35566 eq27
    | exact resolve eq27 eq35566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35566
  have eq36531 : y = (τ (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq35798 eq31
    | exact resolve eq31 eq35798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35798
  have eq36630 : x = y ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq36531
    | exact resolve eq36531 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36531
  have eq36631 : y = (M.op x y) ∨ x = y := by grind
  clear eq36630
  have eq36669 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq24
       have i₂ := eq36631
       grind)
    | exact superpose eq36631 eq24
    | exact resolve eq24 eq36631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36631
  have eq36720 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq36669
    | exact resolve eq36669 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36669
  have eq36782 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq36720 eq36471
    | (have r₁ := eq36471
       have r₂ := eq36720
       grind)
    | exact resolve eq36471 eq36720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36471 eq36720
  have eq36783 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq36782
  have eq36784 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq36783
  have eq36831 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq36784 eq31
    | exact resolve eq31 eq36784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq36784
  have eq36940 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq36831
    | exact resolve eq36831 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq36831
  have eq36941 : x = y := by grind
  clear eq36940
  have eq36981 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq36941
       grind)
    | exact superpose eq36941 eq18
    | exact resolve eq18 eq36941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq36982 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq36941
       grind)
    | exact superpose eq36941 eq24
    | exact resolve eq24 eq36941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq36941
  have eq37019 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq36982
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq36982
    | exact resolve eq36982 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq36982
  have eq37026 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq37019 eq26
    | exact resolve eq26 eq37019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq37019
  have eq37154 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq698 x X0
       have i₂ := eq36981
       grind)
    | exact superpose eq36981 eq698
    | exact resolve eq698 eq36981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37212 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq2054 X0 x
       have i₂ := eq36981
       grind)
    | exact superpose eq36981 eq2054
    | exact resolve eq2054 eq36981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2054 eq36981
  have eq37463 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq20 eq37212
    | (have j0 := eq37212 X0
       grind)
    | exact resolve eq37212 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq37212
  have eq37576 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq37463 x
       have i₂ := eq37154 x
       grind)
    | exact superpose eq37154 eq37463
    | exact resolve eq37463 eq37154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37463
  have eq38080 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq37026 eq698
    | exact resolve eq698 eq37026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698 eq37026
  have eq38429 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq38080 x
       have i₂ := eq37154 x
       grind)
    | exact superpose eq37154 eq38080
    | exact resolve eq38080 eq37154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37154 eq38080
  have eq38836 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq38429 eq27
    | exact resolve eq27 eq38429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq38429
  have eq38878 : False := by grind
  exact eq38878

/-- `Equation2725`: `x = ((y ◇ x) ◇ (z ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_y_y_x_pxy_Equation2725 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2725 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2725.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X2)) X1) = X0 := by
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
  have eq152 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq72 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq72
    | exact resolve eq72 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq174 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op X0 X0)) x) := by
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
  have eq176 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) (σ x) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op (M.op X1 X0) (M.op X2 X2))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X1 (M.op (M.op X1 X0) (M.op X2 X2)) X3
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X2 X2) (M.op (M.op X1 X1) X0) X1
       have i₂ := eq16 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : ∀ X0 X1 : G, x = (M.op (M.op y (M.op X1 X1)) (M.op (M.op x y) (M.op X0 X0))) := by
    intro X0 X1
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ y) (M.op X1 X1)) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) := by
    intro X0 X1
    first
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq343 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq393 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq38 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq174 (τ X0)
       grind)
    | exact superpose eq174 eq38
    | exact resolve eq38 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq425 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq393 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq393
    | exact resolve eq393 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393
  have eq445 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq343 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq174 (σ X0)
       grind)
    | exact superpose eq174 eq343
    | exact resolve eq343 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq467 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq445 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq445
    | exact resolve eq445 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445
  have eq698 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq178 x x X1
       have i₂ := eq178 x x X0
       grind)
    | exact superpose eq178 eq178
    | exact resolve eq178 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq699 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X1) X0)) ≠ X3 ∨ (k X3 X2) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X3 X2
       have i₂ := eq178 X0 X1 X2
       grind)
    | exact superpose eq178 eq13
    | (have j0 := eq13 X3 X2
       grind)
    | (have r₁ := eq13 (M.op X0 (M.op (M.op X1 X1) X0)) X2
       have r₂ := eq178 X0 X1 X2
       grind)
    | exact resolve eq13 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq706 : ∀ X0 X1 X2 : G, (k (τ (M.op X0 (M.op (M.op X1 X1) X0))) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq467 X2
       have i₂ := eq178 X0 X1 (σ X2)
       grind)
    | exact superpose eq178 eq467
    | exact resolve eq467 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467
  have eq707 : ∀ X0 X1 X2 : G, (k (σ (M.op X0 (M.op (M.op X1 X1) X0))) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq425 X2
       have i₂ := eq178 X0 X1 (τ X2)
       grind)
    | exact superpose eq178 eq425
    | exact resolve eq425 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425
  have eq709 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X1 (M.op X1 X1)
       have i₂ := eq178 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq711 : ∀ X0 X2 : G, (k (σ (M.op X0 X0)) X2) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq707 X0 x X2
       have i₂ := eq709 x X0
       grind)
    | exact superpose eq709 eq707
    | exact resolve eq707 eq709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707
  have eq712 : ∀ X0 X2 : G, (k (τ (M.op X0 X0)) X2) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq706 X0 x X2
       have i₂ := eq709 x X0
       grind)
    | exact superpose eq709 eq706
    | exact resolve eq706 eq709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706
  have eq719 : ∀ X0 X2 X3 : G, (M.op X0 X0) ≠ X3 ∨ (k X3 X2) = X2 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq699 X0 x X2 X3
       have i₂ := eq709 x X0
       grind)
    | exact superpose eq709 eq699
    | (have j0 := eq699 X0 x X2 X3
       grind)
    | (have r₁ := eq699 (M.op X0 X0) x X2 (M.op (M.op x x) (M.op X0 X0))
       have r₂ := eq709 X0 (M.op (M.op x x) (M.op X0 X0))
       grind)
    | (have r₁ := eq699 X0 x X2 (M.op (M.op X0 X0) (M.op X0 (M.op (M.op x x) X0)))
       have r₂ := eq709 X0 (M.op X0 (M.op (M.op x x) X0))
       grind)
    | exact resolve eq699 eq709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699
  have eq792 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X2 X2)) (M.op X1 X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 (M.op X1 X1) X2
       have i₂ := eq709 X1 X0
       grind)
    | exact superpose eq709 eq16
    | exact resolve eq16 eq709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq829 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (σ (M.op X1 X1))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 (σ (M.op X1 X1))
       have i₂ := eq711 X1 (τ X0)
       grind)
    | exact superpose eq711 eq38
    | exact resolve eq38 eq711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq842 : ∀ X0 X1 : G, (k (σ (σ (M.op X1 X1))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq829 X0 X1
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq829
    | exact resolve eq829 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829
  have eq859 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (τ (M.op X1 X1))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq343 (τ (M.op X1 X1)) X0
       have i₂ := eq712 X1 (σ X0)
       grind)
    | exact superpose eq712 eq343
    | exact resolve eq343 eq712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343
  have eq874 : ∀ X0 X1 : G, (k (τ (τ (M.op X1 X1))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq859 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq859
    | exact resolve eq859 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq859
  have eq889 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq896 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 X1
       have i₂ := eq698 X0 X1
       grind)
    | (have i₁ := eq11 X0 X0
       have i₂ := eq698 X0 X1
       grind)
    | exact superpose eq698 eq11
    | (have j0 := eq11 (k X1 X1) X0
       grind)
    | exact resolve eq11 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698
  have eq902 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq903 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq964 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq896 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896
  have eq2206 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) ∨ (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq711 X1 (σ (M.op X1 X1))
       have i₂ := eq964 X0 (σ (M.op X1 X1))
       grind)
    | exact superpose eq964 eq711
    | (have j1 := eq964 X0 (σ (M.op X1 X1))
       grind)
    | exact resolve eq711 eq964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711
  have eq2207 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (σ (M.op X1 X1))) ∨ (M.op X0 X0) = (σ (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq842 (σ (σ (M.op X1 X1))) X1
       have i₂ := eq964 X0 (σ (σ (M.op X1 X1)))
       grind)
    | exact superpose eq964 eq842
    | (have j1 := eq964 X0 (σ (σ (M.op X1 X1)))
       grind)
    | exact resolve eq842 eq964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842
  have eq2210 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) ∨ (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq712 X1 (τ (M.op X1 X1))
       have i₂ := eq964 X0 (τ (M.op X1 X1))
       grind)
    | exact superpose eq964 eq712
    | (have j1 := eq964 X0 (τ (M.op X1 X1))
       grind)
    | exact resolve eq712 eq964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2213 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (τ (M.op X1 X1))) ∨ (M.op X0 X0) = (τ (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq874 (τ (τ (M.op X1 X1))) X1
       have i₂ := eq964 X0 (τ (τ (M.op X1 X1)))
       grind)
    | exact superpose eq964 eq874
    | (have j1 := eq964 X0 (τ (τ (M.op X1 X1)))
       grind)
    | exact resolve eq874 eq964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874
  have eq2217 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq964 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq964
  have eq2221 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq2213 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2213
  have eq2222 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2210 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2210
  have eq2225 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq2207 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2207
  have eq2226 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2206 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2206
  have eq2335 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X1 X1
       have i₂ := eq2226 (M.op X1 X1) X0
       grind)
    | exact superpose eq2226 eq16
    | exact resolve eq16 eq2226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2226
  have eq2454 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (τ (M.op X0 X0))) x) := by
    intro X0
    first
    | (have i₁ := eq175 x
       have i₂ := eq2222 x X0
       grind)
    | exact superpose eq2222 eq175
    | exact resolve eq175 eq2222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2504 : ∀ X0 X1 : G, (M.op (τ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X1 X1
       have i₂ := eq2222 (M.op X1 X1) X0
       grind)
    | exact superpose eq2222 eq16
    | exact resolve eq16 eq2222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2222
  have eq2707 : ∀ X0 X1 : G, (M.op (τ (τ (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2504 (τ (M.op X0 X0)) X1
       have i₂ := eq2504 X0 (τ (M.op X0 X0))
       grind)
    | exact superpose eq2504 eq2504
    | exact resolve eq2504 eq2504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2504
  have eq2908 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (σ (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2335 X1 (σ (M.op X1 X1))
       have i₂ := eq2225 (σ (M.op X1 X1)) X0
       grind)
    | exact superpose eq2225 eq2335
    | exact resolve eq2335 eq2225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2225
  have eq3198 : ∀ X0 X1 X3 : G, (M.op (M.op X1 (τ (τ (M.op X0 X0)))) (M.op X3 X3)) = X1 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq792 X1 X3 x
       have i₂ := eq2221 x X0
       grind)
    | exact superpose eq2221 eq792
    | exact resolve eq792 eq2221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2221
  have eq4557 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq902
       grind)
    | exact superpose eq902 eq40
    | exact resolve eq40 eq902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq4558 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq4557
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4557
    | exact resolve eq4557 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4557
  have eq4560 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq4558
    | exact resolve eq4558 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4558
  have eq4683 : ∀ X0 X1 : G, (k x (σ (M.op X1 X1))) = (τ (k (σ x) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq44 (σ (M.op X1 X1))
       have i₂ := eq2908 X1 X0
       grind)
    | exact superpose eq2908 eq44
    | exact resolve eq44 eq2908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2908
  have eq4701 : ∀ X0 X1 : G, (k x (σ (M.op X1 X1))) = (k x (M.op X0 X0)) := by
    intro X0 X1
    first
    | exact superpose eq44 eq4683
    | exact resolve eq4683 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq4683
  have eq5459 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 (M.op X4 X4)) = (M.op (M.op (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X3 X3)) (M.op X0 (M.op X5 X5))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq177 (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X1 (M.op X4 X4)) X5 X3
       have i₂ := eq177 X1 X0 X2 X4
       grind)
    | exact superpose eq177 eq177
    | exact resolve eq177 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5460 : ∀ X0 X1 X2 : G, (M.op (M.op x y) (M.op X1 X1)) = (M.op (M.op x (M.op X0 X0)) (M.op y (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | exact superpose eq175 eq177
    | exact resolve eq177 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5544 : ∀ X0 X1 X4 X5 : G, (M.op X1 (M.op X4 X4)) = (M.op (M.op X0 X1) (M.op X0 (M.op X5 X5))) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq5459 X0 X1 x x X4 X5
       have i₂ := eq792 (M.op X0 X1) x x
       grind)
    | exact superpose eq792 eq5459
    | exact resolve eq5459 eq792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq792 eq5459
  have eq22439 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq4560 eq903
    | exact resolve eq903 eq4560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903 eq4560
  have eq22450 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq22439
       have r₂ := eq27
       grind)
    | exact resolve eq22439 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22439
  have eq22478 : ∀ X0 : G, (k (τ (σ x)) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq22450 eq712
    | exact resolve eq712 eq22450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22450
  have eq22748 : ∀ X0 : G, (k x X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq29 eq22478
    | exact resolve eq22478 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22478
  have eq22811 : ∀ X0 : G, (k x X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq22748 X0
       have j1 := eq719 X0 X0 x
       grind)
    | (have r₁ := eq22748 (M.op X0 X0)
       have r₂ := eq719 X0 x (k x (M.op X0 X0))
       grind)
    | (have r₁ := eq22748 X0
       have r₂ := eq719 y x x
       grind)
    | exact resolve eq22748 eq719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22748
  have eq22906 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k x (M.op X1 X1)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq4701 X1 X0
       have i₂ := eq22811 (σ (M.op X0 X0))
       grind)
    | exact superpose eq22811 eq4701
    | exact resolve eq4701 eq22811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22917 : ∀ X0 : G, x ≠ x ∨ x = (M.op X0 X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq2217 X0 x
       have i₂ := eq22811 x
       grind)
    | exact superpose eq22811 eq2217
    | (have j0 := eq2217 X0 x
       grind)
    | (have r₁ := eq2217 X0 x
       have r₂ := eq22811 x
       grind)
    | exact resolve eq2217 eq22811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22929 : ∀ X0 : G, x = (M.op X0 X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq22917 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22917
  have eq22943 : ∀ X0 : G, (k x x) = (σ (M.op X0 X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq22929 eq22906
    | exact resolve eq22906 eq22929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22906
  have eq22958 : ∀ X0 : G, x = (σ (M.op X0 X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq22811 eq22943
    | exact resolve eq22943 eq22811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22811 eq22943
  have eq22970 : x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq22929 eq22958
    | exact resolve eq22958 eq22929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22958
  have eq22977 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq22970
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq22970
    | exact resolve eq22970 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22970
  have eq23272 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16 X0 X0 X0
       have i₂ := eq22929 (M.op X0 X0)
       grind)
    | exact superpose eq22929 eq16
    | exact resolve eq16 eq22929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22929
  have eq23334 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq22977 eq23272
    | (have j0 := eq23272 y
       grind)
    | exact resolve eq23272 eq22977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22977 eq23272
  have eq24125 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq23334 eq26
    | (have j1 := eq23334 (σ y)
       grind)
    | exact resolve eq26 eq23334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23334
  have eq24315 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq24125
  have eq24469 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ y) (M.op X0 X0)) (M.op (σ y) (M.op X1 X1))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq24315 eq192
    | exact resolve eq192 eq24315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq24470 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq24315 eq889
    | (have r₁ := eq889
       have r₂ := eq24315
       grind)
    | exact resolve eq889 eq24315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq889 eq24315
  have eq24477 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq24470
  have eq26263 : (τ (σ x)) = (k (τ (σ x)) y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq24477 eq152
    | exact resolve eq152 eq24477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq24477
  have eq26278 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq26263
    | exact resolve eq26263 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26263
  have eq26306 : ∀ X0 : G, (k (τ (σ x)) X0) = X0 ∨ x = (k x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26278 eq712
    | exact resolve eq712 eq26278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712 eq26278
  have eq26555 : ∀ X0 : G, x = (k x y) ∨ (k x X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29 eq26306
    | exact resolve eq26306 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26306
  have eq27610 : ∀ X0 : G, x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (k x X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq902
       have i₂ := eq26555 X0
       grind)
    | exact superpose eq26555 eq902
    | (have j1 := eq26555 X0
       grind)
    | exact resolve eq902 eq26555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq902 eq26555
  have eq27618 : ∀ X0 : G, x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (k x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq27610 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27610
  have eq27624 : ∀ X0 : G, (k x X0) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq27618 X0
       have j1 := eq719 X0 X0 x
       grind)
    | (have r₁ := eq27618 X0
       have r₂ := eq719 y x x
       grind)
    | (have r₁ := eq27618 (M.op X0 X0)
       have r₂ := eq719 X0 x (k x (M.op X0 X0))
       grind)
    | exact resolve eq27618 eq719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719 eq27618
  have eq27650 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k x (M.op X1 X1)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq4701 X1 X0
       have i₂ := eq27624 (σ (M.op X0 X0))
       grind)
    | exact superpose eq27624 eq4701
    | exact resolve eq4701 eq27624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4701
  have eq27667 : ∀ X0 : G, x ≠ x ∨ x = (M.op X0 X0) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq2217 X0 x
       have i₂ := eq27624 x
       grind)
    | exact superpose eq27624 eq2217
    | (have j0 := eq2217 X0 x
       grind)
    | (have r₁ := eq2217 X0 x
       have r₂ := eq27624 x
       grind)
    | exact resolve eq2217 eq27624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2217
  have eq27679 : ∀ X0 : G, x = (M.op X0 X0) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq27667 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27667
  have eq27706 : ∀ X0 : G, (k x x) = (σ (M.op X0 X0)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq27679 eq27650
    | exact resolve eq27650 eq27679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27650
  have eq27722 : ∀ X0 : G, x = (σ (M.op X0 X0)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq27624 eq27706
    | exact resolve eq27706 eq27624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27624 eq27706
  have eq27734 : x = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27679 eq27722
    | exact resolve eq27722 eq27679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27722
  have eq27741 : y = (M.op x y) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq27734
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq27734
    | exact resolve eq27734 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27734
  have eq28199 : y = (M.op (M.op (M.op x y) x) x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq175 x
       have i₂ := eq27679 x
       grind)
    | exact superpose eq27679 eq175
    | exact resolve eq175 eq27679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq28429 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X1)) x) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq177 X0 X0 X0 X1
       have i₂ := eq27679 (M.op X0 X0)
       grind)
    | exact superpose eq27679 eq177
    | exact resolve eq177 eq27679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq28513 : ∀ X0 : G, (M.op (M.op X0 x) x) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq27679 eq28429
    | exact resolve eq28429 eq27679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27679 eq28429
  have eq28718 : y = (M.op (M.op (M.op x y) (σ x)) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27741 eq28199
    | exact resolve eq28199 eq27741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28199
  have eq28766 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ x)) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq27741 eq28513
    | exact resolve eq28513 eq27741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27741 eq28513
  have eq34053 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28766 eq28718
    | exact resolve eq28718 eq28766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28718 eq28766
  have eq34068 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq34053
  have eq60568 : y = (M.op (M.op (M.op x y) (τ (σ x))) x) ∨ y = (M.op x y) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f60568_13 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (τ (M.op X0 X0))) x) := by
      intro X0
      grind
    have f60568_14 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ y) (M.op X0 X0)) (M.op (σ y) (M.op X1 X1))) ∨ y = (M.op x y) := by
      intro X0 X1
      grind
    have f60568_23 : y ≠ (M.op (M.op (M.op x y) (τ (σ x))) x) := by grind
    have f60568_24 : y ≠ (M.op x y) := by grind
    have f60568_26 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ y) (M.op X0 X0)) (M.op (σ y) (M.op X1 X1))) := by
      intro X0 X1
      first
      | (have j0 := f60568_14 X0 X1
         grind)
      | (have r₁ := f60568_14 X0 X1
         have r₂ := f60568_24
         grind)
      | exact resolve f60568_14 f60568_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f60568_73 : y = (M.op (M.op (M.op x y) (τ (σ x))) x) := by
      first
      | (have i₁ := f60568_13 (M.op (σ y) (M.op x x))
         have i₂ := f60568_26 x x
         grind)
      | exact superpose f60568_26 f60568_13
      | exact resolve f60568_13 f60568_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f60568_79 : False := by
      first
      | (have r₁ := f60568_73
         have r₂ := f60568_23
         grind)
      | exact resolve f60568_73 f60568_23
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f60568_79
  clear eq2454 eq24469
  have eq60905 : y = (M.op (M.op (M.op x y) x) x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq60568
    | exact resolve eq60568 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq60568
  have eq61107 : y = (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq34068 eq60905
    | exact resolve eq60905 eq34068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34068 eq60905
  have eq61237 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq61107
       have i₂ := eq709 sF0 sF0
       grind)
    | exact superpose eq709 eq61107
    | exact resolve eq61107 eq709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61107
  have eq61238 : y = (M.op x y) := by grind
  clear eq61237
  have eq61310 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq61238
       grind)
    | exact superpose eq61238 eq18
    | exact resolve eq18 eq61238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq61311 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq61238
       grind)
    | exact superpose eq61238 eq24
    | exact resolve eq24 eq61238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq61331 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq61311 eq20
    | exact resolve eq20 eq61311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq61311
  have eq61488 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) (M.op X0 X0)) x) := by
    intro X0
    first
    | exact superpose eq61310 eq16
    | exact resolve eq16 eq61310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61310
  have eq66967 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) (τ (τ (M.op X0 X0)))) x) := by
    intro X0
    first
    | (have i₁ := eq61488 (τ (τ (M.op X0 X0)))
       have i₂ := eq2707 X0 (τ (τ (M.op X0 X0)))
       grind)
    | exact superpose eq2707 eq61488
    | exact resolve eq61488 eq2707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2707 eq61488
  have eq74922 : ∀ X0 X1 X2 : G, (M.op x (M.op X0 X0)) = (M.op (M.op x y) (M.op (M.op (M.op x y) (τ (τ (M.op X1 X1)))) (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | exact superpose eq66967 eq5544
    | exact resolve eq5544 eq66967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66967
  have eq75590 : ∀ X0 X1 X3 : G, x = (M.op (M.op (M.op X0 y) (M.op X0 (M.op X1 X1))) (M.op (M.op x y) (M.op X3 X3))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq191 X3 x
       have i₂ := eq5544 X0 y x X1
       grind)
    | exact superpose eq5544 eq191
    | exact resolve eq191 eq5544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq76132 : ∀ X0 X1 X3 : G, x = (M.op (M.op (M.op X0 (M.op x y)) (M.op X0 (M.op X1 X1))) (M.op (M.op x y) (M.op X3 X3))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq75590 X0 X1 X3
       have i₂ := eq61238
       grind)
    | exact superpose eq61238 eq75590
    | exact resolve eq75590 eq61238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75590
  have eq76256 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op x (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq74922 X0 X0 x
       have i₂ := eq3198 X0 sF0 x
       grind)
    | exact superpose eq3198 eq74922
    | exact resolve eq74922 eq3198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3198 eq74922
  have eq76683 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X2) (M.op X3 X3)) = (M.op (M.op (M.op x (M.op X0 X0)) (M.op y (M.op X1 X1))) (M.op (M.op x y) (M.op X4 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq5460 eq5544
    | exact resolve eq5544 eq5460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5460 eq5544
  have eq76714 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X2) (M.op X3 X3)) = (M.op (M.op (M.op x (M.op X0 X0)) (M.op (M.op x y) (M.op X1 X1))) (M.op (M.op x y) (M.op X4 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq76683 X0 X1 X2 X3 X4
       have i₂ := eq61238
       grind)
    | exact superpose eq61238 eq76683
    | exact resolve eq76683 eq61238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61238 eq76683
  have eq76840 : ∀ X1 X2 X3 X4 : G, (M.op (M.op X2 X2) (M.op X3 X3)) = (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op X1 X1))) (M.op (M.op x y) (M.op X4 X4))) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq76714 x X1 X2 X3 X4
       have i₂ := eq76256 x
       grind)
    | exact superpose eq76256 eq76714
    | exact resolve eq76714 eq76256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76256 eq76714
  have eq76937 : ∀ X2 X3 : G, x = (M.op (M.op X2 X2) (M.op X3 X3)) := by
    intro X2 X3
    first
    | exact superpose eq76132 eq76840
    | exact resolve eq76840 eq76132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76132 eq76840
  have eq76961 : ∀ X3 : G, x = (M.op X3 X3) := by
    intro X3
    first
    | (have i₁ := eq76937 x X3
       have i₂ := eq709 x (M.op X3 X3)
       grind)
    | exact superpose eq709 eq76937
    | exact resolve eq76937 eq709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709 eq76937
  have eq77196 : ∀ X1 : G, (M.op (σ x) X1) = X1 := by
    intro X1
    first
    | (have i₁ := eq2335 x X1
       have i₂ := eq76961 x
       grind)
    | exact superpose eq76961 eq2335
    | exact resolve eq2335 eq76961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2335 eq76961
  have eq77609 : ∀ X1 : G, (M.op (σ x) X1) = X1 := by
    intro X1
    first
    | (have i₁ := eq77196 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq77196
    | (have j0 := eq77196 X1
       grind)
    | exact resolve eq77196 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq77196
  have eq79459 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq77609 eq26
    | (have j1 := eq77609 (σ y)
       grind)
    | exact resolve eq26 eq77609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq77609
  have eq80101 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq79459 eq27
    | exact resolve eq27 eq79459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq79459
  have eq80122 : False := by grind
  exact eq80122

/-- `Equation2725`: `x = ((y ◇ x) ◇ (z ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = m(Y,X) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyx_pxy_pxx_pxy_Equation2725 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2725 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2725.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X2)) X1) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op (M.op X1 X0) (M.op X2 X2))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 (M.op (M.op X1 X0) (M.op X2 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X2 X2) (M.op (M.op X1 X1) X0) X1
       have i₂ := eq9 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq42 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq42 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq42 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq56 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq56 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq56
    | (have j0 := eq56 (σ X0) (σ X1)
       grind)
    | exact resolve eq56 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq43 (τ X0)
       grind)
    | exact superpose eq43 eq18
    | exact resolve eq18 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq83 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq82 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq82
    | exact resolve eq82 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq91 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq83 X0
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq83
    | exact resolve eq83 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq83
  have eq95 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq91 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq91
    | exact resolve eq91 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X0 (M.op X0 X0) X1
       have i₂ := eq9 X0 X0 X0
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X2 (M.op X0 (M.op X1 X1))) (M.op X3 X3))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq23 (M.op X0 (M.op X1 X1)) X2 X3 (M.op X0 X0)
       have i₂ := eq23 X0 X0 X0 X1
       grind)
    | exact superpose eq23 eq23
    | exact resolve eq23 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X0) (M.op X3 X3)) = (M.op (M.op X1 (M.op X2 X2)) (M.op X0 (M.op X4 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq23 X1 (M.op (M.op X1 X0) (M.op X3 X3)) X4 X2
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq23
    | exact resolve eq23 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X2)) (M.op X0 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 X1 X1 (M.op X1 X1) X2
       have i₂ := eq24 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq24 eq23
    | exact resolve eq23 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq160 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq67 x y
       grind)
    | exact superpose eq67 eq16
    | (have j1 := eq67 x y
       grind)
    | exact resolve eq16 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq236 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq91 X1
       have i₂ := eq105 X0 (τ X1)
       grind)
    | (have i₁ := eq91 X1
       have i₂ := eq105 (τ X1) X0
       grind)
    | exact superpose eq105 eq91
    | exact resolve eq91 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq105
  have eq715 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq160
       have i₂ := eq95 x
       grind)
    | exact superpose eq95 eq160
    | exact resolve eq160 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq160
  have eq716 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op x x)) ∨ (M.op x x) = (M.op y x) := by
    first
    | (have i₁ := eq715
       have i₂ := eq56 x y
       grind)
    | exact superpose eq56 eq715
    | (have j1 := eq56 x y
       grind)
    | exact resolve eq715 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq715
  have eq717 : (M.op x x) = (M.op y x) ∨ (M.op (σ y) (σ x)) = (σ (M.op x x)) := by grind
  clear eq716
  have eq2070 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X1)) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq125 (M.op X0 X1) X1 x X2 x
       have i₂ := eq23 X1 X0 x x
       grind)
    | exact superpose eq23 eq125
    | exact resolve eq125 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2089 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X0 (M.op X1 X1)) (M.op (M.op X2 (M.op X3 X3)) (M.op X4 X4)))) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq122 X2 X3 X0 x
       have i₂ := eq125 (M.op X2 (M.op X3 X3)) X0 X1 x X4
       grind)
    | (have i₁ := eq122 (M.op X1 X1) X1 X1 (M.op X4 X4)
       have i₂ := eq125 (M.op X4 X4) X1 (M.op X1 X1) X3 X4
       grind)
    | exact superpose eq125 eq122
    | exact resolve eq122 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2145 : ∀ X0 X1 X2 X3 X5 : G, (M.op X0 (M.op X3 X3)) = (M.op X1 (M.op (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X5 X5))) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq122 X1 x (M.op X0 (M.op X3 X3)) X5
       have i₂ := eq125 X1 X0 X3 X2 x
       grind)
    | (have i₁ := eq122 (M.op X1 X1) X1 (M.op X1 X0) X3
       have i₂ := eq125 X0 X1 X2 (M.op X1 X1) x
       grind)
    | exact superpose eq125 eq122
    | exact resolve eq122 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq125
  have eq2223 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X3 X3)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq2145 X0 X1 x X3 x
       have i₂ := eq131 x (M.op X0 X1) x
       grind)
    | exact superpose eq131 eq2145
    | exact resolve eq2145 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2145
  have eq2238 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 (M.op X1 X1)) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2089 X0 X1 X2 x x
       have i₂ := eq131 x X2 x
       grind)
    | exact superpose eq131 eq2089
    | exact resolve eq2089 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq2089
  have eq4436 : ∀ X0 X1 : G, y = (M.op (M.op x (M.op X0 X0)) (M.op (M.op x x) (M.op X1 X1))) ∨ (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 x y X1 X0
       have i₂ := eq717
       grind)
    | exact superpose eq717 eq23
    | exact resolve eq23 eq717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717
  have eq4446 : x = y ∨ (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq4436 x x
       have i₂ := eq23 x x x x
       grind)
    | exact superpose eq23 eq4436
    | exact resolve eq4436 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq4436
  have eq8043 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X1)) (σ (M.op X0 X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2070 X2 X1 x
       have i₂ := eq236 X0 x
       grind)
    | exact superpose eq236 eq2070
    | exact resolve eq2070 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2070
  have eq8147 : ∀ X0 X1 X3 : G, (M.op X1 (σ (M.op X0 X0))) = (M.op X3 (M.op X1 X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq2223 X1 X3 x
       have i₂ := eq236 X0 x
       grind)
    | exact superpose eq236 eq2223
    | exact resolve eq2223 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2223
  have eq8603 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 (σ (M.op X0 X0))) X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2238 X2 x X1
       have i₂ := eq236 X0 x
       grind)
    | exact superpose eq236 eq2238
    | exact resolve eq2238 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2238
  have eq69890 : ∀ X0 X1 X3 : G, (M.op X3 (M.op (M.op X1 (M.op X0 X1)) X3)) = X0 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq8147 x (M.op X1 (M.op X0 X1)) X3
       have i₂ := eq8043 x X1 X0
       grind)
    | exact superpose eq8043 eq8147
    | exact resolve eq8147 eq8043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8043 eq8147
  have eq217139 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4446
       grind)
    | exact superpose eq4446 eq16
    | exact resolve eq16 eq4446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4446
  have eq217140 : (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq217139
       have r₂ := eq236 x (σ x)
       grind)
    | exact resolve eq217139 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217139
  have eq217207 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (M.op (σ x) (σ (M.op x x))) X0)) := by
    intro X0
    first
    | (have i₁ := eq69890 (σ y) (σ x) X0
       have i₂ := eq217140
       grind)
    | exact superpose eq217140 eq69890
    | exact resolve eq69890 eq217140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69890 eq217140
  have eq217212 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq217207 x
       have i₂ := eq8603 x x (σ x)
       grind)
    | exact superpose eq8603 eq217207
    | exact resolve eq217207 eq8603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8603 eq217207
  have eq217319 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq217212
       grind)
    | exact superpose eq217212 eq10
    | exact resolve eq10 eq217212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217212
  have eq217599 : x = y := by
    first
    | (have i₁ := eq217319
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq217319
    | exact resolve eq217319 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217319
  have eq218386 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq217599
       grind)
    | exact superpose eq217599 eq16
    | exact resolve eq16 eq217599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217599
  have eq218389 : False := by grind
  exact eq218389
