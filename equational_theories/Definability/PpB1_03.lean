import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1437`: `x = (x ◇ x) ◇ (y ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_x_pyx_x_pyx_Equation1437 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1437 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1437.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
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
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq30 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq73 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq74 : ∀ X0 X1 : G, (σ X1) = (M.op X0 (σ X1)) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq30 X1 X0
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq30
    | (have j1 := eq14 (σ X1) X0
       grind)
    | exact resolve eq30 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq252 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq73 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq4888 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k (σ X0) X1) ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) ∨ (M.op X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) X0
       have i₂ := eq74 X0 X1
       grind)
    | exact superpose eq74 eq13
    | (have j0 := eq13 (σ X0) X1
       have j1 := eq74 X1 X0
       grind)
    | (have r₁ := eq13 (σ X1) X0
       have r₂ := eq74 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq74 (σ X1) X1
       grind)
    | exact resolve eq13 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4911 : ∀ X0 X1 : G, (σ X1) ≠ X0 ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq74 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq4913 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) X1) ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) ∨ (M.op X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq4888 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4888
  have eq4922 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) X1) ∨ (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) ∨ (M.op X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq4913 X0 X1
       have j1 := eq4911 X1 X0
       grind)
    | (have r₁ := eq4913 X1 X1
       have r₂ := eq4911 (k (σ X1) X1) X1
       grind)
    | (have r₁ := eq4913 X1 X0
       have r₂ := eq4911 X0 X1
       grind)
    | (have r₁ := eq4913 X0 (σ X1)
       have r₂ := eq4911 (σ X0) X1
       grind)
    | exact resolve eq4913 eq4911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4913
  have eq5901 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4911 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4911
    | (have r₁ := eq4911 X0 (τ X0)
       have r₂ := eq11 X0
       grind)
    | (have r₁ := eq4911 (σ (τ (σ X1))) X1
       have r₂ := eq11 (σ X1)
       grind)
    | exact resolve eq4911 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4911
  have eq5922 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5901 X0 X1
       have i₂ := eq34 X1 X0
       grind)
    | exact superpose eq34 eq5901
    | (have j0 := eq5901 X0 X1
       grind)
    | (have r₁ := eq5901 (k (τ X1) (τ X0)) (τ (k X1 X0))
       have r₂ := eq34 X0 X1
       grind)
    | (have r₁ := eq5901 (τ (k X1 X0)) (k (τ X1) (τ X0))
       have r₂ := eq34 X0 X1
       grind)
    | exact resolve eq5901 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5901
  have eq5923 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq5922 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5922
  have eq6036 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq5923 X0
       grind)
    | exact superpose eq5923 eq11
    | (have j1 := eq5923 X0
       grind)
    | exact resolve eq11 eq5923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5923
  have eq6145 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq6036 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq6036
    | (have j0 := eq6036 X0
       grind)
    | exact resolve eq6036 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6036
  have eq6159 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq6145 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq6145 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq6145 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6145
  have eq6208 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq6159 (σ X0)
       grind)
    | exact superpose eq6159 eq15
    | exact resolve eq15 eq6159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6279 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq6208 X0
       have i₂ := eq6159 X0
       grind)
    | exact superpose eq6159 eq6208
    | exact resolve eq6208 eq6159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6159 eq6208
  have eq42278 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4922 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4922
    | exact resolve eq4922 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4922
  have eq42535 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq42278 X0 X1
       have i₂ := eq34 X1 X0
       grind)
    | exact superpose eq34 eq42278
    | (have j0 := eq42278 X0 X1
       grind)
    | exact resolve eq42278 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq42278
  have eq42976 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ (k X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq42535 X1 X0
       grind)
    | exact superpose eq42535 eq11
    | (have j1 := eq42535 X1 X0
       grind)
    | exact resolve eq11 eq42535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42535
  have eq43134 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq42976 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq42976
    | (have j0 := eq42976 X0 X1
       grind)
    | exact resolve eq42976 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42976
  have eq43158 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq43134 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq43134 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq43134 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43134
  have eq43271 : ∀ X0 X1 : G, (k X1 (σ X0)) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 X0
       have i₂ := eq43158 (σ X0) X1
       grind)
    | exact superpose eq43158 eq24
    | (have j1 := eq43158 (σ X0) X1
       grind)
    | exact resolve eq24 eq43158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq43409 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq43158 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43941 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 (σ X1)
       have i₂ := eq43271 X1 (σ X0)
       grind)
    | exact superpose eq43271 eq30
    | (have j1 := eq43271 X1 (σ X0)
       grind)
    | exact resolve eq30 eq43271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq43271
  have eq44029 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq43941 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq43941
    | (have j0 := eq43941 X0 X1
       grind)
    | exact resolve eq43941 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43941
  have eq44087 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq44029 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq44029
    | (have j0 := eq44029 X0 X1
       grind)
    | exact resolve eq44029 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44029
  have eq44115 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X1) (σ X0))) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq44087 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq44087
    | (have j0 := eq44087 X0 X1
       grind)
    | exact resolve eq44087 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44087
  have eq44755 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X1) (σ X0))
       have i₂ := eq44115 X0 X1
       grind)
    | exact superpose eq44115 eq11
    | (have j1 := eq44115 X0 X1
       grind)
    | exact resolve eq11 eq44115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44115
  have eq45596 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq44755 y x
       grind)
    | exact superpose eq44755 eq16
    | (have j1 := eq44755 y x
       grind)
    | exact resolve eq16 eq44755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44755
  have eq46044 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq45596
       have i₂ := eq43158 x y
       grind)
    | exact superpose eq43158 eq45596
    | (have j1 := eq43158 x y
       grind)
    | exact resolve eq45596 eq43158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43158
  have eq46045 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq45596
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq45596
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq45596 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45596
  have eq46049 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq46045
  have eq46050 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq46049
  have eq46051 : y = (M.op x y) ∨ y = (k y x) := by grind
  clear eq46044
  have eq46053 : y = (k y x) := by
    first
    | (have j1 := eq43409 y x
       grind)
    | (have r₁ := eq46051
       have r₂ := eq43409 y x
       grind)
    | exact resolve eq46051 eq43409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43409 eq46051
  have eq46489 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq252 x y
       have i₂ := eq46053
       grind)
    | exact superpose eq46053 eq252
    | (have j0 := eq252 x y
       grind)
    | exact resolve eq252 eq46053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252
  have eq46511 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq46489
  have eq78805 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq46511
       grind)
    | exact superpose eq46511 eq16
    | exact resolve eq16 eq46511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46511
  have eq79243 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq78805
       have i₂ := eq46050
       grind)
    | exact superpose eq46050 eq78805
    | exact resolve eq78805 eq46050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46050 eq78805
  have eq79244 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq79243
  have eq79262 : x ≠ x ∨ x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq79244
       grind)
    | exact superpose eq79244 eq12
    | (have r₁ := eq12 y x
       have r₂ := eq79244
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq79244
       grind)
    | exact resolve eq12 eq79244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79244
  have eq79298 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq79262
  have eq79307 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq79298
       have i₂ := eq46053
       grind)
    | exact superpose eq46053 eq79298
    | exact resolve eq79298 eq46053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79298
  have eq79621 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq79307
       grind)
    | exact superpose eq79307 eq16
    | exact resolve eq16 eq79307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79307
  have eq79695 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq79621
       have r₂ := eq6279 x
       grind)
    | exact resolve eq79621 eq6279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79621
  have eq79732 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq79695
       grind)
    | exact superpose eq79695 eq12
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq79695
       grind)
    | exact resolve eq12 eq79695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79695
  have eq79768 : (σ x) = (k (σ y) (σ x)) := by grind
  clear eq79732
  have eq79787 : (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq79768
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq79768
    | exact resolve eq79768 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79768
  have eq79810 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq79787
       have i₂ := eq46053
       grind)
    | exact superpose eq46053 eq79787
    | exact resolve eq79787 eq46053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46053 eq79787
  have eq80901 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq79810
       grind)
    | exact superpose eq79810 eq10
    | exact resolve eq10 eq79810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79810
  have eq81117 : x = y := by
    first
    | (have i₁ := eq80901
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq80901
    | exact resolve eq80901 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80901
  have eq81182 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq81117
       grind)
    | exact superpose eq81117 eq16
    | exact resolve eq16 eq81117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81117
  have eq81268 : False := by grind
  exact eq81268

/-- `Equation1437`: `x = (x ◇ x) ◇ (y ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_pyx_pxx_pyx_Equation1437 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1437 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1437.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ X0 ≠ X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
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
  have eq25 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq35 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25
    | exact resolve eq25 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq56 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq84 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq182 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq56 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq56
    | exact resolve eq56 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq193 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq182 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq182
    | (have j0 := eq182 X0
       grind)
    | exact resolve eq182 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq182
  have eq196 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq193 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq193
    | (have j0 := eq193 X0
       grind)
    | exact resolve eq193 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq197 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq196 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq196 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq196 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq204 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq197 (σ X0)
       grind)
    | exact superpose eq197 eq15
    | exact resolve eq15 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq204 X0
       have i₂ := eq197 X0
       grind)
    | exact superpose eq197 eq204
    | exact resolve eq204 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197 eq204
  have eq315 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq84 x y
       grind)
    | exact superpose eq84 eq16
    | (have j1 := eq84 x y
       grind)
    | exact resolve eq16 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq322 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq84 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq1059 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq86 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq86
    | exact resolve eq86 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq1104 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1059 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1059
    | (have j0 := eq1059 X0 X1
       grind)
    | exact resolve eq1059 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1059
  have eq1215 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq322 (τ X1) (τ X0)
       have i₂ := eq35 X1 X0
       grind)
    | exact superpose eq35 eq322
    | (have j0 := eq322 (τ X0) (τ X1)
       grind)
    | exact resolve eq322 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq1223 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1215 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1215
    | (have j0 := eq1215 X0 X1
       grind)
    | exact resolve eq1215 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1215
  have eq1226 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1223 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1223
    | (have j0 := eq1223 X0 X1
       grind)
    | exact resolve eq1223 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1223
  have eq1228 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1226 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1226
    | (have j0 := eq1226 X0 X1
       grind)
    | exact resolve eq1226 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1226
  have eq1229 : ∀ X0 X1 : G, X0 = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1228 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1228
    | (have j0 := eq1228 X0 X1
       grind)
    | exact resolve eq1228 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1228
  have eq1230 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ X0 = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1229 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1229
    | (have j0 := eq1229 X0 X1
       grind)
    | exact resolve eq1229 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1229
  have eq1231 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1230 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1230
    | (have j0 := eq1230 X0 X1
       grind)
    | exact resolve eq1230 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1230
  have eq1772 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq315
       have i₂ := eq1104 y x
       grind)
    | exact superpose eq1104 eq315
    | (have j1 := eq1104 (σ x) (σ y)
       grind)
    | (have r₁ := eq315
       have r₂ := eq1104 y x
       grind)
    | (have r₁ := eq315
       have r₂ := eq1104 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq315
       have r₂ := eq1104 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq315 eq1104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315 eq1104
  have eq1773 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq1772
  have eq11280 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1773
       grind)
    | exact superpose eq1773 eq16
    | exact resolve eq16 eq1773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1773
  have eq11281 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq11280
       have r₂ := eq215 x
       grind)
    | exact resolve eq11280 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11280
  have eq11283 : x ≠ x ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq11281
       grind)
    | exact superpose eq11281 eq12
    | (have r₁ := eq12 y x
       have r₂ := eq11281
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq11281
       grind)
    | exact resolve eq12 eq11281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11281
  have eq11299 : x = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq11283
  have eq11354 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq322 x y
       have i₂ := eq11299
       grind)
    | exact superpose eq11299 eq322
    | (have j0 := eq322 x y
       grind)
    | exact resolve eq322 eq11299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322 eq11299
  have eq11371 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq11354
  have eq11372 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq11371
  have eq11380 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11372
       grind)
    | exact superpose eq11372 eq16
    | exact resolve eq16 eq11372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11387 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq11372
       grind)
    | exact superpose eq11372 eq12
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq11372
       grind)
    | exact resolve eq12 eq11372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11372
  have eq11403 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq11387
  have eq11410 : (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq11403
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq11403
    | exact resolve eq11403 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11403
  have eq11470 : y = (τ (σ x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq11410
       grind)
    | exact superpose eq11410 eq10
    | exact resolve eq10 eq11410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11410
  have eq11551 : x = y ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq11470
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq11470
    | exact resolve eq11470 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11470
  have eq11698 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11551
       grind)
    | exact superpose eq11551 eq16
    | exact resolve eq16 eq11551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11551
  have eq11699 : (σ x) = (σ (k y x)) := by
    first
    | (have r₁ := eq11698
       have r₂ := eq215 x
       grind)
    | exact resolve eq11698 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11698
  have eq11710 : (k y x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq11699
       grind)
    | exact superpose eq11699 eq10
    | exact resolve eq10 eq11699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11699
  have eq11793 : x = (k y x) := by
    first
    | (have i₁ := eq11710
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq11710
    | exact resolve eq11710 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11710
  have eq11930 : x ≠ x ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1231 y x
       have i₂ := eq11793
       grind)
    | exact superpose eq11793 eq1231
    | (have j0 := eq1231 x y
       grind)
    | (have r₁ := eq1231 y x
       have r₂ := eq11793
       grind)
    | exact resolve eq1231 eq11793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1231 eq11793
  have eq11936 : x = y ∨ x = (M.op x y) := by grind
  clear eq11930
  have eq11941 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11936
       grind)
    | exact superpose eq11936 eq16
    | exact resolve eq16 eq11936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11936
  have eq11946 : x = (M.op x y) := by
    first
    | (have r₁ := eq11941
       have r₂ := eq215 x
       grind)
    | exact resolve eq11941 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11941
  have eq12059 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq11380
       have i₂ := eq11946
       grind)
    | exact superpose eq11946 eq11380
    | exact resolve eq11380 eq11946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11380 eq11946
  have eq12079 : (σ x) = (σ y) := by grind
  clear eq12059
  have eq12081 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq12079
       grind)
    | exact superpose eq12079 eq10
    | exact resolve eq10 eq12079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12079
  have eq12162 : x = y := by
    first
    | (have i₁ := eq12081
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq12081
    | exact resolve eq12081 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12081
  have eq12286 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12162
       grind)
    | exact superpose eq12162 eq16
    | exact resolve eq16 eq12162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12162
  have eq12292 : False := by grind
  exact eq12292

/-- `Equation1437`: `x = (x ◇ x) ◇ (y ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pyx_pxy_pyx_Equation1437 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1437 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1437.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
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
  have eq85 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq85 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq85 X0 X1
       grind)
    | exact superpose eq85 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq85 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq85 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq85 X0 X1
       grind)
    | exact resolve eq13 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq197 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq183 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq198 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq197 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq202 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq198 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq198
    | (have j0 := eq198 X0 X1
       grind)
    | exact resolve eq198 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq203 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq202 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq583 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq203 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq203
    | exact resolve eq203 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq597 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq203 x y
       grind)
    | exact superpose eq203 eq16
    | (have j1 := eq203 x y
       grind)
    | exact resolve eq16 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq618 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq583 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq583
    | (have j0 := eq583 X0 X1
       grind)
    | exact resolve eq583 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq583
  have eq619 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq618 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq618
    | exact resolve eq618 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618
  have eq680 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq619 (τ X1) X0
       grind)
    | exact superpose eq619 eq18
    | (have j1 := eq619 (τ X1) X0
       grind)
    | exact resolve eq18 eq619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq619
  have eq857 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq680 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq680
    | exact resolve eq680 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680
  have eq903 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq857 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq857
    | (have j0 := eq857 X0 X1
       grind)
    | exact resolve eq857 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857
  have eq1014 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq597
       have i₂ := eq903 y x
       grind)
    | exact superpose eq903 eq597
    | (have j1 := eq903 (σ y) (σ x)
       grind)
    | (have r₁ := eq597
       have r₂ := eq903 y x
       grind)
    | exact resolve eq597 eq903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1015 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1014
  have eq1048 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1015
  have eq1062 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq597
       have i₂ := eq1048
       grind)
    | exact superpose eq1048 eq597
    | exact resolve eq597 eq1048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597 eq1048
  have eq1063 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1062
  have eq1064 : (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1063
  have eq1124 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq1064
  have eq1142 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq1124
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq1124
    | exact resolve eq1124 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1124
  have eq1230 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1142
       grind)
    | exact superpose eq1142 eq16
    | exact resolve eq16 eq1142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1142
  have eq1248 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1230
       have i₂ := eq903 y x
       grind)
    | exact superpose eq903 eq1230
    | (have j1 := eq903 y x
       grind)
    | (have r₁ := eq1230
       have r₂ := eq903 y x
       grind)
    | exact resolve eq1230 eq903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903
  have eq1249 : y = (M.op x x) := by grind
  clear eq1248
  have eq1310 : (M.op x y) = (k y x) := by grind
  clear eq1249
  have eq1327 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1230
       have i₂ := eq1310
       grind)
    | exact superpose eq1310 eq1230
    | exact resolve eq1230 eq1310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1230 eq1310
  have eq1330 : False := by grind
  exact eq1330

/-- `Equation1443`: `x = (x ◇ y) ◇ (x ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_pxy_pxx_pxy_Equation1443 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1443 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1443.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X0 X2))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
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
  have eq21 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X0 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X1) X2 (M.op X0 (M.op X0 x))
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k (τ X0) X1) X2
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq15
    | exact resolve eq15 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq35 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25
    | exact resolve eq25 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq56 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq79 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq114 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq56 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq56
    | exact resolve eq56 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq124 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq114 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq114
    | (have j0 := eq114 X0
       grind)
    | exact resolve eq114 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq125 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq124 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq124
    | (have j0 := eq124 X0
       grind)
    | exact resolve eq124 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq126 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq125 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq125 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq125 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq129 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq126 (σ X0)
       grind)
    | exact superpose eq126 eq15
    | exact resolve eq15 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0 X0
       have i₂ := eq126 (τ X0)
       grind)
    | exact superpose eq126 eq35
    | exact resolve eq35 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq138 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq131 X0
       have i₂ := eq126 X0
       grind)
    | exact superpose eq126 eq131
    | exact resolve eq131 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq140 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq129 X0
       have i₂ := eq126 X0
       grind)
    | exact superpose eq126 eq129
    | exact resolve eq129 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq165 : ∀ X0 X1 X2 : G, (σ X2) = (M.op (σ X2) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (σ X2) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq79 (k (τ X0) X1) X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq79
    | exact resolve eq79 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq184 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op (M.op (τ (M.op X0 X0)) X1) (M.op (τ (M.op X0 X0)) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq21 (τ X0) (τ X0) x
       have i₂ := eq138 X0
       grind)
    | exact superpose eq138 eq21
    | exact resolve eq21 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq138
  have eq3179 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ X0) ∨ (M.op (k X1 (σ X2)) (σ X0)) = (k (k X1 (σ X2)) (σ X0)) ∨ (σ X0) = (k X1 (σ X2)) ∨ (M.op (k X1 (σ X2)) (σ X0)) = (σ (k (k (τ X1) X2) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (k X1 (σ X2)) (σ X0)
       have i₂ := eq165 X1 X2 X0
       grind)
    | exact superpose eq165 eq12
    | (have j0 := eq12 (k X1 (σ X2)) (σ X0)
       have j1 := eq165 X1 X2 X0
       grind)
    | (have r₁ := eq12 (k X0 (σ X1)) (σ X2)
       have r₂ := eq165 X0 X1 X2
       grind)
    | exact resolve eq12 eq165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165
  have eq3196 : ∀ X0 X1 X2 : G, (M.op (k X1 (σ X2)) (σ X0)) = (k (k X1 (σ X2)) (σ X0)) ∨ (σ X0) = (k X1 (σ X2)) ∨ (M.op (k X1 (σ X2)) (σ X0)) = (σ (k (k (τ X1) X2) X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq3179 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3179
  have eq3204 : ∀ X0 X1 X2 : G, (M.op (k X1 (σ X2)) (σ X0)) = (σ (k (k (τ X1) X2) X0)) ∨ (σ X0) = (k X1 (σ X2)) ∨ (M.op (k X1 (σ X2)) (σ X0)) = (σ (k (k (τ X1) X2) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3196 X0 X1 X2
       have i₂ := eq24 X1 X2 X0
       grind)
    | exact superpose eq24 eq3196
    | (have j0 := eq3196 X0 X1 X2
       grind)
    | exact resolve eq3196 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq3196
  have eq3205 : ∀ X0 X1 X2 : G, (M.op (k X1 (σ X2)) (σ X0)) = (σ (k (k (τ X1) X2) X0)) ∨ (σ X0) = (k X1 (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq3204 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3204
  have eq3527 : ∀ X0 X1 X2 : G, (τ X0) = (M.op (M.op (τ X0) X2) (M.op (τ X0) (τ (M.op X0 (M.op X0 X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq184 (M.op X0 (M.op X0 X2)) X1
       have i₂ := eq9 X0 (M.op X0 X2) X2
       grind)
    | exact superpose eq9 eq184
    | exact resolve eq184 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq3896 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 (τ (M.op (σ X0) (M.op (σ X0) X2))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3527 (σ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3527
    | exact resolve eq3527 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3527
  have eq13704 : ∀ X0 X1 X2 : G, (k (σ (k (τ X0) X1)) X2) = (M.op (k X0 (σ X1)) (σ (τ X2))) ∨ (k X0 (σ X1)) = (σ (τ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X2 (k (τ X0) X1)
       have i₂ := eq3205 (τ X2) X0 X1
       grind)
    | exact superpose eq3205 eq19
    | (have j1 := eq3205 (τ X2) X0 X1
       grind)
    | exact resolve eq19 eq3205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3205
  have eq13788 : ∀ X0 X1 X2 : G, (k (σ (k (τ X0) X1)) X2) = (M.op (k X0 (σ X1)) X2) ∨ (k X0 (σ X1)) = (σ (τ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13704 X0 X1 X2
       have i₂ := eq11 X2
       grind)
    | exact superpose eq11 eq13704
    | (have j0 := eq13704 X0 X1 X2
       grind)
    | exact resolve eq13704 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13704
  have eq13826 : ∀ X0 X1 X2 : G, (k (k X0 (σ X1)) X2) = (M.op (k X0 (σ X1)) X2) ∨ (k X0 (σ X1)) = (σ (τ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13788 X0 X1 X2
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq13788
    | (have j0 := eq13788 X0 X1 X2
       grind)
    | exact resolve eq13788 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq13788
  have eq13858 : ∀ X0 X1 X2 : G, (k (k X0 (σ X1)) X2) = (M.op (k X0 (σ X1)) X2) ∨ (k X0 (σ X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13826 X0 X1 X2
       have i₂ := eq11 X2
       grind)
    | exact superpose eq11 eq13826
    | (have j0 := eq13826 X0 X1 X2
       grind)
    | exact resolve eq13826 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13826
  have eq13908 : ∀ X0 X1 X2 : G, (k (k X1 X0) X2) = (M.op (k X1 X0) X2) ∨ (k X1 X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13858 X0 (τ X0) X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq13858
    | exact resolve eq13858 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13858
  have eq14008 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = (M.op (M.op X0 X0) X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13908 X0 X0 x
       have i₂ := eq126 X0
       grind)
    | exact superpose eq126 eq13908
    | (have j0 := eq13908 X1 (M.op X0 X0) (M.op (M.op X0 X0) X1)
       grind)
    | exact resolve eq13908 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126 eq13908
  have eq14353 : ∀ X0 X2 : G, (M.op X0 X2) = (k X0 X2) ∨ X0 = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq14008 (M.op X0 (τ (M.op (σ X0) (M.op (σ X0) X2)))) x
       have i₂ := eq3896 X0 (τ (M.op (σ X0) (M.op (σ X0) X2))) X2
       grind)
    | exact superpose eq3896 eq14008
    | exact resolve eq14008 eq3896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3896 eq14008
  have eq14429 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14353 X0 (τ X1)
       grind)
    | exact superpose eq14353 eq19
    | (have j1 := eq14353 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq14353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq14447 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14353 (σ X0) (σ X1)
       grind)
    | exact superpose eq14353 eq15
    | (have j1 := eq14353 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq14353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14353
  have eq15284 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14429 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq14429
    | exact resolve eq14429 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14429
  have eq15396 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15284 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq15284
    | (have j0 := eq15284 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq15284 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15284
  have eq16561 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14447 x y
       grind)
    | exact superpose eq14447 eq16
    | (have j1 := eq14447 x y
       grind)
    | exact resolve eq16 eq14447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14447
  have eq16714 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16561
       have i₂ := eq15396 y x
       grind)
    | exact superpose eq15396 eq16561
    | (have j1 := eq15396 (σ x) (σ y)
       grind)
    | (have r₁ := eq16561
       have r₂ := eq15396 y x
       grind)
    | (have r₁ := eq16561
       have r₂ := eq15396 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq16561
       have r₂ := eq15396 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq16561 eq15396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15396 eq16561
  have eq16717 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq16714
  have eq16898 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16717
       grind)
    | exact superpose eq16717 eq16
    | exact resolve eq16 eq16717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16717
  have eq16899 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq16898
       have r₂ := eq140 x
       grind)
    | exact resolve eq16898 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16898
  have eq16900 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16899
       grind)
    | exact superpose eq16899 eq16
    | exact resolve eq16 eq16899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16901 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq16899
       grind)
    | exact superpose eq16899 eq10
    | exact resolve eq10 eq16899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16899
  have eq17002 : x = y := by
    first
    | (have i₁ := eq16901
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq16901
    | exact resolve eq16901 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16901
  have eq17003 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16900
       have i₂ := eq140 x
       grind)
    | exact superpose eq140 eq16900
    | exact resolve eq16900 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140 eq16900
  have eq17008 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq17003
       have i₂ := eq17002
       grind)
    | exact superpose eq17002 eq17003
    | exact resolve eq17003 eq17002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17002 eq17003
  have eq17009 : False := by grind
  exact eq17009

/-- `Equation1445`: `x = (x ◇ y) ◇ (x ◇ (y ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pxy_pyx_pxy_Equation1445 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1445 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1445.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
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
  have eq53 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq53 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq53 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq53 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq56 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq54 (σ X0)
       grind)
    | exact superpose eq54 eq15
    | exact resolve eq15 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq56 X0
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq56
    | exact resolve eq56 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq56
  have eq79 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq92 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq86 X0 X1
       have i₂ := eq65 X1
       grind)
    | exact superpose eq65 eq86
    | (have j0 := eq86 X0 X1
       grind)
    | exact resolve eq86 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq86
  have eq239 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq92 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq92 X0 X1
       grind)
    | exact superpose eq92 eq13
    | (have j0 := eq13 X0 (σ X1)
       have j1 := eq92 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq92 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq92 X0 X1
       grind)
    | exact resolve eq13 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq244 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq239 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq249 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq244 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq244 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq244 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244
  have eq262 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq249 X0 X1
       have j1 := eq79 X1 (σ X0)
       grind)
    | (have r₁ := eq249 X0 X0
       have r₂ := eq79 X0 X1
       grind)
    | exact resolve eq249 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq249
  have eq269 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq262 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq262
    | (have j0 := eq262 X0 X1
       grind)
    | exact resolve eq262 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262
  have eq270 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq269 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269
  have eq276 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq270 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq270
    | exact resolve eq270 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq287 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq270 x y
       grind)
    | exact superpose eq270 eq16
    | exact resolve eq16 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq386 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq276 X0 (τ X1)
       grind)
    | exact superpose eq276 eq18
    | exact resolve eq18 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq276
  have eq409 : ∀ X0 X1 : G, (M.op X0 X1) = (k (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq386 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq386
    | exact resolve eq386 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386
  have eq420 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq409 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq409
    | exact resolve eq409 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409
  have eq447 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq287
       have i₂ := eq420 x y
       grind)
    | exact superpose eq420 eq287
    | exact resolve eq287 eq420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287 eq420
  have eq448 : False := by grind
  exact eq448

/-- `Equation1445`: `x = (x ◇ y) ◇ (x ◇ (y ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pxy_pyx_Equation1445 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1445 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1445.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X0) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq19 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq20 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (k X1 X1) ≠ (k X0 X0) := by
    intro X0 X1
    grind
  clear eq18
  have eq21 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (k X1 X1) = (k X0 X0) := by
    intro X0 X1
    grind
  clear eq19
  have eq22 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq15
    | exact resolve eq15 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq566 : (M.op (σ x) (σ y)) ≠ (σ (k x y)) ∨ x = y ∨ (k y y) ≠ (k x x) := by
    first
    | (have i₁ := eq9
       have i₂ := eq20 x y
       grind)
    | exact superpose eq20 eq9
    | (have j1 := eq20 x y
       grind)
    | (have r₁ := eq9
       have r₂ := eq20 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq9
       have r₂ := eq20 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq9 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq573 : (k y y) ≠ (k x x) ∨ x = y ∨ (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq566
       have i₂ := eq10 x y
       grind)
    | exact superpose eq10 eq566
    | exact resolve eq566 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566
  have eq1226 : (M.op (σ x) (σ y)) ≠ (σ (k y x)) ∨ x = y ∨ (k y y) = (k x x) := by
    first
    | (have i₁ := eq9
       have i₂ := eq21 y x
       grind)
    | exact superpose eq21 eq9
    | (have j1 := eq21 x y
       grind)
    | (have r₁ := eq9
       have r₂ := eq21 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq9
       have r₂ := eq21 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq9 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1236 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ x = y ∨ (k y y) = (k x x) := by
    first
    | (have i₁ := eq1226
       have i₂ := eq10 y x
       grind)
    | exact superpose eq10 eq1226
    | exact resolve eq1226 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1226
  have eq1244 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ x = y ∨ (k y y) = (k x x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1236
       have i₂ := eq21 (σ y) (σ x)
       grind)
    | exact superpose eq21 eq1236
    | (have j1 := eq21 x y
       grind)
    | (have r₁ := eq1236
       have r₂ := eq21 (σ y) (σ x)
       grind)
    | (have r₁ := eq1236
       have r₂ := eq21 (M.op (σ x) (σ y)) (k (σ y) (σ x))
       grind)
    | (have r₁ := eq1236
       have r₂ := eq21 (k (σ y) (σ x)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq1236 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1236
  have eq1246 : x = y ∨ (k y y) = (k x x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq1244
  have eq1322 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (k y y) = (k x x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq1246
       grind)
    | exact superpose eq1246 eq9
    | exact resolve eq9 eq1246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1246
  have eq1323 : (M.op (σ x) (σ x)) ≠ (σ (k x x)) ∨ (k y y) = (k x x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq1322
  have eq1324 : (k (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (k y y) = (k x x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1323
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq1323
    | exact resolve eq1323 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1323
  have eq1325 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (k y y) = (k x x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq1324
  have eq1326 : (k y y) = (k x x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq1325
  have eq1404 : (k (σ y) (σ y)) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq10 y y
       have i₂ := eq1326
       grind)
    | exact superpose eq1326 eq10
    | exact resolve eq10 eq1326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1326
  have eq1406 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1404
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq1404
    | exact resolve eq1404 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1404
  have eq1407 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq1406
  have eq1410 : (k y y) = (τ (k (σ x) (σ x))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq22 y y
       have i₂ := eq1407
       grind)
    | exact superpose eq1407 eq22
    | exact resolve eq22 eq1407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1457 : (k y y) = (k x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1410
       have i₂ := eq22 x x
       grind)
    | exact superpose eq22 eq1410
    | exact resolve eq1410 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1410
  have eq1479 : (k x x) ≠ (k x x) ∨ x = y ∨ (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq573
       have i₂ := eq1457
       grind)
    | exact superpose eq1457 eq573
    | (have r₁ := eq573
       have r₂ := eq1457
       grind)
    | exact resolve eq573 eq1457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573 eq1457
  have eq1482 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1479
  have eq1486 : (k (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1482
       have i₂ := eq20 (σ x) (σ y)
       grind)
    | exact superpose eq20 eq1482
    | (have j1 := eq20 (σ x) (σ y)
       grind)
    | (have r₁ := eq1482
       have r₂ := eq20 (σ x) (σ y)
       grind)
    | (have r₁ := eq1482
       have r₂ := eq20 (M.op (σ x) (σ y)) (k (σ x) (σ y))
       grind)
    | (have r₁ := eq1482
       have r₂ := eq20 (k (σ x) (σ y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq1482 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1482
  have eq1487 : (k (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) := by grind
  clear eq1486
  have eq1488 : x = y ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) := by grind
  clear eq1487
  have eq1490 : x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq1488
       have r₂ := eq1407
       grind)
    | exact resolve eq1488 eq1407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1407 eq1488
  have eq1491 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9
       have i₂ := eq1490
       grind)
    | exact superpose eq1490 eq9
    | exact resolve eq9 eq1490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1490
  have eq1492 : (M.op (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ y) := by grind
  clear eq1491
  have eq1493 : (k (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1492
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq1492
    | exact resolve eq1492 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1492
  have eq1494 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq1493
  have eq1495 : (σ x) = (σ y) := by grind
  clear eq1494
  have eq1497 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq15 y
       have i₂ := eq1495
       grind)
    | exact superpose eq1495 eq15
    | exact resolve eq15 eq1495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1495
  have eq1544 : x = y := by
    first
    | (have i₁ := eq1497
       have i₂ := eq15 x
       grind)
    | exact superpose eq15 eq1497
    | exact resolve eq1497 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1497
  have eq1547 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq1544
       grind)
    | exact superpose eq1544 eq9
    | exact resolve eq9 eq1544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1544
  have eq1548 : (M.op (σ x) (σ x)) ≠ (σ (k x x)) := by grind
  clear eq1547
  have eq1549 : (k (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1548
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq1548
    | exact resolve eq1548 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1548
  have eq1550 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) := by grind
  clear eq1549
  have eq1551 : False := by grind
  exact eq1551

/-- `Equation1445`: `x = (x ◇ y) ◇ (x ◇ (y ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_y_pxy_Equation1445 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1445 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1445.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
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
  have eq49 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq93 : ∀ X0 X1 : G, (σ X1) = (M.op X0 (σ X1)) ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq28
    | (have j1 := eq14 X0 (σ X1)
       grind)
    | exact resolve eq28 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq247 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq95 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq5111 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k X1 (σ X0)) ∨ (σ X0) = X1 ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq93 X1 X0
       grind)
    | exact superpose eq93 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq93 X1 X0
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq93 X0 X1
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq93 (M.op X0 (σ X1)) X1
       grind)
    | exact resolve eq13 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq5130 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k X1 (σ X0)) ∨ (σ X0) = X1 ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq5111 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5111
  have eq5131 : ∀ X0 X1 : G, (σ X0) = (k X1 (σ X0)) ∨ (σ X0) = X1 ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq5130 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5130
  have eq6722 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ X0 = X1 ∨ (k (τ X1) (τ X0)) = (τ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5131 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5131
    | exact resolve eq5131 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6756 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ X1) X0) ∨ (σ X0) = X1 ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 X0
       have i₂ := eq5131 X0 X1
       grind)
    | exact superpose eq5131 eq28
    | (have j1 := eq5131 X0 X1
       grind)
    | exact resolve eq28 eq5131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq5131
  have eq6850 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (σ X0) = X1 ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq6756 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6756
    | (have j0 := eq6756 X0 X1
       grind)
    | exact resolve eq6756 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6756
  have eq6858 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ (k X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6722 X0 X1
       have i₂ := eq49 X0 X1
       grind)
    | exact superpose eq49 eq6722
    | (have j0 := eq6722 X0 X1
       grind)
    | exact resolve eq6722 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6722
  have eq6913 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq6858 X1 X0
       grind)
    | exact superpose eq6858 eq11
    | (have j1 := eq6858 X1 X0
       grind)
    | exact resolve eq11 eq6858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6858
  have eq7038 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6913 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq6913
    | (have j0 := eq6913 X0 X1
       grind)
    | exact resolve eq6913 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6913
  have eq7299 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq7038 (τ X0) X1
       grind)
    | exact superpose eq7038 eq18
    | (have j1 := eq7038 (τ X0) X1
       grind)
    | exact resolve eq18 eq7038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq7038
  have eq7392 : ∀ X0 X1 : G, (τ X1) = (τ (k X0 X1)) ∨ (σ (τ X1)) = X0 ∨ (τ (k X0 X1)) = (τ (M.op X0 (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq6850 (τ X0) X1
       have i₂ := eq49 X0 X1
       grind)
    | exact superpose eq49 eq6850
    | (have j0 := eq6850 (τ X1) X0
       grind)
    | exact resolve eq6850 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq6850
  have eq7540 : ∀ X0 X1 : G, X0 = X1 ∨ (τ X1) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op X0 (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq7392 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq7392
    | (have j0 := eq7392 X0 X1
       grind)
    | exact resolve eq7392 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7392
  have eq7583 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ X0 = X1 ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7540 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq7540
    | (have j0 := eq7540 X0 X1
       grind)
    | exact resolve eq7540 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7540
  have eq7924 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ X0 = X1 ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq7583 X0 X1
       grind)
    | exact superpose eq7583 eq11
    | (have j1 := eq7583 X0 X1
       grind)
    | exact resolve eq11 eq7583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7583
  have eq8051 : ∀ X0 X1 : G, (τ X1) = (τ (k X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq7924 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq7924
    | (have j0 := eq7924 X0 X1
       grind)
    | exact resolve eq7924 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7924
  have eq8335 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = (τ (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8051 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq8051
    | (have j0 := eq8051 (τ (σ (k X0 X1))) (τ (σ X1))
       grind)
    | exact resolve eq8051 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8051
  have eq8523 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = X1 ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8335 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq8335
    | (have j0 := eq8335 X0 X1
       grind)
    | exact resolve eq8335 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8335
  have eq8532 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8523 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq8523
    | (have j0 := eq8523 X0 X1
       grind)
    | exact resolve eq8523 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8523
  have eq9408 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7299 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7299
    | exact resolve eq7299 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7299
  have eq9507 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9408 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq9408
    | (have j0 := eq9408 X0 X1
       grind)
    | exact resolve eq9408 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9408
  have eq10095 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8532 x y
       grind)
    | exact superpose eq8532 eq16
    | (have j1 := eq8532 x y
       grind)
    | exact resolve eq16 eq8532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8532
  have eq10258 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq10095
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq10095
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq10095
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq10095
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq10095 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10259 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ y = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq10095
       have i₂ := eq9507 x y
       grind)
    | exact superpose eq9507 eq10095
    | (have j1 := eq9507 x y
       grind)
    | (have r₁ := eq10095
       have r₂ := eq9507 x y
       grind)
    | (have r₁ := eq10095
       have r₂ := eq9507 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq10095
       have r₂ := eq9507 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq10095 eq9507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9507 eq10095
  have eq10262 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ x = y := by grind
  clear eq10259
  have eq10263 : x = y ∨ y = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq10262
  have eq10264 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq10258
  have eq10265 : x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq10264
  have eq10268 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10263
       grind)
    | exact superpose eq10263 eq16
    | exact resolve eq16 eq10263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10263
  have eq10269 : y = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq10268
       have r₂ := eq22 x
       grind)
    | exact resolve eq10268 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10268
  have eq10378 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq247 x y
       have i₂ := eq10269
       grind)
    | exact superpose eq10269 eq247
    | (have j0 := eq247 x y
       grind)
    | exact resolve eq247 eq10269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247 eq10269
  have eq10393 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq10378
  have eq10394 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq10393
  have eq10399 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10265
       grind)
    | exact superpose eq10265 eq16
    | exact resolve eq16 eq10265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10265
  have eq10400 : y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq10399
       have r₂ := eq22 x
       grind)
    | exact resolve eq10399 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10399
  have eq10516 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10394
       grind)
    | exact superpose eq10394 eq16
    | exact resolve eq16 eq10394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10394
  have eq10652 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq10516
       have i₂ := eq10400
       grind)
    | exact superpose eq10400 eq10516
    | exact resolve eq10516 eq10400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10400 eq10516
  have eq10656 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq10652
  have eq10657 : (σ x) = (σ y) := by grind
  clear eq10656
  have eq10658 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10657
       grind)
    | exact superpose eq10657 eq16
    | exact resolve eq16 eq10657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10659 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq10657
       grind)
    | exact superpose eq10657 eq10
    | exact resolve eq10 eq10657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10657
  have eq10751 : x = y := by
    first
    | (have i₁ := eq10659
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq10659
    | exact resolve eq10659 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10659
  have eq10752 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq10658
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq10658
    | exact resolve eq10658 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq10658
  have eq10753 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq10752
       have i₂ := eq10751
       grind)
    | exact superpose eq10751 eq10752
    | exact resolve eq10752 eq10751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10751 eq10752
  have eq10754 : False := by grind
  exact eq10754

/-- `Equation1446`: `x = (x ◇ y) ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,X) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_x_pxy_pxx_pxy_Equation1446 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X2))) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X0
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq11 eq13
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
  clear eq24
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
  have eq175 : ∀ X0 : G, x = (M.op (M.op x y) (M.op x (M.op y X0))) := by
    intro X0
    first
    | (have i₁ := eq16 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x y X0
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ y) X0))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, (M.op (M.op X0 x) (M.op X0 (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 x y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (M.op X0 (M.op (σ x) (σ y)))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X1 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 (M.op X0 X2) (M.op X0 (M.op X2 x))
       have i₂ := eq16 X0 X2 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : (M.op x y) = (M.op (M.op (M.op x y) x) x) := by
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) (M.op X0 x)) = X0 := by
    intro X0
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) := by
    first
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op X0 (σ x))) = X0 := by
    intro X0
    first
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq593 : (M.op x y) = (M.op x (M.op (M.op x y) x)) := by
    first
    | exact superpose eq175 eq180
    | exact resolve eq180 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq594 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    first
    | exact superpose eq176 eq180
    | exact resolve eq180 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq612 : x = (M.op (M.op x y) (M.op x (M.op x y))) := by
    first
    | exact superpose eq593 eq180
    | exact resolve eq180 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq613 : x = (M.op (M.op x (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq593 eq16
    | exact resolve eq16 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593
  have eq620 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq594 eq180
    | exact resolve eq180 eq594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq621 : (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq594 eq16
    | exact resolve eq16 eq594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594
  have eq703 : (M.op x y) = (k x y) ∨ x = (M.op x x) := by
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
  clear eq18
  have eq713 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
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
  clear eq26
  have eq723 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq762 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq703
       grind)
    | exact superpose eq703 eq41
    | exact resolve eq41 eq703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq703
  have eq763 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq762
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq762
    | exact resolve eq762 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762
  have eq765 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq763
    | exact resolve eq763 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763
  have eq775 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq765 eq713
    | exact resolve eq713 eq765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713 eq765
  have eq782 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq775
       have r₂ := eq27
       grind)
    | exact resolve eq775 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775
  have eq792 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq782 eq13
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq782
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq782
       grind)
    | exact resolve eq13 eq782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782
  have eq795 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq792
  have eq799 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq795 eq142
    | exact resolve eq142 eq795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq795
  have eq802 : x = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq30 eq799
    | exact resolve eq799 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq799
  have eq805 : x = (M.op x x) := by
    first
    | (have j1 := eq723 x
       grind)
    | (have r₁ := eq802
       have r₂ := eq723 x
       grind)
    | exact resolve eq802 eq723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802
  have eq809 : x = (M.op (M.op x (M.op x y)) x) := by
    first
    | (have i₁ := eq188 x
       have i₂ := eq805
       grind)
    | exact superpose eq805 eq188
    | exact resolve eq188 eq805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq814 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq805
       grind)
    | exact superpose eq805 eq13
    | (have r₁ := eq13 x x
       have r₂ := eq805
       grind)
    | exact resolve eq13 eq805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq817 : x = (k x x) := by grind
  clear eq814
  have eq820 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq817
       grind)
    | exact superpose eq817 eq40
    | exact resolve eq40 eq817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq817
  have eq823 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq820
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq820
    | exact resolve eq820 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq820
  have eq828 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq823 eq723
    | (have j0 := eq723 (σ x)
       grind)
    | (have r₁ := eq723 (σ x)
       have r₂ := eq823
       grind)
    | exact resolve eq723 eq823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723 eq823
  have eq829 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq828
  have eq834 : (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq829 eq195
    | exact resolve eq195 eq829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq847 : (M.op x (M.op x y)) = (M.op x (M.op (M.op x (M.op x y)) (M.op x y))) := by
    first
    | exact superpose eq809 eq178
    | exact resolve eq178 eq809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq809
  have eq856 : (M.op x (M.op x y)) = (M.op x x) := by
    first
    | exact superpose eq613 eq847
    | exact resolve eq847 eq613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613 eq847
  have eq858 : x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq856
       have i₂ := eq805
       grind)
    | exact superpose eq805 eq856
    | exact resolve eq856 eq805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856
  have eq863 : x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq858 eq612
    | exact resolve eq612 eq858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612 eq858
  have eq876 : (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq863 eq186
    | exact resolve eq186 eq863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186 eq863
  have eq889 : x = (M.op x y) := by
    first
    | (have i₁ := eq805
       have i₂ := eq876
       grind)
    | exact superpose eq876 eq805
    | exact resolve eq805 eq876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq805 eq876
  have eq903 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq889
       grind)
    | exact superpose eq889 eq22
    | exact resolve eq22 eq889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq889
  have eq927 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq903 eq20
    | exact resolve eq20 eq903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq903
  have eq1062 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq834 eq179
    | exact resolve eq179 eq834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq834
  have eq1071 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq621 eq1062
    | exact resolve eq1062 eq621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621 eq1062
  have eq1073 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq829 eq1071
    | exact resolve eq1071 eq829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1071
  have eq1078 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq1073 eq620
    | exact resolve eq620 eq1073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620 eq1073
  have eq1091 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1078 eq193
    | exact resolve eq193 eq1078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193 eq1078
  have eq1102 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq829 eq1091
    | exact resolve eq1091 eq829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829 eq1091
  have eq1305 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq1102 eq27
    | exact resolve eq27 eq1102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1102
  have eq1323 : False := by grind
  exact eq1323
