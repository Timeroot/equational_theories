import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_pxy_pyy_pxy_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq21 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq9 (M.op X0 X3) (M.op x x) X0 X4
       have i₂ := eq9 X0 x x X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  clear eq19
  have eq36 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    grind
  have eq46 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq34
    | exact resolve eq34 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq58 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq189 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq58 x y
       grind)
    | exact superpose eq58 eq16
    | (have j1 := eq58 x y
       grind)
    | exact resolve eq16 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (σ (k X0 X1)) (M.op (σ X1) X2)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 (σ X0) (σ X1) X2
       have i₂ := eq58 X0 X1
       grind)
    | exact superpose eq58 eq21
    | (have j1 := eq58 X0 X1
       grind)
    | exact resolve eq21 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq194 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (M.op (σ (k X0 X1)) X2)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 (σ X0) (σ X1) x
       have i₂ := eq58 X0 X1
       grind)
    | exact superpose eq58 eq22
    | (have j1 := eq58 X0 X1
       grind)
    | exact resolve eq22 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq202 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  clear eq58
  have eq207 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq202 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq210 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq207 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq207
    | (have j0 := eq207 X0
       grind)
    | exact resolve eq207 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq720 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq189
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq189
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq189 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq721 : y = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by grind
  clear eq720
  have eq937 : ∀ X0 X1 X2 : G, (σ (τ X1)) = (M.op (σ (τ (k X0 X1))) (M.op (σ (τ X1)) X2)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq193 (τ X0) (τ X1) X2
       have i₂ := eq46 X1 X0
       grind)
    | exact superpose eq46 eq193
    | (have j0 := eq193 (τ X0) (τ X1) X2
       grind)
    | exact resolve eq193 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq193
  have eq970 : ∀ X0 X1 X2 : G, (M.op (σ (τ (k X0 X1))) (M.op X1 X2)) = X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq937 X0 X0 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq937
    | (have j0 := eq937 X0 X1 X2
       grind)
    | exact resolve eq937 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq937
  have eq973 : ∀ X0 X1 X2 : G, (M.op (k X0 X1) (M.op X1 X2)) = X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq970 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq970
    | (have j0 := eq970 X0 X1 X2
       grind)
    | exact resolve eq970 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq970
  have eq975 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (σ (τ X1)) ∨ (M.op (k X0 X1) (M.op X1 X2)) = X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq973 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq973
    | (have j0 := eq973 X0 X1 X2
       grind)
    | exact resolve eq973 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq973
  have eq976 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X1 ∨ (M.op (k X0 X1) (M.op X1 X2)) = X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq975 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq975
    | (have j0 := eq975 X0 X1 X2
       grind)
    | exact resolve eq975 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq975
  have eq977 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op (k X0 X1) (M.op X1 X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq976 X0 X0 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq976
    | (have j0 := eq976 X0 X1 X2
       grind)
    | exact resolve eq976 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq976
  have eq978 : ∀ X0 X1 X2 : G, (M.op (k X0 X1) (M.op X1 X2)) = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq977 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq977
    | (have j0 := eq977 X0 X1 X2
       grind)
    | exact resolve eq977 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq977
  have eq1124 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ (k (k X0 X0) X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq194 X0 X0 (σ X0)
       have i₂ := eq210 X0
       grind)
    | exact superpose eq210 eq194
    | (have j0 := eq194 X0 X0 x
       have j1 := eq210 X0
       grind)
    | exact resolve eq194 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194 eq210
  have eq1138 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X0)) = (M.op (σ X0) (σ (k (k X0 X0) X0))) := by
    intro X0
    first
    | (have j0 := eq1124 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1124
  have eq4583 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ (k (τ X0) (τ X0))) = (M.op X0 (σ (k (k (τ X0) (τ X0)) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq1138 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1138
    | exact resolve eq1138 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1138
  have eq4639 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (M.op X0 (k (σ (k (τ X0) (τ X0))) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4583 X0
       have i₂ := eq20 X0 (k (τ X0) (τ X0))
       grind)
    | exact superpose eq20 eq4583
    | (have j0 := eq4583 X0
       grind)
    | exact resolve eq4583 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4583
  have eq4642 : ∀ X0 : G, (k (σ (τ X0)) X0) = (M.op X0 (k (k (σ (τ X0)) X0) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4639 X0
       have i₂ := eq20 X0 (τ X0)
       grind)
    | exact superpose eq20 eq4639
    | (have j0 := eq4639 X0
       grind)
    | exact resolve eq4639 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq4639
  have eq4643 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k (k X0 X0) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4642 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4642
    | (have j0 := eq4642 X0
       grind)
    | exact resolve eq4642 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4642
  have eq4655 : ∀ X0 X1 : G, (k X0 X0) = (M.op X0 (M.op (k X0 X0) X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq22 X0 (k (k X0 X0) X0) x
       have i₂ := eq4643 X0
       grind)
    | exact superpose eq4643 eq22
    | (have j1 := eq4643 X0
       grind)
    | exact resolve eq22 eq4643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq4643
  have eq4821 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4655 X0 (M.op X0 x)
       have i₂ := eq978 X0 X0 x
       grind)
    | exact superpose eq978 eq4655
    | (have j0 := eq4655 X0 x
       have j1 := eq978 X0 X0 x
       grind)
    | exact resolve eq4655 eq978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq978 eq4655
  have eq4848 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq4821 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4821
  have eq4863 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  clear eq4848
  have eq4895 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq4863 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4863
  have eq5085 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq4895 (σ X0)
       grind)
    | exact superpose eq4895 eq15
    | exact resolve eq15 eq4895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5151 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq5085 X0
       have i₂ := eq4895 X0
       grind)
    | exact superpose eq4895 eq5085
    | exact resolve eq5085 eq4895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4895 eq5085
  have eq5778 : ∀ X0 : G, (k (σ X0) (σ (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq36 (σ X0)
       have i₂ := eq5151 X0
       grind)
    | exact superpose eq5151 eq36
    | exact resolve eq36 eq5151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5780 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq5803 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq5780 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq5780
    | exact resolve eq5780 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5780
  have eq5805 : ∀ X0 : G, (σ (k X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq5778 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq5778
    | exact resolve eq5778 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5778
  have eq5838 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  clear eq5803
  have eq5840 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq5805 X0
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq5805
    | exact resolve eq5805 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq5805
  have eq10615 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq5840 x
       have i₂ := eq721
       grind)
    | exact superpose eq721 eq5840
    | exact resolve eq5840 eq721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721 eq5840
  have eq10661 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq10615
       have r₂ := eq16
       grind)
    | exact resolve eq10615 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10615
  have eq10697 : (σ x) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10661
       have i₂ := eq5151 y
       grind)
    | exact superpose eq5151 eq10661
    | exact resolve eq10661 eq5151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10661
  have eq10718 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10697
       have i₂ := eq5151 x
       grind)
    | exact superpose eq5151 eq10697
    | exact resolve eq10697 eq5151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10697
  have eq37441 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq5838 y
       have i₂ := eq10718
       grind)
    | exact superpose eq10718 eq5838
    | exact resolve eq5838 eq10718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10718
  have eq37521 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq37441
       have r₂ := eq16
       grind)
    | exact resolve eq37441 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37441
  have eq38495 : (M.op (σ y) (σ y)) = (σ (M.op (M.op x x) (M.op x x))) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq5151 (M.op x x)
       have i₂ := eq37521
       grind)
    | exact superpose eq37521 eq5151
    | exact resolve eq5151 eq37521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37521
  have eq38546 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq38495
       have i₂ := eq21 x x x
       grind)
    | (have i₁ := eq38495
       have i₂ := eq21 x (M.op (M.op x x) (M.op x x)) x
       grind)
    | exact superpose eq21 eq38495
    | exact resolve eq38495 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq38495
  have eq38602 : (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq38546
       have i₂ := eq5151 y
       grind)
    | exact superpose eq5151 eq38546
    | exact resolve eq38546 eq5151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5151 eq38546
  have eq38603 : (σ x) = (σ (M.op y y)) := by grind
  clear eq38602
  have eq38654 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq38603
       grind)
    | exact superpose eq38603 eq10
    | exact resolve eq10 eq38603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38603
  have eq38813 : x = (M.op y y) := by
    first
    | (have i₁ := eq38654
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq38654
    | exact resolve eq38654 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38654
  have eq39709 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5838 y
       have i₂ := eq38813
       grind)
    | exact superpose eq38813 eq5838
    | exact resolve eq5838 eq38813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5838 eq38813
  have eq39790 : False := by grind
  exact eq39790

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_x_pyx_pxx_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
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
  have eq40 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10
    | (have j0 := eq10 X0 x
       grind)
    | exact resolve eq10 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq14 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq14 X0 x x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq75 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  clear eq37
  have eq77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq91 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq74
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq74
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq74 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq16
    | exact resolve eq16 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq91
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq91
    | exact resolve eq91 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq97
    | exact resolve eq97 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq98
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq98
    | exact resolve eq98 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq105 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq16
    | exact resolve eq16 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : y ≠ (M.op x y) ∨ y = (M.op x x) ∨ (k y x) = (M.op y y) := by
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
  have eq114 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq172 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq11 (σ X0) sF2
       grind)
    | exact superpose eq11 eq40
    | (have j1 := eq11 (σ X0) (σ x)
       grind)
    | exact resolve eq40 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq255 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq53 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq53
    | (have j0 := eq53 x y X0
       grind)
    | exact resolve eq53 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq256 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq27 eq53
    | (have j0 := eq53 (σ x) (σ y) X0
       grind)
    | exact resolve eq53 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq265 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq53 X0 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq53
    | (have j0 := eq53 X0 x y
       grind)
    | exact resolve eq53 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq27 eq53
    | (have j0 := eq53 X0 (σ x) (σ y)
       grind)
    | exact resolve eq53 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq267 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq53 X2 X0 x
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq281 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    grind
  have eq346 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq372 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq620 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq77 X0 X1
       grind)
    | exact superpose eq77 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq77 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq77 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq77 X0 X0
       grind)
    | exact resolve eq12 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq634 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq620 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620
  have eq636 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq634 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq634 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq634 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq634 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634
  have eq640 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq636 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq636
    | (have j0 := eq636 X0 X1
       grind)
    | exact resolve eq636 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636
  have eq673 : ∀ X0 : G, (k (τ X0) (k y y)) = (τ (k X0 (k (σ y) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq346 X0 (k y y)
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq346
    | exact resolve eq346 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq679 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq346 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq346
    | (have j0 := eq346 X0 y
       grind)
    | exact resolve eq346 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq722 : (k (k y y) y) = (τ (k (k (σ y) (σ y)) (σ y))) := by
    first
    | exact superpose eq105 eq679
    | exact resolve eq679 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq739 : ∀ X0 : G, (k (k y y) (τ X0)) = (τ (k (k (σ y) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq372 (k y y) X0
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq372
    | exact resolve eq372 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq745 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq372 y X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq372
    | (have j0 := eq372 y X0
       grind)
    | exact resolve eq372 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq815 : (k y (k y y)) = (τ (k (σ y) (k (σ y) (σ y)))) := by
    first
    | exact superpose eq105 eq745
    | exact resolve eq745 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3880 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq172 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172
  have eq11355 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq99 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11363 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq11355
    | exact resolve eq11355 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11355
  have eq11374 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq11363
       have r₂ := eq28
       grind)
    | exact resolve eq11363 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11363
  have eq11376 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq11374
    | exact resolve eq11374 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11374
  have eq11614 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq11376
  have eq11633 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq11614
    | exact resolve eq11614 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11614
  have eq11888 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq11633 eq99
    | exact resolve eq99 eq11633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq11633
  have eq11903 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq11888
  have eq11905 : y = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq11903
       have r₂ := eq28
       grind)
    | exact resolve eq11903 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11903
  have eq11910 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq11905
  have eq11929 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11910
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq11910
    | exact resolve eq11910 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11910
  have eq12187 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq74
       have i₂ := eq11929
       grind)
    | exact superpose eq11929 eq74
    | exact resolve eq74 eq11929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11929
  have eq12215 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq12187
    | exact resolve eq12187 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12187
  have eq12299 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12215 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq12215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12309 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq12299
    | exact resolve eq12299 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12299
  have eq12320 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq12309
       have r₂ := eq28
       grind)
    | exact resolve eq12309 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12309
  have eq12322 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq12320
    | exact resolve eq12320 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12320
  have eq12323 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq12322
  have eq12328 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq12323
  have eq12347 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq12328
    | exact resolve eq12328 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12328
  have eq12381 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12347 eq12215
    | exact resolve eq12215 eq12347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12215 eq12347
  have eq12390 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq12381
  have eq12394 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq12390
       have r₂ := eq28
       grind)
    | exact resolve eq12390 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12390
  have eq12398 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12394 eq114
    | (have r₁ := eq114
       have r₂ := eq12394
       grind)
    | exact resolve eq114 eq12394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq12407 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq12394 eq256
    | exact resolve eq256 eq12394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256
  have eq12408 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq12394 eq266
    | exact resolve eq266 eq12394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266 eq12394
  have eq12415 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq12398
  have eq13212 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12407 eq12407
    | exact resolve eq12407 eq12407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12407
  have eq13239 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq13212
  have eq13277 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13239 eq281
    | exact resolve eq281 eq13239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14151 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13277 eq105
    | exact resolve eq105 eq13277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14506 : (τ (σ y)) = (k y y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13239 eq14151
    | exact resolve eq14151 eq13239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14151
  have eq14533 : (τ (σ y)) = (k y y) ∨ y = (M.op x y) := by grind
  clear eq14506
  have eq14537 : y = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq14533
    | exact resolve eq14533 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14533
  have eq14549 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq14537
       grind)
    | exact superpose eq14537 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq14537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14569 : y = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq14549
  have eq14594 : (k y y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq281 y
       have i₂ := eq14569
       grind)
    | exact superpose eq14569 eq281
    | exact resolve eq281 eq14569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14600 : ∀ X0 : G, y = (M.op (M.op X0 y) y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq53 X0 y y
       have i₂ := eq14569
       grind)
    | exact superpose eq14569 eq53
    | exact resolve eq53 eq14569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq14569
  have eq16443 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (k (σ y) (σ y)))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq673 X0
       have i₂ := eq14537
       grind)
    | exact superpose eq14537 eq673
    | exact resolve eq673 eq14537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673
  have eq16478 : ∀ X0 : G, (τ (k X0 (k (σ y) (σ y)))) = (τ (k X0 (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16443 X0
       have i₂ := eq679 X0
       grind)
    | exact superpose eq679 eq16443
    | exact resolve eq16443 eq679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679 eq16443
  have eq18055 : ∀ X0 : G, (k y (τ X0)) = (τ (k (k (σ y) (σ y)) X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq739 X0
       have i₂ := eq14537
       grind)
    | exact superpose eq14537 eq739
    | exact resolve eq739 eq14537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739 eq14537
  have eq18161 : ∀ X0 : G, (τ (k (k (σ y) (σ y)) X0)) = (τ (k (σ y) X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq18055 X0
       have i₂ := eq745 X0
       grind)
    | exact superpose eq745 eq18055
    | exact resolve eq18055 eq745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745 eq18055
  have eq20166 : ∀ X0 : G, (k X0 (τ (k (σ y) (σ y)))) = (τ (k (σ X0) (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq16478 eq372
    | exact resolve eq372 eq16478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20170 : ∀ X0 : G, (k X0 (k (σ y) (σ y))) = (σ (τ (k X0 (σ y)))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq16478 eq15
    | exact resolve eq15 eq16478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20257 : ∀ X0 : G, (k X0 (σ y)) = (k X0 (k (σ y) (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq20170 X0
       have i₂ := eq15 (k X0 sF3)
       grind)
    | exact superpose eq15 eq20170
    | exact resolve eq20170 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20170
  have eq20261 : ∀ X0 : G, (k X0 (τ (k (σ y) (σ y)))) = (k X0 (τ (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq20166 X0
       have i₂ := eq372 X0 sF3
       grind)
    | exact superpose eq372 eq20166
    | exact resolve eq20166 eq372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372 eq20166
  have eq20267 : ∀ X0 : G, (k X0 y) = (k X0 (τ (k (σ y) (σ y)))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq30 eq20261
    | exact resolve eq20261 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20261
  have eq20270 : ∀ X0 : G, (k X0 y) = (k X0 (k y y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq105 eq20267
    | exact resolve eq20267 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20267
  have eq20273 : ∀ X0 : G, (k X0 (σ y)) = (k X0 (M.op (σ y) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13277 eq20257
    | exact resolve eq20257 eq13277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20257
  have eq20309 : ∀ X0 : G, (k X0 (σ y)) = (k X0 (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq20273 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20273
  have eq20536 : ∀ X0 : G, (k X0 y) = (k X0 (M.op y y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq20270 X0
       have i₂ := eq14594
       grind)
    | exact superpose eq14594 eq20270
    | exact resolve eq20270 eq14594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14594 eq20270
  have eq20571 : ∀ X0 : G, (k X0 y) = (k X0 (M.op y y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq20536 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20536
  have eq23431 : ∀ X0 : G, (k (τ (k (σ y) (σ y))) X0) = (τ (k (σ y) (σ X0))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq18161 eq346
    | exact resolve eq346 eq18161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23432 : (τ (k (k (σ y) (σ y)) (σ y))) = (τ (k (σ y) (k (σ y) (σ y)))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18161 eq16478
    | exact resolve eq16478 eq18161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16478
  have eq23433 : ∀ X0 : G, (k (k (σ y) (σ y)) X0) = (σ (τ (k (σ y) X0))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq18161 eq15
    | exact resolve eq15 eq18161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18161
  have eq23477 : (τ (k (k (σ y) (σ y)) (σ y))) = (τ (k (σ y) (k (σ y) (σ y)))) ∨ y = (M.op x y) := by grind
  clear eq23432
  have eq23528 : ∀ X0 : G, (k (σ y) X0) = (k (k (σ y) (σ y)) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq23433 X0
       have i₂ := eq15 (k sF3 X0)
       grind)
    | exact superpose eq15 eq23433
    | exact resolve eq23433 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23433
  have eq23529 : (k y (k y y)) = (τ (k (k (σ y) (σ y)) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq815 eq23477
    | exact resolve eq23477 eq815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23477
  have eq23530 : ∀ X0 : G, (k (τ (k (σ y) (σ y))) X0) = (k (τ (σ y)) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq23431 x
       have i₂ := eq346 sF3 x
       grind)
    | exact superpose eq346 eq23431
    | exact resolve eq23431 eq346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346 eq23431
  have eq23543 : (k y (k y y)) = (k (k y y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq722 eq23529
    | exact resolve eq23529 eq722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722 eq23529
  have eq23544 : ∀ X0 : G, (k y X0) = (k (τ (k (σ y) (σ y))) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq30 eq23530
    | exact resolve eq23530 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23530
  have eq23551 : ∀ X0 : G, (k y X0) = (k (k y y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq105 eq23544
    | exact resolve eq23544 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq23544
  have eq23556 : ∀ X0 : G, (k (σ y) X0) = (k (M.op (σ y) (σ y)) X0) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13277 eq23528
    | exact resolve eq23528 eq13277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13277 eq23528
  have eq23624 : ∀ X0 : G, (k (σ y) X0) = (k (M.op (σ y) (σ y)) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq23556 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23556
  have eq23738 : (k (k y y) y) = (k y (M.op y y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq20571 (k y y)
       have i₂ := eq23551 (M.op y y)
       grind)
    | exact superpose eq23551 eq20571
    | exact resolve eq20571 eq23551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20571 eq23551
  have eq23771 : (k (k y y) y) = (k y (M.op y y)) ∨ y = (M.op x y) := by grind
  clear eq23738
  have eq23802 : (k (k y y) y) = (M.op (M.op y y) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq23771
       have i₂ := eq281 y
       grind)
    | exact superpose eq281 eq23771
    | exact resolve eq23771 eq281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23771
  have eq23897 : (k (σ y) (σ y)) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by grind
  have eq23922 : (k (σ y) (M.op (σ y) (σ y))) = (k (M.op (σ y) (σ y)) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq23624 eq20309
    | exact resolve eq20309 eq23624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20309 eq23624
  have eq23953 : (k (σ y) (M.op (σ y) (σ y))) = (k (M.op (σ y) (σ y)) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq23922
  have eq23981 : (k (σ y) (M.op (σ y) (σ y))) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by grind
  clear eq23953
  have eq24005 : (M.op (M.op (σ y) (σ y)) (σ y)) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq23981
       have i₂ := eq281 sF3
       grind)
    | exact superpose eq281 eq23981
    | exact resolve eq23981 eq281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281 eq23981
  have eq30390 : (k y (k y y)) = (M.op (M.op y y) y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq23543
       have i₂ := eq23802
       grind)
    | exact superpose eq23802 eq23543
    | exact resolve eq23543 eq23802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23543 eq23802
  have eq30408 : (k y (k y y)) = (M.op (M.op y y) y) ∨ y = (M.op x y) := by grind
  clear eq30390
  have eq30864 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (M.op (σ y) (σ y))) (M.op (σ y) X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq24005 eq14
    | exact resolve eq14 eq24005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24005
  have eq47713 : (M.op (M.op (σ y) (M.op (σ y) (σ y))) (σ y)) = (k (σ y) (M.op (σ y) (M.op (σ y) (σ y)))) ∨ y = (M.op x y) := by grind
  clear eq30864
  have eq47752 : (M.op (σ y) (σ y)) = (k (σ y) (M.op (σ y) (M.op (σ y) (σ y)))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq47713
       have i₂ := eq267 sF3 sF3 sF3
       grind)
    | exact superpose eq267 eq47713
    | exact resolve eq47713 eq267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267 eq47713
  have eq69447 : (M.op (σ y) (σ y)) = (k (σ y) (k (σ y) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq23897 eq47752
    | exact resolve eq47752 eq23897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23897 eq47752
  have eq69462 : (M.op (σ y) (σ y)) = (k (σ y) (k (σ y) (σ y))) ∨ y = (M.op x y) := by grind
  clear eq69447
  have eq69483 : (k y (k y y)) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq69462 eq815
    | exact resolve eq815 eq69462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq815 eq69462
  have eq69534 : (τ (M.op (σ y) (σ y))) = (M.op (M.op y y) y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq30408
       have i₂ := eq69483
       grind)
    | exact superpose eq69483 eq30408
    | exact resolve eq30408 eq69483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30408 eq69483
  have eq69554 : (τ (M.op (σ y) (σ y))) = (M.op (M.op y y) y) ∨ y = (M.op x y) := by grind
  clear eq69534
  have eq70143 : y = (M.op (τ (M.op (σ y) (σ y))) y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14600 (M.op y y)
       have i₂ := eq69554
       grind)
    | exact superpose eq69554 eq14600
    | exact resolve eq14600 eq69554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14600 eq69554
  have eq70162 : y = (M.op (τ (M.op (σ y) (σ y))) y) ∨ y = (M.op x y) := by grind
  clear eq70143
  have eq90778 : (k y x) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12415 eq96
    | exact resolve eq96 eq12415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq12415
  have eq156309 : (τ (σ y)) = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13239 eq90778
    | exact resolve eq90778 eq13239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13239 eq90778
  have eq156603 : (τ (σ y)) = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq156309
  have eq156611 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq156603
    | exact resolve eq156603 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq156603
  have eq156614 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq156611 eq12408
    | exact resolve eq12408 eq156611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12408 eq156611
  have eq156636 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (k y x) := by grind
  clear eq156614
  have eq156774 : y = (M.op (τ (σ x)) y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ y = (k y x) := by
    first
    | exact superpose eq156636 eq70162
    | exact resolve eq70162 eq156636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70162 eq156636
  have eq156907 : y = (M.op (τ (σ x)) y) ∨ y = (M.op x y) ∨ y = (k y x) := by grind
  clear eq156774
  have eq157018 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (k y x) := by
    first
    | exact superpose eq29 eq156907
    | exact resolve eq156907 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq156907
  have eq157060 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq157018
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq157018
    | exact resolve eq157018 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157018
  have eq157061 : y = (k y x) ∨ y = (M.op x y) := by grind
  clear eq157060
  have eq157080 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq157061
       grind)
    | exact superpose eq157061 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq157061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq157092 : y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq157080
  have eq157105 : y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq157092
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq157092
    | exact resolve eq157092 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157092
  have eq157106 : y = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq157105
  have eq157176 : (M.op x y) = (k y x) ∨ y = (M.op x y) := by grind
  clear eq157106
  have eq157195 : (M.op x y) = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq157176
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq157176
    | exact resolve eq157176 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq157176
  have eq157357 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq157061
       have i₂ := eq157195
       grind)
    | exact superpose eq157195 eq157061
    | exact resolve eq157061 eq157195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157061 eq157195
  have eq157370 : y = (M.op x y) := by grind
  clear eq157357
  have eq157424 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq157370 eq21
    | exact resolve eq21 eq157370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq157434 : y ≠ y ∨ y = (M.op x x) ∨ (k y x) = (M.op y y) := by
    first
    | exact superpose eq157370 eq113
    | (have r₁ := eq113
       have r₂ := eq157370
       grind)
    | exact resolve eq113 eq157370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq157483 : ∀ X0 : G, y = (M.op y (M.op y X0)) := by
    intro X0
    first
    | exact superpose eq157370 eq255
    | exact resolve eq255 eq157370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq157484 : ∀ X0 : G, x = (M.op (M.op X0 x) y) := by
    intro X0
    first
    | exact superpose eq157370 eq265
    | exact resolve eq265 eq157370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265 eq157370
  have eq157586 : y = (M.op x x) ∨ (k y x) = (M.op y y) := by grind
  clear eq157434
  have eq157716 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq157424
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq157424
    | exact resolve eq157424 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157424
  have eq157720 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq157716 eq27
    | exact resolve eq27 eq157716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq158286 : y = (M.op y y) := by
    first
    | (have i₁ := eq157483 (M.op y x)
       have i₂ := eq157483 x
       grind)
    | exact superpose eq157483 eq157483
    | exact resolve eq157483 eq157483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157483
  have eq158498 : (k y y) = (M.op y y) := by grind
  have eq158526 : y = (k y y) := by
    first
    | (have i₁ := eq158498
       have i₂ := eq158286
       grind)
    | exact superpose eq158286 eq158498
    | exact resolve eq158498 eq158286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158498
  have eq158623 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq640 y y
       have i₂ := eq158526
       grind)
    | exact superpose eq158526 eq640
    | (have j0 := eq640 y y
       grind)
    | exact resolve eq640 eq158526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640 eq158526
  have eq158629 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq158623
  have eq158630 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq158629
  have eq158644 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq158630
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq158630
    | exact resolve eq158630 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158630
  have eq158668 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq157716 eq158644
    | exact resolve eq158644 eq157716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158644
  have eq167231 : y = (k y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq157586
       have i₂ := eq158286
       grind)
    | exact superpose eq158286 eq157586
    | exact resolve eq157586 eq158286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157586
  have eq167236 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq74
       have i₂ := eq167231
       grind)
    | exact superpose eq167231 eq74
    | exact resolve eq74 eq167231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq167252 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq3880 y
       have i₂ := eq167231
       grind)
    | exact superpose eq167231 eq3880
    | (have j0 := eq3880 y
       grind)
    | exact resolve eq3880 eq167231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3880 eq167231
  have eq167270 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq167252
  have eq167288 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq167270
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq167270
    | exact resolve eq167270 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167270
  have eq167301 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq157716 eq167236
    | exact resolve eq167236 eq157716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167236
  have eq167314 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq167288
    | exact resolve eq167288 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq167288
  have eq167327 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq167301
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq167301
    | exact resolve eq167301 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167301
  have eq167337 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq157716 eq167314
    | exact resolve eq167314 eq157716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167314
  have eq167350 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq157716 eq167327
    | exact resolve eq167327 eq157716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167327
  have eq167358 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq167337
       have r₂ := eq28
       grind)
    | exact resolve eq167337 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167337
  have eq167369 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq167358
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq167358
    | exact resolve eq167358 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167358
  have eq167377 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq157716 eq167369
    | exact resolve eq167369 eq157716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167369
  have eq167515 : (k (σ (M.op x y)) (σ x)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x x) := by grind
  clear eq167377
  have eq167541 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq157720 eq167515
    | exact resolve eq167515 eq157720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167515
  have eq168773 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq167541 eq167350
    | exact resolve eq167350 eq167541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167350 eq167541
  have eq168784 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq168773
  have eq168788 : y = (M.op x x) := by
    first
    | (have r₁ := eq168784
       have r₂ := eq28
       grind)
    | exact resolve eq168784 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168784
  have eq168802 : x = (M.op y y) := by
    first
    | (have i₁ := eq157484 x
       have i₂ := eq168788
       grind)
    | exact superpose eq168788 eq157484
    | exact resolve eq157484 eq168788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157484 eq168788
  have eq168832 : x = y := by
    first
    | (have i₁ := eq168802
       have i₂ := eq158286
       grind)
    | exact superpose eq158286 eq168802
    | exact resolve eq168802 eq158286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158286 eq168802
  have eq168843 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq168832
       grind)
    | exact superpose eq168832 eq25
    | exact resolve eq25 eq168832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq168832
  have eq169604 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq157716 eq168843
    | exact resolve eq168843 eq157716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157716 eq168843
  have eq169894 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq169604
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq169604
    | exact resolve eq169604 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq169604
  have eq170472 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq169894 eq157720
    | exact resolve eq157720 eq169894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157720 eq169894
  have eq170488 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq158668 eq170472
    | exact resolve eq170472 eq158668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158668 eq170472
  have eq170566 : False := by grind
  exact eq170566

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_pxx_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq61 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq9 (M.op X0 X3) (M.op x x) X0 X4
       have i₂ := eq9 X0 x x X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X1 (M.op X0 X0)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq61 X0 X0 X0
       grind)
    | exact superpose eq61 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | exact resolve eq12 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq338 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq339 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq338 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq342 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq339 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq339 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq339 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339
  have eq357 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq342 (σ X0)
       grind)
    | exact superpose eq342 eq15
    | exact resolve eq15 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq376 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq357 X0
       have i₂ := eq342 X0
       grind)
    | exact superpose eq342 eq357
    | exact resolve eq357 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342 eq357
  have eq428 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq376 X0
       grind)
    | exact superpose eq376 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq430 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq376 X0
       grind)
    | exact superpose eq376 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq431 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq428 X0 X1
       have j1 := eq430 X0 X1
       grind)
    | (have r₁ := eq428 X0 X1
       have r₂ := eq430 X0 X1
       grind)
    | exact resolve eq428 eq430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428
  have eq1073 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq431 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq431
    | exact resolve eq431 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1084 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq431 X0 (σ X1)
       grind)
    | exact superpose eq431 eq15
    | (have j1 := eq431 X0 (σ X1)
       grind)
    | exact resolve eq15 eq431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431
  have eq1124 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq1073 X0 (τ X1)
       grind)
    | exact superpose eq1073 eq17
    | (have j1 := eq1073 X0 (τ X1)
       grind)
    | exact resolve eq17 eq1073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1073
  have eq1330 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1124 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1124
    | exact resolve eq1124 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1124
  have eq1402 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1330 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1330
    | (have j0 := eq1330 X0 X1
       grind)
    | exact resolve eq1330 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1330
  have eq1904 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1084 x y
       grind)
    | exact superpose eq1084 eq16
    | (have j1 := eq1084 x y
       grind)
    | exact resolve eq16 eq1084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1084
  have eq2114 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1904
       have i₂ := eq1402 y x
       grind)
    | exact superpose eq1402 eq1904
    | (have j1 := eq1402 (σ y) (σ x)
       grind)
    | (have r₁ := eq1904
       have r₂ := eq1402 y x
       grind)
    | exact resolve eq1904 eq1402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1904
  have eq2115 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2114
  have eq2122 : ∀ X0 : G, x = (M.op x (M.op x X0)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq62 x y x
       have i₂ := eq2115
       grind)
    | exact superpose eq2115 eq62
    | exact resolve eq62 eq2115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq2211 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2122 y
       have i₂ := eq2115
       grind)
    | exact superpose eq2115 eq2122
    | exact resolve eq2122 eq2115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2115 eq2122
  have eq2226 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq2211
  have eq2230 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2226
       grind)
    | exact superpose eq2226 eq16
    | exact resolve eq16 eq2226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2236 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq61 X0 (σ x) (σ y)
       have i₂ := eq2226
       grind)
    | exact superpose eq2226 eq61
    | exact resolve eq61 eq2226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq2226
  have eq2332 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2236 (M.op x (σ x))
       have i₂ := eq2236 x
       grind)
    | exact superpose eq2236 eq2236
    | exact resolve eq2236 eq2236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2236
  have eq2356 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq2332
  have eq2360 : x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2356
       have i₂ := eq376 x
       grind)
    | exact superpose eq376 eq2356
    | exact resolve eq2356 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376 eq2356
  have eq2371 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) X0) = (k X0 (σ x)) ∨ (σ x) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq430 x X0
       have i₂ := eq2360
       grind)
    | exact superpose eq2360 eq430
    | (have j0 := eq430 x X0
       grind)
    | (have r₁ := eq430 x x
       have r₂ := eq2360
       grind)
    | exact resolve eq430 eq2360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2360
  have eq2399 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (σ x)) ∨ (σ x) = (σ (M.op x x)) := by
    intro X0
    first
    | (have j0 := eq2371 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2371
  have eq2402 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq2399 X0
       have j1 := eq430 x X0
       grind)
    | (have r₁ := eq2399 X0
       have r₂ := eq430 x x
       grind)
    | exact resolve eq2399 eq430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430 eq2399
  have eq2415 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq2402 (σ X0)
       grind)
    | exact superpose eq2402 eq15
    | exact resolve eq15 eq2402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2402
  have eq2532 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2415 y
       grind)
    | exact superpose eq2415 eq16
    | exact resolve eq16 eq2415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2415
  have eq2634 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2532
       have i₂ := eq1402 y x
       grind)
    | exact superpose eq1402 eq2532
    | (have j1 := eq1402 y x
       grind)
    | (have r₁ := eq2532
       have r₂ := eq1402 y x
       grind)
    | exact resolve eq2532 eq1402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1402
  have eq2635 : x = (M.op x y) := by grind
  clear eq2634
  have eq2638 : (σ x) ≠ (σ x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2230
       have i₂ := eq2635
       grind)
    | exact superpose eq2635 eq2230
    | exact resolve eq2230 eq2635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2230 eq2635
  have eq2656 : x = (M.op x x) := by grind
  clear eq2638
  have eq2660 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq92 x x
       have i₂ := eq2656
       grind)
    | exact superpose eq2656 eq92
    | (have r₁ := eq92 x x
       have r₂ := eq2656
       grind)
    | exact resolve eq92 eq2656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq2656
  have eq2695 : ∀ X0 : G, (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq2660 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2660
  have eq2796 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq2532
       have i₂ := eq2695 y
       grind)
    | exact superpose eq2695 eq2532
    | exact resolve eq2532 eq2695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2532 eq2695
  have eq2799 : False := by grind
  exact eq2799

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,Y) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyy_x_pxy_pxx_pxy_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
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
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 (M.op (M.op X1 X1) (M.op X1 X1)) X1
       have r₂ := eq13 X0 (M.op X1 X1)
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
  clear eq38
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
  have eq108 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq48 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq48
    | exact resolve eq48 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq132 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | (have i₁ := eq51 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq51
    | (have j0 := eq51 x
       grind)
    | exact resolve eq51 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | (have i₁ := eq51 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq51
    | (have j0 := eq51 y
       grind)
    | exact resolve eq51 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq51
    | (have j0 := eq51 (M.op x y)
       grind)
    | exact resolve eq51 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
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
  have eq177 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq16 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq16 X0 x x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq16 (M.op X0 X3) (M.op x x) X0 X4
       have i₂ := eq16 X0 x x X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 : G, x = (M.op (M.op (M.op X0 X1) x) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 x X0 X1 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x X0 X1 y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X1) (M.op X0 X1)) ∨ (k X2 (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op X2 (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op (M.op X0 X1) (M.op X0 X1))
       have i₂ := eq16 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq16 eq13
    | (have j0 := eq13 X0 (M.op X0 X1)
       grind)
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X1) (M.op X0 X1)) ∨ (k X2 (k (M.op X0 X1) (M.op X0 X1))) = (M.op X2 (k (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | exact superpose eq13 eq182
    | (have j0 := eq182 X0 X1 X2
       have j1 := eq13 X0 (M.op X0 X1)
       grind)
    | exact resolve eq182 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq184 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq177 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq177
    | (have j0 := eq177 x y X0
       grind)
    | exact resolve eq177 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq177
    | (have j0 := eq177 (σ x) (σ y) X0
       grind)
    | exact resolve eq177 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq177 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq177
    | (have j0 := eq177 X0 x y
       grind)
    | exact resolve eq177 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq177
    | (have j0 := eq177 X0 (σ x) (σ y)
       grind)
    | exact resolve eq177 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq177 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq177 X2 X0 x
       grind)
    | exact superpose eq177 eq177
    | exact resolve eq177 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193 : ∀ X0 X1 X2 X3 : G, (M.op X3 X0) = (M.op (M.op (M.op X1 X2) (M.op X3 X0)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op X3 X0) X1 X2 (M.op X0 x)
       have i₂ := eq177 X3 X0 x
       grind)
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X1 (M.op X0 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X0)
       have i₂ := eq177 X0 X0 X0
       grind)
    | exact superpose eq177 eq13
    | (have j0 := eq13 X0 X0
       grind)
    | exact resolve eq13 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X1 (k X0 X0)) = (M.op X1 (k X0 X0)) := by
    intro X0 X1
    first
    | exact superpose eq13 eq195
    | (have j0 := eq195 X0 X1
       have j1 := eq13 X0 X0
       grind)
    | exact resolve eq195 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq197 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) y) := by
    intro X0
    first
    | exact superpose eq184 eq177
    | exact resolve eq177 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq207 : ∀ X1 : G, (M.op x y) = (M.op x (M.op (M.op x y) X1)) := by
    intro X1
    first
    | exact superpose eq188 eq177
    | exact resolve eq177 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq212 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) X1)) := by
    intro X1
    first
    | exact superpose eq189 eq177
    | exact resolve eq177 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq764 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq28 X0 X0
       grind)
    | exact superpose eq28 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq28 X1 X0
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq28 X0 X0
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X1)
       have r₂ := eq28 (M.op (M.op X1 X1) (M.op X1 X1)) X1
       grind)
    | exact resolve eq13 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq768 : ∀ X0 X1 X2 : G, (M.op (k X0 X1) (M.op X1 X2)) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq177 X0 X1 X2
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq177
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq177 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq769 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 (M.op (k X0 X1) X2)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq178 X0 X1 x
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq178
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq178 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq779 : ∀ X0 : G, (σ x) = (M.op (k X0 (σ x)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq189 X0
       have i₂ := eq28 X0 sF2
       grind)
    | exact superpose eq28 eq189
    | (have j1 := eq28 X0 (σ x)
       grind)
    | exact resolve eq189 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq790 : ∀ X0 X1 : G, x = (k (M.op (M.op X0 X1) x) (M.op x y)) ∨ (M.op (M.op X0 X1) x) = (M.op (M.op x y) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq179 X0 X1
       have i₂ := eq28 (M.op (M.op X0 X1) x) sF0
       grind)
    | exact superpose eq28 eq179
    | (have j1 := eq28 (M.op (M.op X0 X1) x) (M.op x y)
       grind)
    | exact resolve eq179 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq798 : (M.op x y) = (k x y) ∨ x = (M.op y y) := by
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
  have eq803 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
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
  have eq808 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq809 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq764 X0 X1
       have j1 := eq13 X1 X0
       grind)
    | (have r₁ := eq764 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq764 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764
  have eq811 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq798
       grind)
    | exact superpose eq798 eq41
    | exact resolve eq41 eq798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq812 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq811
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq811
    | exact resolve eq811 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq811
  have eq814 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq812
    | exact resolve eq812 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq812
  have eq816 : ∀ X0 X1 : G, (k X0 X0) ≠ X1 ∨ (k X0 X0) = X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq28 X1 X1
       grind)
    | exact superpose eq28 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq28 (k X1 X0) X1
       grind)
    | (have r₁ := eq12 (k X1 X1) X1
       have r₂ := eq28 X1 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq28 X0 X1
       grind)
    | (have r₁ := eq12 (M.op X1 X1) X1
       have r₂ := eq28 (M.op X1 X1) X1
       grind)
    | exact resolve eq12 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq819 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq12 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq820 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq819 X0
       have i₂ := eq177 X0 X0 X0
       grind)
    | (have i₁ := eq819 X0
       have i₂ := eq177 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq177 eq819
    | (have j0 := eq819 X0
       grind)
    | exact resolve eq819 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq819
  have eq823 : ∀ X0 X1 : G, (k X0 X0) ≠ X1 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq816 X0 X1
       have j1 := eq808 X0
       grind)
    | (have r₁ := eq816 X0 (M.op (k X0 X0) (k X0 X0))
       have r₂ := eq808 (k X0 X0)
       grind)
    | (have r₁ := eq816 X0 X1
       have r₂ := eq808 X0
       grind)
    | exact resolve eq816 eq808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq816
  have eq824 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq28 eq820
    | (have j0 := eq820 X0
       have j1 := eq28 X0 X0
       grind)
    | exact resolve eq820 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq820
  have eq830 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq808 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq808
    | (have j0 := eq808 (σ X0)
       grind)
    | exact resolve eq808 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq833 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq814 eq803
    | exact resolve eq803 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq840 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq833
       have r₂ := eq27
       grind)
    | exact resolve eq833 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq833
  have eq844 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq840
       have i₂ := eq28 sF3 sF3
       grind)
    | exact superpose eq28 eq840
    | (have j1 := eq28 x y
       grind)
    | exact resolve eq840 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq847 : ∀ X0 : G, (σ x) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq840 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | exact resolve eq13 eq840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq850 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq840 eq28
    | (have j0 := eq28 x y
       grind)
    | exact resolve eq28 eq840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq851 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (σ x)) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq840 eq177
    | exact resolve eq177 eq840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq853 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op (σ x) X0)) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq840 eq178
    | exact resolve eq178 eq840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq856 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ y)) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq840 eq191
    | exact resolve eq191 eq840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq859 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq850 eq844
    | exact resolve eq844 eq850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844
  have eq893 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq840 eq851
    | exact resolve eq851 eq840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851
  have eq909 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by grind
  clear eq893
  have eq911 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq909
       have i₂ := eq28 sF2 sF2
       grind)
    | exact superpose eq28 eq909
    | (have j1 := eq28 x y
       grind)
    | exact resolve eq909 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq917 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq909 eq28
    | (have j0 := eq28 x y
       grind)
    | exact resolve eq28 eq909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq993 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq850 eq116
    | exact resolve eq116 eq850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq999 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30 eq993
    | exact resolve eq993 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq993
  have eq1009 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq917 eq98
    | exact resolve eq98 eq917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917
  have eq1015 : y = (k x x) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq32 eq1009
    | exact resolve eq1009 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1009
  have eq1025 : (τ (σ x)) = (k y y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq859 eq116
    | exact resolve eq116 eq859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq859
  have eq1032 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (k y y) := by
    first
    | exact superpose eq30 eq1025
    | exact resolve eq1025 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1025
  have eq1114 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ x = (k y y) := by
    first
    | exact superpose eq1032 eq856
    | exact resolve eq856 eq1032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856
  have eq1116 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) ∨ x = (M.op y y) ∨ x = (k y y) := by
    intro X0
    first
    | exact superpose eq1032 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq1032
       grind)
    | exact resolve eq13 eq1032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1127 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) ∨ x = (M.op y y) ∨ x = (k y y) := by
    intro X0
    first
    | (have j0 := eq1116 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1116
  have eq1128 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (k y y) := by grind
  clear eq1114
  have eq1134 : x = (k y y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1128
    | exact resolve eq1128 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1128
  have eq1186 : (τ (σ y)) = (k x x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq911 eq98
    | exact resolve eq98 eq911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1195 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ y = (k x x) := by
    first
    | exact superpose eq32 eq1186
    | exact resolve eq1186 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1186
  have eq1198 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq809 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq809
    | (have j0 := eq809 (σ X0) X1
       grind)
    | exact resolve eq809 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1211 : y = (k x y) ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq824 y
       have i₂ := eq1134
       grind)
    | exact superpose eq1134 eq824
    | (have j0 := eq824 y
       grind)
    | exact resolve eq824 eq1134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1212 : y = (k x y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq824 y
       have i₂ := eq999
       grind)
    | exact superpose eq999 eq824
    | (have j0 := eq824 y
       grind)
    | exact resolve eq824 eq999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1213 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq911 eq824
    | (have j0 := eq824 (σ x)
       grind)
    | exact resolve eq824 eq911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq911
  have eq1217 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq850 eq824
    | (have j0 := eq824 (σ y)
       grind)
    | exact resolve eq824 eq850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850
  have eq1228 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by grind
  clear eq1213
  have eq1238 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq814 eq1217
    | exact resolve eq1217 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1217
  have eq1242 : y = (M.op y y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq798 eq1212
    | exact resolve eq1212 eq798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1212
  have eq1243 : y = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq798 eq1211
    | exact resolve eq1211 eq798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1211
  have eq1254 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq840 eq1238
    | exact resolve eq1238 eq840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq840 eq1238
  have eq1255 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1254
  have eq1512 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) ∨ x = (M.op y y) ∨ y = (k x x) := by
    intro X0
    first
    | exact superpose eq1195 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq1195
       grind)
    | exact resolve eq13 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1523 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) ∨ x = (M.op y y) ∨ y = (k x x) := by
    intro X0
    first
    | (have j0 := eq1512 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1512
  have eq1557 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1228 eq108
    | exact resolve eq108 eq1228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq1228
  have eq1560 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (k y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30 eq1557
    | exact resolve eq1557 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1557
  have eq1592 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) ∨ x = (k y x) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq1560 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq1560
       grind)
    | exact resolve eq13 eq1560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1603 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) ∨ x = (k y x) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq1592 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1592
  have eq1790 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op (k X0 X0) (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq823 X0 (k X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq823
  have eq1792 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq824 eq1790
    | (have j0 := eq1790 X0
       have j1 := eq824 X0
       grind)
    | exact resolve eq1790 eq824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1790
  have eq1847 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq1242
       grind)
    | exact superpose eq1242 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq1242
       grind)
    | exact resolve eq13 eq1242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1242
  have eq1861 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq1847 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1847
  have eq2023 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq1243
       grind)
    | exact superpose eq1243 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq1243
       grind)
    | exact resolve eq13 eq1243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1243
  have eq2039 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq2023 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2023
  have eq2991 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (k y y) ∨ x = (M.op y y) ∨ x = (k y y) := by
    first
    | exact superpose eq1127 eq1032
    | exact resolve eq1032 eq1127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032 eq1127
  have eq3014 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (k y y) := by grind
  clear eq2991
  have eq3099 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op y y) ∨ x = (k y y) := by
    first
    | exact superpose eq3014 eq142
    | exact resolve eq142 eq3014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3014
  have eq3121 : x = (k y y) ∨ x = (M.op y y) ∨ x = (k x x) := by
    first
    | exact superpose eq30 eq3099
    | exact resolve eq3099 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3099
  have eq3128 : y = (k x y) ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq824 y
       have i₂ := eq3121
       grind)
    | exact superpose eq3121 eq824
    | (have j0 := eq824 y
       grind)
    | exact resolve eq824 eq3121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3131 : y = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ x = (k x x) := by
    first
    | exact superpose eq798 eq3128
    | exact resolve eq3128 eq798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798 eq3128
  have eq3966 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op y y) ∨ y = (k x x) ∨ x = (M.op y y) ∨ y = (k x x) := by
    first
    | exact superpose eq1523 eq1195
    | exact resolve eq1195 eq1523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1195 eq1523
  have eq3995 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op y y) ∨ y = (k x x) := by grind
  clear eq3966
  have eq4094 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op y y) ∨ y = (k x x) := by
    first
    | exact superpose eq3995 eq142
    | exact resolve eq142 eq3995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3995
  have eq4119 : y = (k x x) ∨ x = (M.op y y) ∨ x = (k x x) := by
    first
    | exact superpose eq30 eq4094
    | exact resolve eq4094 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4094
  have eq4129 : x ≠ y ∨ x = (M.op y y) ∨ x = (k x x) := by grind
  have eq4440 : (σ x) = (k (σ x) (σ x)) ∨ x = (k y x) ∨ x = (M.op y y) ∨ x = (k y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1603 eq1560
    | exact resolve eq1560 eq1603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1560 eq1603
  have eq4473 : (σ x) = (k (σ x) (σ x)) ∨ x = (k y x) ∨ x = (M.op y y) := by grind
  clear eq4440
  have eq4578 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (k y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq4473 eq142
    | exact resolve eq142 eq4473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4473
  have eq4605 : x = (k y x) ∨ x = (k x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30 eq4578
    | exact resolve eq4578 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4578
  have eq5644 : x ≠ (k y y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by grind
  clear eq1861
  have eq5678 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq5644
       have r₂ := eq999
       grind)
    | exact resolve eq5644 eq999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq999 eq5644
  have eq5704 : y = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq184 y
       have i₂ := eq5678
       grind)
    | exact superpose eq5678 eq184
    | exact resolve eq184 eq5678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5738 : x = (M.op y (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5704 eq188
    | exact resolve eq188 eq5704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5704
  have eq5766 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (k y (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5738 eq28
    | (have j0 := eq28 y (M.op x y)
       grind)
    | exact resolve eq28 eq5738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6571 : (M.op x y) = (M.op y y) ∨ x = (k y (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5766 eq197
    | exact resolve eq197 eq5766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6576 : y = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (k y (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5766 eq28
    | exact resolve eq28 eq5766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6594 : y = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (k y (M.op x y)) ∨ (σ x) = (σ y) := by grind
  clear eq6576
  have eq6666 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (k y (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq5678
       have i₂ := eq6571
       grind)
    | exact superpose eq6571 eq5678
    | exact resolve eq5678 eq6571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6571
  have eq6706 : x = (k y (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq6666
  have eq7349 : x ≠ (k y y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2039
  have eq7392 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq7349
       have r₂ := eq1134
       grind)
    | exact resolve eq7349 eq1134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1134 eq7349
  have eq10237 : ∀ X0 : G, y ≠ (M.op y y) ∨ (k X0 (k y y)) = (M.op X0 (k y y)) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ x = (k x x) := by
    intro X0
    first
    | (have i₁ := eq183 y y x
       have i₂ := eq3131
       grind)
    | exact superpose eq3131 eq183
    | exact resolve eq183 eq3131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10271 : ∀ X0 : G, (k X0 (k y y)) = (M.op X0 (k y y)) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ x = (k x x) := by
    intro X0
    first
    | (have j0 := eq10237 X0
       grind)
    | (have r₁ := eq10237 X0
       have r₂ := eq3131
       grind)
    | exact resolve eq10237 eq3131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3131 eq10237
  have eq10273 : ∀ X0 : G, (k X0 x) = (M.op X0 x) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ x = (k x x) := by
    intro X0
    first
    | exact superpose eq3121 eq10271
    | exact resolve eq10271 eq3121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3121 eq10271
  have eq10275 : ∀ X0 : G, (k X0 x) = (M.op X0 x) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq10273 X0
       have j1 := eq809 x X0
       grind)
    | (have r₁ := eq10273 X0
       have r₂ := eq809 x x
       grind)
    | exact resolve eq10273 eq809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10273
  have eq10370 : (M.op (σ x) (σ y)) = (M.op (σ x) (k (M.op (σ x) (σ y)) x)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq212 x
       have i₂ := eq10275 sF4
       grind)
    | exact superpose eq10275 eq212
    | exact resolve eq212 eq10275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212 eq10275
  have eq10412 : (σ x) = (M.op (σ x) (k (σ x) x)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq7392 eq10370
    | exact resolve eq10370 eq7392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7392 eq10370
  have eq10679 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq10412 eq853
    | exact resolve eq853 eq10412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq853 eq10412
  have eq10702 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq10679
  have eq10709 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5678 eq10702
    | exact resolve eq10702 eq5678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10702
  have eq10736 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq10709 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq10709
       grind)
    | exact resolve eq13 eq10709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10758 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq10736 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10736
  have eq11098 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10758 eq10709
    | exact resolve eq10709 eq10758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10709 eq10758
  have eq11136 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq11098
  have eq11270 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11136 eq142
    | exact resolve eq142 eq11136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq11136
  have eq11322 : x = (k x x) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq11270
    | exact resolve eq11270 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11270
  have eq14547 : x = (M.op y y) ∨ x = (M.op x x) ∨ x = (M.op y y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq1792 x
       have i₂ := eq4119
       grind)
    | exact superpose eq4119 eq1792
    | (have j0 := eq1792 x
       grind)
    | exact resolve eq1792 eq4119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4119
  have eq14608 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (k X0 X0)) = (M.op X1 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (k X0 X0)
       have i₂ := eq1792 X0
       grind)
    | exact superpose eq1792 eq13
    | (have j0 := eq13 X1 (k X0 X0)
       have j1 := eq1792 X0
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq1792 X0
       grind)
    | exact resolve eq13 eq1792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14640 : x = (M.op y y) ∨ x = (M.op x x) ∨ x = (k x x) := by grind
  clear eq14547
  have eq14645 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (k X0 X0)) = (M.op X1 (k X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq14608 X0 X1
       have j1 := eq196 X0 X1
       grind)
    | (have r₁ := eq14608 X0 X1
       have r₂ := eq196 X0 X1
       grind)
    | exact resolve eq14608 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196 eq14608
  have eq14659 : x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq808 x
       grind)
    | (have r₁ := eq14640
       have r₂ := eq808 x
       grind)
    | exact resolve eq14640 eq808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14640
  have eq14809 : y = (M.op (M.op x y) x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq184 y
       have i₂ := eq14659
       grind)
    | exact superpose eq14659 eq184
    | exact resolve eq184 eq14659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14827 : ∀ X0 : G, y = (M.op (M.op X0 y) x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq177 X0 y y
       have i₂ := eq14659
       grind)
    | exact superpose eq14659 eq177
    | exact resolve eq177 eq14659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14829 : ∀ X0 : G, x = (M.op y (M.op x X0)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq178 y y x
       have i₂ := eq14659
       grind)
    | exact superpose eq14659 eq178
    | exact resolve eq178 eq14659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14874 : (M.op x y) = (M.op x x) ∨ y = (k (M.op x y) x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq14809 eq28
    | (have j0 := eq28 (M.op x y) x
       grind)
    | exact resolve eq28 eq14809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14809
  have eq14967 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq14827 y
       have i₂ := eq14659
       grind)
    | exact superpose eq14659 eq14827
    | exact resolve eq14827 eq14659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14827
  have eq15013 : y = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq14967
  have eq15051 : y = (k x x) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq28 x x
       have i₂ := eq15013
       grind)
    | exact superpose eq15013 eq28
    | (have j0 := eq28 x x
       grind)
    | exact resolve eq28 eq15013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15071 : x ≠ y ∨ x = (M.op x x) := by grind
  clear eq15013
  have eq15076 : y = (k x x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq15051
       have r₂ := eq15071
       grind)
    | exact resolve eq15051 eq15071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15051
  have eq15083 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq15076
       grind)
    | exact superpose eq15076 eq40
    | exact resolve eq40 eq15076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15076
  have eq15107 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq15083
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15083
    | exact resolve eq15083 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15083
  have eq15110 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq15107
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15107
    | exact resolve eq15107 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15107
  have eq15157 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq15110 eq1792
    | (have j0 := eq1792 (σ x)
       grind)
    | exact resolve eq1792 eq15110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15161 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq15110 eq808
    | (have j0 := eq808 (σ x)
       grind)
    | exact resolve eq808 eq15110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16180 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ y = (k (M.op x y) x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq28 x x
       have i₂ := eq14874
       grind)
    | exact superpose eq14874 eq28
    | (have j0 := eq28 x x
       grind)
    | exact resolve eq28 eq14874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16201 : x ≠ (M.op x y) ∨ y = (k (M.op x y) x) ∨ x = (M.op x x) := by grind
  clear eq14874
  have eq16211 : (M.op x y) = (k x x) ∨ y = (k (M.op x y) x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq16180
       have r₂ := eq16201
       grind)
    | exact resolve eq16180 eq16201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16180 eq16201
  have eq16701 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (k (M.op x y) x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq16211
       grind)
    | exact superpose eq16211 eq40
    | exact resolve eq40 eq16211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16211
  have eq16743 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (k (M.op x y) x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16701
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16701
    | exact resolve eq16701 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16701
  have eq16745 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (k (M.op x y) x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq16743
    | exact resolve eq16743 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16743
  have eq16747 : y = (k (M.op x y) x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq15110 eq16745
    | exact resolve eq16745 eq15110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15110 eq16745
  have eq16753 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq16747 eq40
    | exact resolve eq40 eq16747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16747
  have eq16771 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq16753
    | exact resolve eq16753 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16753
  have eq16773 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16771
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16771
    | exact resolve eq16771 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16771
  have eq23168 : ∀ X0 : G, x = (M.op y (M.op x X0)) ∨ y = (M.op x x) ∨ x = (k x x) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq769 y x x
       have i₂ := eq4605
       grind)
    | exact superpose eq4605 eq769
    | (have j0 := eq769 y x x
       grind)
    | exact resolve eq769 eq4605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4605
  have eq23472 : ∀ X0 : G, x = (M.op y (M.op x X0)) ∨ x = y ∨ x = (k x x) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq14829 eq23168
    | (have j0 := eq23168 X0
       have j1 := eq14829 X0
       grind)
    | exact resolve eq23168 eq14829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14829 eq23168
  have eq23502 : ∀ X0 : G, x = (M.op y (M.op x X0)) ∨ x = (k x x) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq23472 X0
       grind)
    | (have r₁ := eq23472 X0
       have r₂ := eq4129
       grind)
    | exact resolve eq23472 eq4129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4129 eq23472
  have eq23517 : ∀ X0 : G, x = (M.op (M.op x y) (M.op x X0)) ∨ x = (k x x) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq11322 eq23502
    | exact resolve eq23502 eq11322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11322 eq23502
  have eq24441 : x = (k x x) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq23517 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq23517
    | (have j0 := eq23517 y
       grind)
    | exact resolve eq23517 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24475 : ∀ X1 : G, x ≠ (M.op x x) ∨ (k X1 (k x x)) = (M.op X1 (k x x)) ∨ x = (k x x) ∨ x = (M.op y y) := by
    intro X1
    first
    | exact superpose eq23517 eq183
    | exact resolve eq183 eq23517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq23517
  have eq24512 : ∀ X1 : G, (k X1 (k x x)) = (M.op X1 (k x x)) ∨ x = (k x x) ∨ x = (M.op y y) := by
    intro X1
    first
    | (have j0 := eq24475 X1
       grind)
    | (have r₁ := eq24475 X1
       have r₂ := eq14659
       grind)
    | exact resolve eq24475 eq14659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14659 eq24475
  have eq24515 : ∀ X1 : G, (k X1 (k x x)) = (M.op X1 (k x x)) ∨ x = (M.op y y) := by
    intro X1
    first
    | (have j0 := eq24512 X1
       have j1 := eq14645 x X1
       grind)
    | (have r₁ := eq24512 X1
       have r₂ := eq14645 x X1
       grind)
    | exact resolve eq24512 eq14645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14645 eq24512
  have eq24561 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq830 x
       have i₂ := eq24441
       grind)
    | exact superpose eq24441 eq830
    | (have j0 := eq830 x
       grind)
    | exact resolve eq830 eq24441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24441
  have eq24573 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op y y) := by grind
  clear eq24561
  have eq24597 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq24573
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq24573
    | exact resolve eq24573 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24573
  have eq24725 : (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq24597 eq909
    | exact resolve eq909 eq24597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq909 eq24597
  have eq24798 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq24725
  have eq25860 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq24515 x
       have i₂ := eq1015
       grind)
    | exact superpose eq1015 eq24515
    | exact resolve eq24515 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1015 eq24515
  have eq26001 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq25860 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25860
  have eq26026 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op X0 (M.op x y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq5678 eq26001
    | exact resolve eq26001 eq5678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26001
  have eq31772 : x = (k (M.op y x) (M.op x y)) ∨ y = (M.op y x) ∨ x = (k y (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5766 eq790
    | exact resolve eq790 eq5766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq790 eq5766
  have eq31887 : (M.op x y) = (k (M.op y (M.op x y)) (M.op x y)) ∨ y = (M.op y x) ∨ x = (k y (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6706 eq31772
    | exact resolve eq31772 eq6706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31772
  have eq31891 : (M.op x y) = (k (M.op y (M.op x y)) (M.op x y)) ∨ y = (M.op y (M.op x y)) ∨ x = (k y (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6706 eq31887
    | exact resolve eq31887 eq6706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31887
  have eq31895 : (M.op x y) = (k x (M.op x y)) ∨ y = (M.op y (M.op x y)) ∨ x = (k y (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5738 eq31891
    | exact resolve eq31891 eq5738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31891
  have eq31899 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op y (M.op x y)) ∨ x = (k y (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6706 eq31895
    | exact resolve eq31895 eq6706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31895
  have eq31904 : y = (M.op x y) ∨ y = (M.op y (M.op x y)) ∨ x = (k y (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6594 eq31899
    | exact resolve eq31899 eq6594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6594 eq31899
  have eq31905 : y = (M.op x y) ∨ y = (M.op y (M.op x y)) ∨ x = (k y (M.op x y)) ∨ (σ x) = (σ y) := by grind
  clear eq31904
  have eq31909 : y = (M.op x y) ∨ x = y ∨ x = (k y (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq5738 eq31905
    | exact resolve eq31905 eq5738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5738 eq31905
  have eq31913 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (k y (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq6706 eq31909
    | exact resolve eq31909 eq6706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6706 eq31909
  have eq31914 : x = (k y (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq31913
  have eq32230 : y = (M.op (M.op x y) (k y (M.op x y))) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26026 eq184
    | exact resolve eq184 eq26026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32249 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26026 eq24798
    | exact resolve eq24798 eq26026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24798
  have eq32290 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq32249
  have eq32345 : (M.op x y) = (M.op (M.op x y) (k (M.op x y) (M.op x y))) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq5678 eq32230
    | exact resolve eq32230 eq5678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32230
  have eq32360 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq32290 eq32345
    | exact resolve eq32345 eq32290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32290 eq32345
  have eq32419 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq32360 eq207
    | exact resolve eq207 eq32360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32360
  have eq32574 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq32419 eq197
    | exact resolve eq197 eq32419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32419
  have eq32644 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq5678 eq32574
    | exact resolve eq32574 eq5678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5678 eq32574
  have eq32712 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq32644 eq26026
    | exact resolve eq26026 eq32644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26026 eq32644
  have eq32750 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq32712
  have eq33000 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k X0 (σ (M.op x y))) = (M.op X0 (σ (M.op x y))) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq32750 eq1198
    | (have j0 := eq1198 (M.op x y) X0
       grind)
    | exact resolve eq1198 eq32750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1198 eq32750
  have eq33007 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (M.op X0 (σ (M.op x y))) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq33000 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33000
  have eq33020 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (M.op X0 (σ (M.op x y))) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq20 eq33007
    | (have j0 := eq33007 X0
       grind)
    | exact resolve eq33007 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33007
  have eq33026 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq1255 eq33020
    | exact resolve eq33020 eq1255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1255 eq33020
  have eq33031 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq33026 X0
       have j1 := eq847 X0
       grind)
    | (have r₁ := eq33026 X0
       have r₂ := eq847 X0
       grind)
    | exact resolve eq33026 eq847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq847 eq33026
  have eq35723 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq33031 eq26
    | (have j1 := eq33031 (σ x)
       grind)
    | exact resolve eq26 eq33031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33031
  have eq35791 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq814 eq35723
    | exact resolve eq35723 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814 eq35723
  have eq35840 : x = (M.op y y) := by
    first
    | (have r₁ := eq35791
       have r₂ := eq27
       grind)
    | exact resolve eq35791 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35791
  have eq35876 : y = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq184 y
       have i₂ := eq35840
       grind)
    | exact superpose eq35840 eq184
    | exact resolve eq184 eq35840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq35905 : x = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq28 y y
       have i₂ := eq35840
       grind)
    | exact superpose eq35840 eq28
    | exact resolve eq28 eq35840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35906 : ∀ X0 : G, y = (M.op (M.op X0 y) x) := by
    intro X0
    first
    | (have i₁ := eq177 X0 y y
       have i₂ := eq35840
       grind)
    | exact superpose eq35840 eq177
    | exact resolve eq177 eq35840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35945 : x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq35876 eq188
    | exact resolve eq188 eq35876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35963 : (M.op x y) = (M.op x x) ∨ y = (k (M.op x y) x) := by
    first
    | exact superpose eq35876 eq28
    | (have j0 := eq28 (M.op x y) x
       grind)
    | exact resolve eq28 eq35876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35876
  have eq36023 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (k y (M.op x y)) := by
    first
    | exact superpose eq35945 eq28
    | (have j0 := eq28 y (M.op x y)
       grind)
    | exact resolve eq28 eq35945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36105 : y = (M.op x x) := by
    first
    | (have i₁ := eq35906 y
       have i₂ := eq35840
       grind)
    | exact superpose eq35840 eq35906
    | exact resolve eq35906 eq35840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35906
  have eq36231 : ∀ X0 : G, y ≠ X0 ∨ x = y ∨ (M.op X0 X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq36105
       grind)
    | exact superpose eq36105 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq36105
       grind)
    | exact resolve eq12 eq36105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36235 : y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq28 x x
       have i₂ := eq36105
       grind)
    | exact superpose eq36105 eq28
    | exact resolve eq28 eq36105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36250 : ∀ X0 : G, x = (M.op (k X0 x) y) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq768 X0 x x
       have i₂ := eq36105
       grind)
    | exact superpose eq36105 eq768
    | exact resolve eq768 eq36105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36650 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq35905
       grind)
    | exact superpose eq35905 eq41
    | exact resolve eq41 eq35905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq36661 : y = (k x y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq824 y
       have i₂ := eq35905
       grind)
    | exact superpose eq35905 eq824
    | (have j0 := eq824 y
       grind)
    | exact resolve eq824 eq35905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824
  have eq36662 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq830 y
       have i₂ := eq35905
       grind)
    | exact superpose eq35905 eq830
    | (have j0 := eq830 y
       grind)
    | exact resolve eq830 eq35905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830 eq35905
  have eq36677 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq36662
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq36662
    | exact resolve eq36662 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36662
  have eq36678 : x = y ∨ y = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq36661
       have i₂ := eq35840
       grind)
    | exact superpose eq35840 eq36661
    | exact resolve eq36661 eq35840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36661
  have eq36679 : y = (k x y) ∨ x = y := by grind
  clear eq36678
  have eq36681 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq36650
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq36650
    | exact resolve eq36650 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36650
  have eq36685 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq36677
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq36677
    | exact resolve eq36677 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36677
  have eq36686 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq36681
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq36681
    | exact resolve eq36681 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36681
  have eq36690 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq36685
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq36685
    | exact resolve eq36685 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36685
  have eq36697 : (σ y) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq36679
       grind)
    | exact superpose eq36679 eq36
    | exact resolve eq36 eq36679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq36706 : (σ y) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq36697
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq36697
    | exact resolve eq36697 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36697
  have eq36726 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq36686 eq1792
    | (have j0 := eq1792 (σ y)
       grind)
    | exact resolve eq1792 eq36686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36686
  have eq36753 : (σ y) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq36235
       grind)
    | exact superpose eq36235 eq40
    | exact resolve eq40 eq36235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36803 : (σ y) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq36753
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq36753
    | exact resolve eq36753 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36753
  have eq36808 : (σ y) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq36803
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq36803
    | exact resolve eq36803 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36803
  have eq36817 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq36706 eq803
    | exact resolve eq803 eq36706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803 eq36706
  have eq36874 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq36808 eq1792
    | (have j0 := eq1792 (σ x)
       grind)
    | exact resolve eq1792 eq36808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1792
  have eq36876 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op (σ x) X0)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq36808 eq768
    | (have j0 := eq768 (σ x) (σ x) x
       grind)
    | exact resolve eq768 eq36808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36808
  have eq37611 : y = (k (M.op x y) x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq36105
       have i₂ := eq35963
       grind)
    | exact superpose eq35963 eq36105
    | exact resolve eq36105 eq35963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37633 : y = (k (M.op x y) x) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq188 x
       have i₂ := eq35963
       grind)
    | exact superpose eq35963 eq188
    | exact resolve eq188 eq35963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188 eq35963
  have eq37702 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq37611 eq40
    | exact resolve eq40 eq37611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq37737 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq37702
    | exact resolve eq37702 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37702
  have eq37739 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq37737
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37737
    | exact resolve eq37737 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37737
  have eq37758 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) X0)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq37739 eq769
    | (have j0 := eq769 (σ (M.op x y)) (σ x) x
       grind)
    | exact resolve eq769 eq37739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37739
  have eq37795 : (M.op x y) = (M.op y y) ∨ x = (k y (M.op x y)) := by
    first
    | exact superpose eq36023 eq197
    | exact resolve eq197 eq36023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37807 : ∀ X0 : G, y ≠ (M.op x y) ∨ (k X0 (M.op x y)) = (M.op X0 (M.op x y)) ∨ x = (k y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq36023 eq13
    | (have j0 := eq13 X0 (M.op x y)
       grind)
    | exact resolve eq13 eq36023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37810 : y = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (k y (M.op x y)) := by
    first
    | exact superpose eq36023 eq28
    | exact resolve eq28 eq36023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36023
  have eq37845 : x = (k y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq37795
       have i₂ := eq35840
       grind)
    | exact superpose eq35840 eq37795
    | exact resolve eq37795 eq35840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37795
  have eq39290 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq36817 eq177
    | exact resolve eq177 eq36817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43639 : x = y ∨ (k y x) = (M.op y y) := by
    first
    | (have j0 := eq36231 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36231
  have eq43640 : x = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq43639
       have i₂ := eq35840
       grind)
    | exact superpose eq35840 eq43639
    | exact resolve eq43639 eq35840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35840 eq43639
  have eq43647 : (σ x) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq43640
       grind)
    | exact superpose eq43640 eq37
    | exact resolve eq37 eq43640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq43640
  have eq43666 : (σ x) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq43647
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq43647
    | exact resolve eq43647 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43647
  have eq43686 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op (σ x) X0)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq43666 eq769
    | (have j0 := eq769 (σ y) (σ x) x
       grind)
    | exact resolve eq769 eq43666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43691 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op (σ x) X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq36876 eq43686
    | (have j0 := eq43686 X0
       have j1 := eq36876 X0
       grind)
    | exact resolve eq43686 eq36876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36876 eq43686
  have eq43708 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq36726 eq15157
    | exact resolve eq15157 eq36726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15157
  have eq43714 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq36726 eq185
    | exact resolve eq185 eq36726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq43774 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have r₁ := eq43708
       have r₂ := eq15161
       grind)
    | exact resolve eq43708 eq15161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15161 eq43708
  have eq43779 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq43774
       have r₂ := eq15071
       grind)
    | exact resolve eq43774 eq15071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15071 eq43774
  have eq43782 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq43779
       have i₂ := eq36105
       grind)
    | exact superpose eq36105 eq43779
    | exact resolve eq43779 eq36105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43779
  have eq43991 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (k y (M.op x y)) := by
    first
    | exact superpose eq37810 eq42
    | exact resolve eq42 eq37810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37810
  have eq44014 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (k y (M.op x y)) := by
    first
    | exact superpose eq20 eq43991
    | exact resolve eq43991 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43991
  have eq44020 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (k y (M.op x y)) := by
    first
    | (have i₁ := eq44014
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq44014
    | exact resolve eq44014 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44014
  have eq44026 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (k y (M.op x y)) := by
    first
    | exact superpose eq31914 eq44020
    | exact resolve eq44020 eq31914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31914 eq44020
  have eq44261 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq43782 eq189
    | exact resolve eq189 eq43782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189 eq43782
  have eq46065 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq36817 eq39290
    | exact resolve eq39290 eq36817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39290
  have eq46137 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq46065
  have eq46573 : (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (k y (M.op x y)) := by
    first
    | exact superpose eq44026 eq134
    | exact resolve eq134 eq44026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134 eq44026
  have eq46596 : x = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (k y (M.op x y)) := by
    first
    | exact superpose eq30 eq46573
    | exact resolve eq46573 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46573
  have eq46600 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (k y (M.op x y)) := by
    first
    | exact superpose eq37845 eq46596
    | exact resolve eq46596 eq37845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37845 eq46596
  have eq46784 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq26 eq43691
    | (have j0 := eq43691 (σ y)
       grind)
    | exact resolve eq43691 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46817 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq43691 eq177
    | exact resolve eq177 eq43691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47062 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (k X0 (M.op x y)) = (M.op X0 (M.op x y)) ∨ y = (M.op x y) ∨ x = (k y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq46600 eq809
    | (have j0 := eq809 (M.op x y) X0
       grind)
    | (have r₁ := eq809 (M.op x y) x
       have r₂ := eq46600
       grind)
    | exact resolve eq809 eq46600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq809 eq46600
  have eq47077 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op X0 (M.op x y)) ∨ y = (M.op x y) ∨ x = (k y (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq47062 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47062
  have eq47096 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op X0 (M.op x y)) ∨ x = (k y (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq47077 X0
       have j1 := eq37807 X0
       grind)
    | (have r₁ := eq47077 X0
       have r₂ := eq37807 X0
       grind)
    | exact resolve eq47077 eq37807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37807 eq47077
  have eq47286 : x = (k y (M.op x y)) ∨ x = (k y (M.op x y)) := by
    first
    | exact superpose eq47096 eq35945
    | exact resolve eq35945 eq47096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47096
  have eq47350 : x = (k y (M.op x y)) := by grind
  clear eq47286
  have eq47417 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq47350 eq42
    | exact resolve eq42 eq47350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq47423 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq47417
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq47417
    | exact resolve eq47417 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47417
  have eq47425 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq47423
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq47423
    | exact resolve eq47423 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47423
  have eq47432 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op (σ x) X0)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq47425 eq769
    | (have j0 := eq769 (σ y) (σ (M.op x y)) x
       grind)
    | exact resolve eq769 eq47425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769
  have eq47433 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq47425 eq768
    | (have j0 := eq768 (σ y) (σ (M.op x y)) x
       grind)
    | exact resolve eq768 eq47425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768 eq47425
  have eq47566 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq47432
    | (have j0 := eq47432 (σ y)
       grind)
    | exact resolve eq47432 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47648 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq47566 eq177
    | exact resolve eq177 eq47566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49356 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq47433 eq47432
    | exact resolve eq47432 eq47433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47432 eq47433
  have eq49399 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) := by grind
  clear eq49356
  have eq49410 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq49399 eq177
    | exact resolve eq177 eq49399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49668 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq47566 eq47648
    | exact resolve eq47648 eq47566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47566 eq47648
  have eq49726 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq49668
  have eq49744 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq49726 eq177
    | exact resolve eq177 eq49726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49746 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op (σ x) X0)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq49726 eq178
    | exact resolve eq178 eq49726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq49726
  have eq50166 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq49399 eq49410
    | exact resolve eq49410 eq49399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49399 eq49410
  have eq50227 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq50166
  have eq50255 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op X0 X1) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq50227 eq193
    | exact resolve eq193 eq50227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq50641 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq43714 eq49744
    | exact resolve eq49744 eq43714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43714 eq49744
  have eq50717 : (σ y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq28 eq50641
    | (have j1 := eq28 (σ (M.op x y)) (σ y)
       grind)
    | exact resolve eq50641 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50641
  have eq50723 : (σ y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq36726 eq50717
    | exact resolve eq50717 eq36726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36726 eq50717
  have eq50724 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq43666 eq50723
    | exact resolve eq50723 eq43666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50723
  have eq61628 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq50724 eq43691
    | exact resolve eq43691 eq50724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43691 eq50724
  have eq61715 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq61628
  have eq62547 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq16773 eq779
    | (have j0 := eq779 (σ (M.op x y))
       grind)
    | exact resolve eq779 eq16773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16773
  have eq62596 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq43666 eq779
    | (have j0 := eq779 (σ y)
       grind)
    | exact resolve eq779 eq43666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779
  have eq62670 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq46137 eq62596
    | exact resolve eq62596 eq46137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46137 eq62596
  have eq62678 : x = y ∨ (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq62547
       have i₂ := eq36105
       grind)
    | exact superpose eq36105 eq62547
    | exact resolve eq62547 eq36105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62547
  have eq62680 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq26 eq62670
    | exact resolve eq62670 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62670
  have eq62689 : x = y ∨ (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq46784 eq62678
    | exact resolve eq62678 eq46784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46784 eq62678
  have eq62692 : x = y ∨ (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq44261 eq62689
    | exact resolve eq62689 eq44261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44261 eq62689
  have eq62693 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq62692
  have eq62824 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq62693 eq177
    | exact resolve eq177 eq62693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62693
  have eq62989 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq62680 eq49746
    | exact resolve eq49746 eq62680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49746 eq62680
  have eq63073 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq36817 eq62989
    | exact resolve eq62989 eq36817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36817 eq62989
  have eq63076 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq61715 eq63073
    | exact resolve eq63073 eq61715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61715 eq63073
  have eq63078 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq63076
       have r₂ := eq36690
       grind)
    | exact resolve eq63076 eq36690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36690 eq63076
  have eq64949 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq63078 eq46817
    | exact resolve eq46817 eq63078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46817
  have eq65012 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by grind
  clear eq63078
  have eq65018 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq64949
  have eq65039 : (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq65018
       have r₂ := eq65012
       grind)
    | exact resolve eq65018 eq65012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65018
  have eq65099 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq65039 eq28
    | (have j0 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq28 eq65039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq65039
  have eq65164 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq43666 eq65099
    | exact resolve eq65099 eq43666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43666 eq65099
  have eq65175 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq65164
       have r₂ := eq65012
       grind)
    | exact resolve eq65164 eq65012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65164
  have eq65180 : (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq36874 eq65175
    | exact resolve eq65175 eq36874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36874 eq65175
  have eq65182 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq65180
       have r₂ := eq65012
       grind)
    | exact resolve eq65180 eq65012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65012 eq65180
  have eq65213 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq65182 eq62824
    | exact resolve eq62824 eq65182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62824
  have eq65270 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq65182 eq50255
    | exact resolve eq50255 eq65182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50255 eq65182
  have eq65272 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq65213
  have eq69018 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq65270 eq177
    | exact resolve eq177 eq65270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq65270
  have eq86686 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq37758 eq69018
    | exact resolve eq69018 eq37758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37758 eq69018
  have eq86772 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq86686
    | exact resolve eq86686 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86686
  have eq86784 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq86772
       have r₂ := eq27
       grind)
    | exact resolve eq86772 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86772
  have eq86785 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq65272 eq86784
    | exact resolve eq86784 eq65272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65272 eq86784
  have eq86786 : (M.op x y) = (τ (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq86785 eq29
    | exact resolve eq29 eq86785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86785
  have eq86942 : y = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32 eq86786
    | exact resolve eq86786 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq86786
  have eq86943 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq86942
  have eq86962 : (M.op x y) = (τ (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq86943 eq29
    | exact resolve eq29 eq86943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq86943
  have eq87099 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq86962
    | exact resolve eq86962 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq86962
  have eq87106 : (M.op x y) = (M.op x (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq87099
       grind)
    | exact superpose eq87099 eq18
    | exact resolve eq18 eq87099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87273 : x = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq35945
       have i₂ := eq87099
       grind)
    | exact superpose eq87099 eq35945
    | exact resolve eq35945 eq87099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35945
  have eq87733 : (M.op x y) = (M.op (M.op x y) y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq87106 eq197
    | exact resolve eq197 eq87106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197 eq87106
  have eq87826 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq87099 eq87733
    | exact resolve eq87733 eq87099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87099 eq87733
  have eq88295 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq87826 eq87273
    | exact resolve eq87273 eq87826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87273 eq87826
  have eq88389 : x = (M.op x y) ∨ x = y := by grind
  clear eq88295
  have eq88416 : (M.op x y) = (M.op (M.op x y) y) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq88389
       grind)
    | exact superpose eq88389 eq18
    | exact resolve eq18 eq88389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88417 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq22
       have i₂ := eq88389
       grind)
    | exact superpose eq88389 eq22
    | exact resolve eq22 eq88389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88803 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq20 eq88417
    | exact resolve eq88417 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88417
  have eq88823 : (k (M.op x y) x) = (τ (k (σ x) (σ x))) ∨ x = y := by
    first
    | exact superpose eq88803 eq132
    | exact resolve eq132 eq88803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq88824 : (k (M.op x y) y) = (τ (k (σ x) (σ y))) ∨ x = y := by
    first
    | exact superpose eq88803 eq133
    | exact resolve eq133 eq88803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq88803
  have eq88919 : (k x y) = (k (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq99 eq88824
    | exact resolve eq88824 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq88824
  have eq88920 : (k x x) = (k (M.op x y) x) ∨ x = y := by
    first
    | exact superpose eq98 eq88823
    | exact resolve eq88823 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq88823
  have eq88935 : y = (k (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq36679 eq88919
    | exact resolve eq88919 eq36679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36679 eq88919
  have eq88936 : y = (k (M.op x y) x) ∨ x = y := by
    first
    | exact superpose eq36235 eq88920
    | exact resolve eq88920 eq36235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36235 eq88920
  have eq88939 : y = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37611 eq88936
    | exact resolve eq88936 eq37611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37611 eq88936
  have eq88941 : x = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq88389 eq88939
    | exact resolve eq88939 eq88389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88939
  have eq89104 : (M.op x y) = (M.op x (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq88416 eq207
    | exact resolve eq207 eq88416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207 eq88416
  have eq89204 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq88389 eq89104
    | exact resolve eq89104 eq88389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88389 eq89104
  have eq89544 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq88941 eq36250
    | (have j0 := eq36250 (M.op x y)
       grind)
    | exact resolve eq36250 eq88941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36250 eq88941
  have eq89580 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq89544
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq89544
    | exact resolve eq89544 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq89544
  have eq89581 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq89580
  have eq89803 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq47350
       have i₂ := eq89581
       grind)
    | exact superpose eq89581 eq47350
    | exact resolve eq47350 eq89581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47350
  have eq89821 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq88935
       have i₂ := eq89581
       grind)
    | exact superpose eq89581 eq88935
    | exact resolve eq88935 eq89581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88935 eq89581
  have eq89822 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq89821
  have eq89876 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq89822 eq89803
    | exact resolve eq89803 eq89822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89803 eq89822
  have eq89877 : x = (M.op x y) := by grind
  clear eq89876
  have eq89982 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq89877
       grind)
    | exact superpose eq89877 eq22
    | exact resolve eq22 eq89877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq90227 : y = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq36105
       have i₂ := eq89877
       grind)
    | exact superpose eq89877 eq36105
    | exact resolve eq36105 eq89877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36105
  have eq90237 : y = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq37633
       have i₂ := eq89877
       grind)
    | exact superpose eq89877 eq37633
    | exact resolve eq37633 eq89877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37633
  have eq90281 : x = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq89204 eq90237
    | exact resolve eq90237 eq89204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89204 eq90237
  have eq90391 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq90281
       have i₂ := eq89877
       grind)
    | exact superpose eq89877 eq90281
    | exact resolve eq90281 eq89877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89877 eq90281
  have eq90408 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have j1 := eq808 (M.op x y)
       grind)
    | (have r₁ := eq90391
       have r₂ := eq808 (M.op x y)
       grind)
    | exact resolve eq90391 eq808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq808 eq90391
  have eq90414 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq89982 eq20
    | exact resolve eq20 eq89982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq90970 : y = (M.op x y) := by
    first
    | exact superpose eq90408 eq90227
    | exact resolve eq90227 eq90408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90227 eq90408
  have eq91074 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq90970
       grind)
    | exact superpose eq90970 eq24
    | exact resolve eq24 eq90970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq90970
  have eq91388 : (σ x) = (σ y) := by
    first
    | exact superpose eq89982 eq91074
    | exact resolve eq91074 eq89982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89982 eq91074
  have eq91470 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq91388 eq26
    | exact resolve eq26 eq91388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq91643 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq91388 eq50227
    | exact resolve eq50227 eq91388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50227 eq91388
  have eq91760 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq90414 eq91643
    | exact resolve eq91643 eq90414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91643
  have eq91857 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq91470 eq91760
    | exact resolve eq91760 eq91470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91760
  have eq91905 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq91470 eq91857
    | exact resolve eq91857 eq91470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91470 eq91857
  have eq91929 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq91905
       have r₂ := eq27
       grind)
    | exact resolve eq91905 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91905
  have eq91942 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq91929 eq27
    | exact resolve eq27 eq91929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq91929
  have eq92070 : False := by grind
  exact eq92070

/-- `Equation2165`: `x = ((y ◇ z) ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyy_pxx_pxy_pyx_Equation2165 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2165 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2165.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X1 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X2) X0) X3)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X2) X0) (M.op X1 X0)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X1 X2) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X0) (M.op X1 X2) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op (M.op (M.op (M.op X1 X2) X0) X3) (M.op X1 X0)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X1 X0) (M.op (M.op X1 X2) X0) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = X1 ∨ (M.op X0 X0) = (M.op X2 X2) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X0 X0
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X2 X0
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (M.op X2 X2) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X2 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X1 X1)
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X2 X2) ∨ (M.op X1 X1) = X1 ∨ (k X2 X1) = (M.op X2 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X2 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 (M.op X1 X1) X1
       have r₂ := eq14 X0 (M.op X1 X1)
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X2 X2) ∨ (M.op X1 X1) = X1 ∨ (k X2 X1) = (M.op X2 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq76 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq92 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (M.op X2 X2) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq71 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq137 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X0 X1 x (M.op X1 X0)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq23
    | exact resolve eq23 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq178 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X2) (M.op X0 X1)) (M.op (M.op X1 X3) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq24 (M.op (M.op X1 X2) (M.op X1 X0)) X0 X2
       have i₂ := eq24 X0 X1 X2
       grind)
    | exact superpose eq24 eq24
    | exact resolve eq24 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq376 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 (M.op X0 X1)
       have i₂ := eq137 X1 X0
       grind)
    | exact superpose eq137 eq9
    | exact resolve eq9 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq524 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq92 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq525 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq92 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq575 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq376 X1 (M.op X0 X0)
       have i₂ := eq376 X0 X0
       grind)
    | exact superpose eq376 eq376
    | exact resolve eq376 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq587 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X1 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) X1 X0
       have i₂ := eq376 X1 X0
       grind)
    | exact superpose eq376 eq9
    | exact resolve eq9 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq942 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X2 X2) ∨ (M.op X1 X2) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq376 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq68 X0 X1 X2
       grind)
    | exact superpose eq68 eq376
    | (have j1 := eq68 X1 X1 X2
       grind)
    | exact resolve eq376 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq1479 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq575 X0 X1
       grind)
    | exact superpose eq575 eq9
    | exact resolve eq9 eq575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575
  have eq1672 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op (M.op (M.op X0 X0) X2) X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 (M.op X1 X0) (M.op X0 X0) X2
       have i₂ := eq1479 X0 X1
       grind)
    | exact superpose eq1479 eq24
    | exact resolve eq24 eq1479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1939 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (M.op (M.op X0 X1) (M.op X0 X1)) X0 X1
       have i₂ := eq587 (M.op X0 X1) X0
       grind)
    | exact superpose eq587 eq24
    | exact resolve eq24 eq587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq587
  have eq1951 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1939 X0 X1
       have i₂ := eq376 (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq376 eq1939
    | exact resolve eq1939 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1939
  have eq2109 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq91 X1 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq7525 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X0 (M.op (M.op X0 X0) X1) x X0
       have i₂ := eq1672 X0 (M.op (M.op (M.op (M.op X0 X0) X1) x) X0) X1
       grind)
    | exact superpose eq1672 eq25
    | exact resolve eq25 eq1672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1672
  have eq8387 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7525 (M.op X1 X1) X1
       have i₂ := eq1479 X1 X1
       grind)
    | exact superpose eq1479 eq7525
    | exact resolve eq7525 eq1479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1479 eq7525
  have eq20118 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 (M.op (M.op X0 X2) (M.op X0 X0))) ∨ (M.op X1 X1) = (M.op (M.op (M.op X0 X2) (M.op X0 X0)) (M.op (M.op X0 X2) (M.op X0 X0))) ∨ (M.op X1 (M.op (M.op X0 X2) (M.op X0 X0))) = (k (M.op (M.op X0 X2) (M.op X0 X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq524 (M.op (M.op X0 X2) (M.op X0 X0)) X1
       have i₂ := eq178 X0 X0 X2 X2
       grind)
    | exact superpose eq178 eq524
    | (have j0 := eq524 (M.op (M.op X0 X2) (M.op X0 X0)) X1
       grind)
    | exact resolve eq524 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524
  have eq20130 : ∀ X0 X1 X2 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (M.op (M.op (M.op X0 X2) (M.op X0 X0)) (M.op (M.op X0 X2) (M.op X0 X0))) ∨ (M.op X1 (M.op (M.op X0 X2) (M.op X0 X0))) = (k (M.op (M.op X0 X2) (M.op X0 X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20118 X0 X1 X2
       have i₂ := eq8387 X0 X2
       grind)
    | exact superpose eq8387 eq20118
    | (have j0 := eq20118 X0 X1 X2
       grind)
    | (have r₁ := eq20118 X0 (M.op (M.op X0 X0) X1) X0
       have r₂ := eq8387 (M.op X0 X0) X1
       grind)
    | exact resolve eq20118 eq8387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20118
  have eq20177 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op (M.op X0 X2) (M.op X0 X0)) (M.op (M.op X0 X2) (M.op X0 X0))) ∨ (M.op X1 (M.op (M.op X0 X2) (M.op X0 X0))) = (k (M.op (M.op X0 X2) (M.op X0 X0)) X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq20130 X0 X1 X2
       have j1 := eq942 X0 X1 (M.op (M.op X0 X2) (M.op X0 X0))
       grind)
    | (have r₁ := eq20130 X0 X1 X2
       have r₂ := eq942 X0 X1 X2
       grind)
    | (have r₁ := eq20130 X1 X1 X2
       have r₂ := eq942 X1 X1 X2
       grind)
    | (have r₁ := eq20130 X2 X2 X2
       have r₂ := eq942 X0 X2 X2
       grind)
    | exact resolve eq20130 eq942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq942 eq20130
  have eq20210 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 (M.op (M.op X0 X2) (M.op X0 X0))) = (k (M.op (M.op X0 X2) (M.op X0 X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20177 X0 X1 X2
       have i₂ := eq178 X0 X0 X2 X2
       grind)
    | exact superpose eq178 eq20177
    | (have j0 := eq20177 X0 X1 X2
       grind)
    | exact resolve eq20177 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq20177
  have eq20227 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq20210 X0 X1 X1
       have i₂ := eq8387 X0 X1
       grind)
    | exact superpose eq8387 eq20210
    | (have j0 := eq20210 X0 X1 x
       grind)
    | exact resolve eq20210 eq8387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8387 eq20210
  have eq20508 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1951 X1 X1
       have i₂ := eq20227 X0 X1
       grind)
    | (have i₁ := eq1951 X0 X0
       have i₂ := eq20227 X0 X1
       grind)
    | exact superpose eq20227 eq1951
    | (have j1 := eq20227 X0 X1
       grind)
    | exact resolve eq1951 eq20227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20740 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1951 X1 X1
       have i₂ := eq20227 X0 X1
       grind)
    | (have i₁ := eq1951 X0 X0
       have i₂ := eq20227 X0 X1
       grind)
    | exact superpose eq20227 eq1951
    | (have j1 := eq20227 X1 X0
       grind)
    | exact resolve eq1951 eq20227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1951 eq20227
  have eq20837 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq20740 X0 X1
       have i₂ := eq376 X0 X0
       grind)
    | exact superpose eq376 eq20740
    | (have j0 := eq20740 X0 X1
       grind)
    | exact resolve eq20740 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20740
  have eq20851 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20508 X0 X1
       have i₂ := eq376 X0 X0
       grind)
    | exact superpose eq376 eq20508
    | (have j0 := eq20508 X0 X1
       grind)
    | exact resolve eq20508 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376 eq20508
  have eq20956 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq525 X0 X1
       have i₂ := eq2109 X1 X0
       grind)
    | exact superpose eq2109 eq525
    | (have j0 := eq525 X0 X1
       have j1 := eq2109 X1 X0
       grind)
    | (have r₁ := eq525 X0 X0
       have r₂ := eq2109 X0 X0
       grind)
    | (have r₁ := eq525 X1 X1
       have r₂ := eq2109 X1 X1
       grind)
    | exact resolve eq525 eq2109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525 eq2109
  have eq20968 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq20956 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20956
  have eq20980 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq20968 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq20968 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq20968 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20968
  have eq21001 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq20980 X0 X1
       have j1 := eq20837 X1 X0
       grind)
    | (have r₁ := eq20980 X0 X0
       have r₂ := eq20837 X0 X0
       grind)
    | (have r₁ := eq20980 X1 X0
       have r₂ := eq20837 X0 X1
       grind)
    | exact resolve eq20980 eq20837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20837 eq20980
  have eq21632 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq21001 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21001
  have eq21639 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq21632 X0 X1
       have j1 := eq20851 X0 X1
       grind)
    | (have r₁ := eq21632 X0 X1
       have r₂ := eq20851 X0 X1
       grind)
    | (have r₁ := eq21632 X1 X1
       have r₂ := eq20851 X1 X1
       grind)
    | exact resolve eq21632 eq20851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20851 eq21632
  have eq22096 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq21639 (σ X1) (σ X0)
       grind)
    | exact superpose eq21639 eq15
    | exact resolve eq15 eq21639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22119 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22096 X0 X1
       have i₂ := eq21639 X1 X0
       grind)
    | exact superpose eq21639 eq22096
    | exact resolve eq22096 eq21639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21639 eq22096
  have eq25674 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq22119 x y
       grind)
    | exact superpose eq22119 eq16
    | (have r₁ := eq16
       have r₂ := eq22119 x y
       grind)
    | exact resolve eq16 eq22119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22119
  have eq25856 : False := by grind
  exact eq25856

/-- `Equation2165`: `x = ((y ◇ z) ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxy_pxx_pyx_Equation2165 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2165 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2165.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : ∀ X0 : G, (k (τ (σ X0)) X0) = (M.op (τ (σ X0)) X0) := by
    intro X0
    first
    | (have j0 := eq12 (τ (σ X0)) X0
       grind)
    | (have r₁ := eq12 (τ (σ X0)) X0
       have r₂ := eq10 X0
       grind)
    | (have r₁ := eq12 X0 (τ (σ X0))
       have r₂ := eq10 X0
       grind)
    | exact resolve eq12 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq17 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq17
    | exact resolve eq17 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq28 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq36 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq21 (σ X0)
       grind)
    | exact superpose eq21 eq15
    | exact resolve eq15 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq36
    | exact resolve eq36 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq36
  have eq92 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 (M.op X1 X0) (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq92 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq106 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq105 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq371 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq106 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq374 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq371 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq371 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq371 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq371 X0 X1
       have r₂ := eq14 (M.op X1 X0) (M.op X0 X0)
       grind)
    | exact resolve eq371 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371
  have eq398 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq374 X1 (τ X0)
       grind)
    | exact superpose eq374 eq28
    | (have j1 := eq374 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq28 eq374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq399 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq374 (σ X1) (σ X0)
       grind)
    | exact superpose eq374 eq15
    | (have j1 := eq374 (M.op (σ X0) (σ X1)) (σ (k X1 X0))
       grind)
    | exact resolve eq15 eq374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374
  have eq12033 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq398 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq398
    | exact resolve eq398 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq398
  have eq12101 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12033 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq12033
    | (have j0 := eq12033 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq12033 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12033
  have eq21433 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq399 x y
       grind)
    | exact superpose eq399 eq16
    | (have j1 := eq399 x y
       grind)
    | exact resolve eq16 eq399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399
  have eq21675 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq21433
       have i₂ := eq12101 x y
       grind)
    | exact superpose eq12101 eq21433
    | (have j1 := eq12101 (σ x) (σ y)
       grind)
    | (have r₁ := eq21433
       have r₂ := eq12101 x y
       grind)
    | (have r₁ := eq21433
       have r₂ := eq12101 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq21433
       have r₂ := eq12101 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq21433 eq12101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12101 eq21433
  have eq21676 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq21675
  have eq22385 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq21676
       grind)
    | exact superpose eq21676 eq10
    | exact resolve eq10 eq21676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21676
  have eq22449 : x = y ∨ x = y := by
    first
    | (have i₁ := eq22385
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq22385
    | exact resolve eq22385 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22385
  have eq22450 : x = y := by grind
  clear eq22449
  have eq23062 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq22450
       grind)
    | exact superpose eq22450 eq16
    | exact resolve eq16 eq22450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22450
  have eq23063 : False := by grind
  exact eq23063

/-- `Equation2291`: `x = (y ◇ (x ◇ (x ◇ x))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pyx_pyy_pyx_Equation2291 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2291 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2291.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 (M.op X0 X0))) X1) = X0 := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
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
  have eq19 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 (M.op X1 X1)) (M.op X0 (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op (M.op X1 (M.op X1 X1)) (M.op X0 (M.op X0 X0)))
       have i₂ := eq9 X0 (M.op X1 (M.op X1 X1))
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (k (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k X0 (τ X1))
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq15
    | exact resolve eq15 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq52 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq52 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq52 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq55 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq53 (σ X0)
       grind)
    | exact superpose eq53 eq15
    | exact resolve eq15 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq55 X0
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq55
    | exact resolve eq55 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq55
  have eq74 : ∀ X0 X1 : G, (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq64 (k X1 (τ X0))
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq64
    | exact resolve eq64 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq88 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq82 X0 X1
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq82
    | (have j0 := eq82 X0 X1
       grind)
    | exact resolve eq82 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq91 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq88 X0 X1
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq88
    | (have j0 := eq88 X0 X1
       grind)
    | exact resolve eq88 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq88
  have eq163 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq91 (k X1 (τ X0)) X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq91
    | exact resolve eq91 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq185 : ∀ X0 X1 X2 : G, (M.op (k (σ X0) X1) (k (σ X0) X1)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (k X2 (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq163 X0 X1 X2
       have i₂ := eq74 X0 X1
       grind)
    | exact superpose eq74 eq163
    | (have j0 := eq163 X0 X1 X2
       grind)
    | exact resolve eq163 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq191 : ∀ X0 X1 X2 : G, (M.op (k (σ X0) X1) (k (σ X0) X1)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (σ (k X2 (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq185 X0 X1 X2
       have i₂ := eq74 X0 X1
       grind)
    | exact superpose eq74 eq185
    | (have j0 := eq185 X0 X1 X2
       grind)
    | exact resolve eq185 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq185
  have eq1341 : ∀ X0 X1 X2 X3 : G, (M.op (k (σ X0) X1) (σ X2)) ≠ (M.op (k (σ X0) X1) X3) ∨ (M.op (k (σ X0) X1) (σ X2)) = (k X3 (k (σ X0) X1)) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (σ (k X2 (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X0 (k (σ X0) X1)
       have i₂ := eq191 X0 X1 X2
       grind)
    | exact superpose eq191 eq13
    | (have j0 := eq13 X0 (k (σ X0) X1)
       have j1 := eq191 X0 X1 X2
       grind)
    | (have r₁ := eq13 (σ X2) (k (σ X0) X1)
       have r₂ := eq191 X0 X1 X2
       grind)
    | exact resolve eq13 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1362 : ∀ X0 X1 X2 : G, (k (σ X0) X1) ≠ (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (σ (k X2 (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq191 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq1374 : ∀ X0 X1 X2 X3 : G, (M.op (k (σ X0) X1) (σ X2)) ≠ (M.op (k (σ X0) X1) X3) ∨ (M.op (k (σ X0) X1) (σ X2)) = (k X3 (k (σ X0) X1)) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (σ (k X2 (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq1341 X0 X1 X2 X3
       have j1 := eq1362 X0 X1 X2
       grind)
    | (have r₁ := eq1341 X0 X1 X2 X3
       have r₂ := eq1362 X0 X1 X2
       grind)
    | exact resolve eq1341 eq1362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1341 eq1362
  have eq93488 : ∀ X0 X1 X2 : G, (k (σ X2) (k (σ X0) X1)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (σ (k X2 (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1374 X0 X1 X2 (σ X2)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1374
  have eq93492 : ∀ X0 X1 X2 : G, (k (σ X2) (k (σ X0) X1)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (k X2 (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq93488 X0 X1 X2
       have j1 := eq12 (σ X2) (k (σ X0) X1)
       grind)
    | (have r₁ := eq93488 X0 X1 X2
       have r₂ := eq12 X0 (k (σ X0) X1)
       grind)
    | exact resolve eq93488 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93488
  have eq93561 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (k X2 (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq93492 X0 X1 X2
       have i₂ := eq27 X0 X1 X2
       grind)
    | exact superpose eq27 eq93492
    | (have j0 := eq93492 X0 X1 X2
       grind)
    | exact resolve eq93492 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq93492
  have eq93562 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq93561 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93561
  have eq93931 : ∀ X0 X1 X2 : G, (k X2 (σ (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ (τ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X2 (k X0 (τ X1))
       have i₂ := eq93562 X0 X1 (τ X2)
       grind)
    | exact superpose eq93562 eq17
    | exact resolve eq17 eq93562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq93562
  have eq94133 : ∀ X0 X1 X2 : G, (k X2 (σ (k X0 (τ X1)))) = (M.op (k (σ X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq93931 X0 X1 X2
       have i₂ := eq11 X2
       grind)
    | exact superpose eq11 eq93931
    | exact resolve eq93931 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93931
  have eq94326 : ∀ X0 X1 X2 : G, (k X2 (k (σ X0) X1)) = (M.op (k (σ X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq94133 X0 X1 X2
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq94133
    | exact resolve eq94133 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq94133
  have eq94517 : ∀ X0 X1 X2 : G, (k X1 (k X0 X2)) = (M.op (k X0 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq94326 (τ X0) X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq94326
    | exact resolve eq94326 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94326
  have eq95461 : ∀ X0 X1 X2 X3 : G, (k X3 (M.op (k X0 X1) X2)) = (M.op (M.op (k X0 X1) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq94517 X1 X1 (k X0 X2)
       have i₂ := eq94517 X0 X1 X2
       grind)
    | exact superpose eq94517 eq94517
    | exact resolve eq94517 eq94517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94517
  have eq123851 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq95461 X0 X1 (M.op (M.op X1 (M.op X1 X1)) (M.op (k X0 X1) (M.op (k X0 X1) (k X0 X1)))) x
       have i₂ := eq19 (k X0 X1) X1
       grind)
    | exact superpose eq19 eq95461
    | exact resolve eq95461 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq95461
  have eq125151 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq123851 (σ X0) (σ X1)
       grind)
    | exact superpose eq123851 eq15
    | exact resolve eq15 eq123851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125450 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq125151 X0 X1
       have i₂ := eq123851 X0 X1
       grind)
    | exact superpose eq123851 eq125151
    | exact resolve eq125151 eq123851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123851 eq125151
  have eq138788 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq125450 x y
       grind)
    | exact superpose eq125450 eq16
    | (have r₁ := eq16
       have r₂ := eq125450 x y
       grind)
    | exact resolve eq16 eq125450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125450
  have eq139032 : False := by grind
  exact eq139032

/-- `Equation2300`: `x = (y ◇ (x ◇ (y ◇ x))) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pyx_pyy_pxx_pyy_pyx_Equation2300 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2300 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2300.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq144 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq154 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq156 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq144 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq2184 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq156 X0 X1
       have j1 := eq154 X1 X0
       grind)
    | (have r₁ := eq156 X0 X1
       have r₂ := eq154 X0 X1
       grind)
    | (have r₁ := eq156 X1 X0
       have r₂ := eq154 X0 X1
       grind)
    | (have r₁ := eq156 X1 X1
       have r₂ := eq154 X1 X1
       grind)
    | exact resolve eq156 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154 eq156
  have eq2550 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq2184 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2184
  have eq2574 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq2550 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq2550 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq2550 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq2550 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq2550 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2550
  have eq2628 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq2574 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq2574 X0 X1
       grind)
    | exact superpose eq2574 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq2574 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq2574 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq2574 X1 X1
       grind)
    | exact resolve eq12 eq2574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2718 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq2628 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2628
  have eq2838 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq2718 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2718
  have eq2845 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq2838 X0 X1
       have j1 := eq2574 X0 X1
       grind)
    | (have r₁ := eq2838 X0 X1
       have r₂ := eq2574 X0 X1
       grind)
    | (have r₁ := eq2838 X1 X1
       have r₂ := eq2574 X1 X1
       grind)
    | exact resolve eq2838 eq2574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2574 eq2838
  have eq2866 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq2845 (σ X0) (σ X1)
       grind)
    | exact superpose eq2845 eq15
    | exact resolve eq15 eq2845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2881 : ∀ X0 X1 : G, (σ (M.op X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2866 X0 X1
       have i₂ := eq2845 X0 X1
       grind)
    | exact superpose eq2845 eq2866
    | exact resolve eq2866 eq2845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2845 eq2866
  have eq3101 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2881 y x
       grind)
    | exact superpose eq2881 eq16
    | (have r₁ := eq16
       have r₂ := eq2881 y x
       grind)
    | exact resolve eq16 eq2881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2881
  have eq3109 : False := by grind
  exact eq3109
