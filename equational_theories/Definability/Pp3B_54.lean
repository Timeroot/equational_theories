import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3461`: `x ◇ x = x ◇ ((y ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_pxy_x_pxy_Equation3461 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3461 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3461.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq267 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
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
  have eq273 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq267 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq274 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq273 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273
  have eq379 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq274 X1 X0
       grind)
    | exact superpose eq274 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq274 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq274 X0 X1
       grind)
    | exact resolve eq13 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq384 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq274 (σ y) (σ x)
       grind)
    | exact superpose eq274 eq16
    | (have j1 := eq274 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq388 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq379 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379
  have eq389 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq384
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq384
    | exact resolve eq384 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384
  have eq391 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq388 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq388 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq388 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388
  have eq405 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq391 X0 (τ X1)
       grind)
    | exact superpose eq391 eq18
    | (have j1 := eq391 X0 (τ X1)
       grind)
    | exact resolve eq18 eq391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq422 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq391 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq680 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (τ X1))) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (τ X1)
       have i₂ := eq405 (τ X0) X1
       grind)
    | exact superpose eq405 eq17
    | (have j1 := eq405 (τ X0) X1
       grind)
    | exact resolve eq17 eq405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq405
  have eq685 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq680 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq680
    | (have j0 := eq680 X0 X1
       grind)
    | exact resolve eq680 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680
  have eq701 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq685 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq685
    | (have j0 := eq685 X0 X1
       grind)
    | exact resolve eq685 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685
  have eq704 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq701 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq701
    | (have j0 := eq701 X0 X1
       grind)
    | exact resolve eq701 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701
  have eq760 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq704 X0 X1
       have i₂ := eq391 X0 X1
       grind)
    | exact superpose eq391 eq704
    | (have j0 := eq704 X0 X1
       have j1 := eq391 X0 X1
       grind)
    | exact resolve eq704 eq391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391 eq704
  have eq819 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq760 X0 X1
       have j1 := eq422 X0 X1
       grind)
    | (have r₁ := eq760 X0 X1
       have r₂ := eq422 X0 X1
       grind)
    | exact resolve eq760 eq422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422 eq760
  have eq869 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ X1)) ∨ (M.op (σ X0) X1) = (σ (M.op (τ (σ X0)) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq819 (σ X0) X1
       grind)
    | exact superpose eq819 eq28
    | (have j1 := eq819 (σ X0) X1
       grind)
    | exact resolve eq28 eq819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq819
  have eq885 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (M.op (σ X0) X1) = (σ (M.op (τ (σ X0)) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq869 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq869
    | (have j0 := eq869 X0 X1
       grind)
    | exact resolve eq869 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869
  have eq911 : ∀ X0 X1 : G, (σ (M.op X0 (τ X1))) = (M.op (σ X0) X1) ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq885 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq885
    | (have j0 := eq885 X0 X1
       grind)
    | exact resolve eq885 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq885
  have eq1154 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq911 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq911
    | exact resolve eq911 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq911
  have eq1216 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1154 y x
       grind)
    | exact superpose eq1154 eq16
    | (have j1 := eq1154 y x
       grind)
    | (have r₁ := eq16
       have r₂ := eq1154 y x
       grind)
    | exact resolve eq16 eq1154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1154
  have eq1232 : x = (k x y) := by grind
  clear eq1216
  have eq1960 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq389
       have i₂ := eq274 y x
       grind)
    | exact superpose eq274 eq389
    | (have j1 := eq274 y x
       grind)
    | exact resolve eq389 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1963 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (k x y) := by grind
  clear eq1960
  have eq1964 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq1963
       have i₂ := eq1232
       grind)
    | exact superpose eq1232 eq1963
    | exact resolve eq1963 eq1232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1963
  have eq1965 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1964
       have i₂ := eq1232
       grind)
    | exact superpose eq1232 eq1964
    | exact resolve eq1964 eq1232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1964
  have eq1966 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq389
       have i₂ := eq1965
       grind)
    | exact superpose eq1965 eq389
    | exact resolve eq389 eq1965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389 eq1965
  have eq1979 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1966
  have eq1980 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1979
       have i₂ := eq1232
       grind)
    | exact superpose eq1232 eq1979
    | exact resolve eq1979 eq1232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1979
  have eq1981 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1980
  have eq1984 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1981
       grind)
    | exact superpose eq1981 eq16
    | exact resolve eq16 eq1981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1981
  have eq2022 : (σ x) ≠ (σ x) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq1984
       have i₂ := eq274 y x
       grind)
    | exact superpose eq274 eq1984
    | (have j1 := eq274 y x
       grind)
    | exact resolve eq1984 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq2025 : (M.op x y) = (k x y) := by grind
  clear eq2022
  have eq2027 : x = (M.op x y) := by
    first
    | (have i₁ := eq2025
       have i₂ := eq1232
       grind)
    | exact superpose eq1232 eq2025
    | exact resolve eq2025 eq1232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1232 eq2025
  have eq2028 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1984
       have i₂ := eq2027
       grind)
    | exact superpose eq2027 eq1984
    | exact resolve eq1984 eq2027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1984 eq2027
  have eq2043 : False := by grind
  exact eq2043

/-- `Equation3461`: `x ◇ x = x ◇ ((y ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(Y,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxy_pxx_pxy_Equation3461 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3461 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3461.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X1 X0) X0)) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
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
  have eq25 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
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
  have eq114 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq116 : ∀ X0 X1 : G, (M.op X1 (τ X0)) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq584 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq116 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq116
    | exact resolve eq116 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq605 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq584 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq584
    | (have j0 := eq584 X0 X1
       grind)
    | exact resolve eq584 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584
  have eq612 : ∀ X0 X1 : G, X0 ≠ X0 ∨ X0 = X1 ∨ (M.op X1 X1) = (k X1 X0) ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq605 X1 X0
       grind)
    | exact superpose eq605 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq605 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq605 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq605 (M.op X1 X0) X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq605 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq613 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (M.op X0 X1)) ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0
       have i₂ := eq605 X1 X0
       grind)
    | exact superpose eq605 eq9
    | (have j1 := eq605 X1 X0
       grind)
    | exact resolve eq9 eq605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq625 : ∀ X0 X1 : G, X0 ≠ X0 ∨ X0 = X1 ∨ (M.op X1 X1) = (k X1 X0) ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq612 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612
  have eq626 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq625 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625
  have eq764 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq114 x y
       grind)
    | exact superpose eq114 eq16
    | (have j1 := eq114 x y
       grind)
    | exact resolve eq16 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq3614 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq613 X0 X1
       have i₂ := eq605 X1 X0
       grind)
    | exact superpose eq605 eq613
    | (have j0 := eq613 X0 X1
       have j1 := eq605 X1 X0
       grind)
    | exact resolve eq613 eq605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605 eq613
  have eq3645 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq3614 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3614
  have eq3707 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq3645 X1 X0
       grind)
    | exact superpose eq3645 eq10
    | (have j1 := eq3645 X1 X0
       grind)
    | exact resolve eq10 eq3645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3752 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3707 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq3707
    | (have j0 := eq3707 X0 X1
       grind)
    | exact resolve eq3707 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3707
  have eq3806 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (M.op X0 X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0
       have i₂ := eq3752 (τ X0) X1
       grind)
    | (have i₁ := eq30 X0
       have i₂ := eq3752 (τ X0) (τ X0)
       grind)
    | exact superpose eq3752 eq30
    | (have j1 := eq3752 (τ X0) X1
       grind)
    | exact resolve eq30 eq3752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq3752
  have eq4844 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq764
       have i₂ := eq3645 y x
       grind)
    | exact superpose eq3645 eq764
    | (have j1 := eq3645 y x
       grind)
    | (have r₁ := eq764
       have r₂ := eq3645 y x
       grind)
    | (have r₁ := eq764
       have r₂ := eq3645 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq764
       have r₂ := eq3645 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq764 eq3645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3645
  have eq4845 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (k x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq764
       have i₂ := eq626 y x
       grind)
    | exact superpose eq626 eq764
    | (have j1 := eq626 y x
       grind)
    | (have r₁ := eq764
       have r₂ := eq626 y x
       grind)
    | (have r₁ := eq764
       have r₂ := eq626 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq764
       have r₂ := eq626 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq764 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626
  have eq4846 : x = y ∨ (σ x) = (σ y) ∨ (k x y) = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq4845
  have eq4847 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq4844
  have eq5772 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3806 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3806
    | exact resolve eq3806 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3806
  have eq5863 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5772 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq5772
    | (have j0 := eq5772 X0 X1
       grind)
    | exact resolve eq5772 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5772
  have eq7523 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (k x y) = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4846
       grind)
    | exact superpose eq4846 eq16
    | exact resolve eq16 eq4846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4846
  have eq7524 : (k x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq7523
       have r₂ := eq22 x
       grind)
    | exact resolve eq7523 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7523
  have eq7528 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq764
       have i₂ := eq7524
       grind)
    | exact superpose eq7524 eq764
    | exact resolve eq764 eq7524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764 eq7524
  have eq7536 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq7528
  have eq9594 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4847
       grind)
    | exact superpose eq4847 eq16
    | exact resolve eq16 eq4847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4847
  have eq9595 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq9594
       have r₂ := eq22 x
       grind)
    | exact resolve eq9594 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9594
  have eq9603 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq7536
       have i₂ := eq9595
       grind)
    | exact superpose eq9595 eq7536
    | exact resolve eq7536 eq9595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7536 eq9595
  have eq9621 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq9603
  have eq9622 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq9621
  have eq9629 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9 (σ x) (σ y)
       have i₂ := eq9622
       grind)
    | exact superpose eq9622 eq9
    | exact resolve eq9 eq9622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9630 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq9622
       grind)
    | exact superpose eq9622 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq9622
       grind)
    | exact resolve eq13 eq9622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9637 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
  clear eq9630
  have eq9638 : (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
  clear eq9637
  have eq9648 : (σ (k x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9638
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq9638
    | exact resolve eq9638 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9638
  have eq9649 : (σ x) = (σ y) ∨ (σ (M.op x x)) = (M.op (σ x) (M.op (σ y) (σ x))) := by
    first
    | (have i₁ := eq9629
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq9629
    | exact resolve eq9629 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9629
  have eq9655 : (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq9648
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq9648
    | exact resolve eq9648 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9648
  have eq9662 : y = (τ (σ x)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq9655
       grind)
    | exact superpose eq9655 eq10
    | exact resolve eq10 eq9655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9655
  have eq9717 : x = y ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq9662
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq9662
    | exact resolve eq9662 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9662
  have eq9719 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9717
       grind)
    | exact superpose eq9717 eq16
    | exact resolve eq16 eq9717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9717
  have eq9720 : (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq9719
       have r₂ := eq22 x
       grind)
    | exact resolve eq9719 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9719
  have eq9725 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ x = y := by
    first
    | (have i₁ := eq9720
       have i₂ := eq5863 x y
       grind)
    | exact superpose eq5863 eq9720
    | (have j1 := eq5863 x y
       grind)
    | exact resolve eq9720 eq5863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5863 eq9720
  have eq9769 : x = y ∨ (σ (M.op x y)) = (σ (M.op x x)) := by grind
  clear eq9725
  have eq9813 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9769
       grind)
    | exact superpose eq9769 eq16
    | exact resolve eq16 eq9769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9769
  have eq9816 : (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq9813
       have r₂ := eq22 x
       grind)
    | exact resolve eq9813 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9813
  have eq11837 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (σ (M.op x x)) = (M.op (σ x) (M.op (σ y) (σ x))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9649
       grind)
    | exact superpose eq9649 eq16
    | exact resolve eq16 eq9649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9649
  have eq11896 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (M.op (σ x) (M.op (σ y) (σ x))) := by
    first
    | (have i₁ := eq11837
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq11837
    | exact resolve eq11837 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11837
  have eq11897 : (σ (M.op x x)) = (M.op (σ x) (M.op (σ y) (σ x))) := by
    first
    | (have r₁ := eq11896
       have r₂ := eq9816
       grind)
    | exact resolve eq11896 eq9816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11896
  have eq11906 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq11897
       have i₂ := eq9622
       grind)
    | exact superpose eq9622 eq11897
    | exact resolve eq11897 eq9622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9622 eq11897
  have eq11982 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11906
       grind)
    | exact superpose eq11906 eq16
    | exact resolve eq16 eq11906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11906
  have eq12058 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq11982
       have r₂ := eq9816
       grind)
    | exact resolve eq11982 eq9816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11982
  have eq12079 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12058
       grind)
    | exact superpose eq12058 eq16
    | exact resolve eq16 eq12058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12058
  have eq12140 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq12079
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq12079
    | exact resolve eq12079 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq12079
  have eq12141 : False := by grind
  exact eq12141

/-- `Equation3506`: `x ◇ x = y ◇ ((z ◇ w) ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then Y else if m(X,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_y_pyy_pxy_Equation3506 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3506 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3506.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X3) X3)) := by
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
  clear eq23
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
  have eq62 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op x y) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 X1 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 X3) = (M.op X4 (M.op (M.op X0 (M.op (M.op X1 X2) X2)) X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq14 X3 X4 X5 X5
       have i₂ := eq14 X5 X0 X1 X2
       grind)
    | (have i₁ := eq14 X0 X1 X1 (M.op (M.op X2 X3) X3)
       have i₂ := eq14 X0 X1 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 X2 x (M.op (M.op x x) x)
       have i₂ := eq14 X0 (M.op x (M.op (M.op x x) x)) x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 x x x
       have i₂ := eq14 X1 x x x
       grind)
    | (have i₁ := eq14 X0 (M.op (M.op x x) x) x x
       have i₂ := eq14 (M.op (M.op x x) x) X1 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq94 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
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
  have eq102 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq94
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq94
    | exact resolve eq94 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq103 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq21 eq102
    | exact resolve eq102 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq109 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq225 : ∀ X0 X2 : G, (M.op X0 (M.op (M.op x y) y)) = (M.op X2 (M.op (M.op x y) y)) := by
    intro X0 X2
    first
    | (have i₁ := eq62 x X2
       have i₂ := eq62 x X0
       grind)
    | (have i₁ := eq62 (M.op (M.op x y) y) x
       have i₂ := eq62 X0 (M.op (M.op x y) y)
       grind)
    | exact superpose eq62 eq62
    | exact resolve eq62 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq314 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X2 (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op X1 X1)
       have i₂ := eq66 X1 X0 (M.op X1 X1)
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq66 X0 X1 X2
       grind)
    | exact superpose eq66 eq13
    | (have j0 := eq13 X2 (M.op X1 X1)
       grind)
    | (have r₁ := eq13 X0 (M.op X2 (M.op X0 X0))
       have r₂ := eq66 X0 (M.op X2 (M.op X0 X0)) X2
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X1)
       have r₂ := eq66 X1 X1 (M.op X1 X1)
       grind)
    | exact resolve eq13 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq322 : ∀ X1 X2 : G, (M.op X1 X1) = (k X2 (M.op X1 X1)) := by
    intro X1 X2
    first
    | (have j0 := eq314 x X1 X2
       grind)
    | (have r₁ := eq314 x X1 X2
       have r₂ := eq67 x X1
       grind)
    | (have r₁ := eq314 X1 x X2
       have r₂ := eq67 x X1
       grind)
    | exact resolve eq314 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314
  have eq1108 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq89 X0 X0
       have i₂ := eq67 (σ X0) X1
       grind)
    | (have i₁ := eq89 X0 X0
       have i₂ := eq67 X0 (σ X0)
       grind)
    | exact superpose eq67 eq89
    | exact resolve eq89 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1119 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq67 X1 (σ X0)
       have i₂ := eq89 X0 X0
       grind)
    | exact superpose eq89 eq67
    | (have j1 := eq89 X0 X0
       grind)
    | exact resolve eq67 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1129 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq89 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq1130 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1129 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1129
  have eq1134 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X1 X1) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1119 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1119
  have eq1145 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq1108 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1108
  have eq1350 : ∀ X0 X1 X2 X3 X5 : G, (M.op X1 X1) = (M.op X2 (M.op (M.op X3 (M.op X0 (M.op (M.op x y) y))) X5)) := by
    intro X0 X1 X2 X3 X5
    first
    | exact superpose eq225 eq64
    | exact resolve eq64 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq225
  have eq7813 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1145 X1 (M.op X0 X0)
       have i₂ := eq322 X0 (M.op X0 X0)
       grind)
    | exact superpose eq322 eq1145
    | (have j0 := eq1145 X1 (M.op X0 X0)
       grind)
    | exact resolve eq1145 eq322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322 eq1145
  have eq7943 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq7813 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7813
  have eq7974 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X1)) = (σ (M.op X3 X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq7943 X3 x
       have i₂ := eq66 X1 x X0
       grind)
    | (have i₁ := eq7943 X0 (M.op X0 X0)
       have i₂ := eq66 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq66 eq7943
    | exact resolve eq7943 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq8177 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op X1 X1)
       have i₂ := eq7943 X1 X0
       grind)
    | exact superpose eq7943 eq16
    | exact resolve eq16 eq7943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7943
  have eq8274 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq8177 x X1
       have i₂ := eq8177 X0 x
       grind)
    | exact superpose eq8177 eq8177
    | exact resolve eq8177 eq8177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11687 : ∀ X0 X1 X3 : G, (σ (M.op X3 X3)) = (M.op X1 (τ (τ (M.op X0 X0)))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq7974 X1 x X3
       have i₂ := eq8274 X0 x
       grind)
    | exact superpose eq8274 eq7974
    | exact resolve eq7974 eq8274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7974 eq8274
  have eq13463 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1130 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq1130
    | (have j0 := eq1130 (τ X0)
       grind)
    | exact resolve eq1130 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1130
  have eq13474 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq13463 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq13463
    | (have j0 := eq13463 X0
       grind)
    | exact resolve eq13463 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13463
  have eq13481 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq13474 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq13474
    | (have j0 := eq13474 X0
       grind)
    | exact resolve eq13474 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13474
  have eq14639 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = (σ (k (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1134 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq1134
    | (have j0 := eq1134 (τ X0) X1
       grind)
    | exact resolve eq1134 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14722 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (M.op X0 X0) = (σ (k y y)) := by
    intro X0
    first
    | (have i₁ := eq1134 y X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1134
    | (have j0 := eq1134 y X0
       grind)
    | exact resolve eq1134 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1134
  have eq14837 : ∀ X0 : G, (M.op X0 X0) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14722 X0
       have i₂ := eq109
       grind)
    | exact superpose eq109 eq14722
    | exact resolve eq14722 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq14722
  have eq14842 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 (σ (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14639 X0 X1
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq14639
    | (have j0 := eq14639 X0 X1
       grind)
    | exact resolve eq14639 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq14639
  have eq14846 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14842 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq14842
    | (have j0 := eq14842 X0 X1
       grind)
    | exact resolve eq14842 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14842
  have eq87343 : ∀ X0 : G, (M.op X0 X0) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq14837 eq13481
    | (have j0 := eq13481 (σ y)
       grind)
    | exact resolve eq13481 eq14837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14837
  have eq87355 : ∀ X0 : G, (M.op X0 X0) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have j0 := eq87343 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87343
  have eq89076 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13481 X1
       have i₂ := eq14846 X1 X0
       grind)
    | exact superpose eq14846 eq13481
    | (have j0 := eq13481 X1
       have j1 := eq14846 X1 X1
       grind)
    | (have r₁ := eq13481 (M.op X1 X1)
       have r₂ := eq14846 (M.op X1 X1) X1
       grind)
    | exact resolve eq13481 eq14846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13481 eq14846
  have eq89181 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq89076 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89076
  have eq351608 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have j1 := eq89181 x y
       grind)
    | (have r₁ := eq103
       have r₂ := eq89181 x y
       grind)
    | (have r₁ := eq103
       have r₂ := eq89181 y y
       grind)
    | exact resolve eq103 eq89181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq351623 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq351608 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq351608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351608
  have eq351624 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq351623
       have r₂ := eq87355 (σ x)
       grind)
    | (have r₁ := eq351623
       have r₂ := eq87355 (σ y)
       grind)
    | exact resolve eq351623 eq87355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87355 eq351623
  have eq351639 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq27 eq351624
    | exact resolve eq351624 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351624
  have eq351641 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq351639
       have r₂ := eq28
       grind)
    | exact resolve eq351639 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351639
  have eq351718 : ∀ X0 : G, (M.op X0 X0) = (τ (σ y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq351641 eq8177
    | exact resolve eq8177 eq351641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8177 eq351641
  have eq351963 : ∀ X0 : G, (M.op X0 X0) = y ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq30 eq351718
    | exact resolve eq351718 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq351718
  have eq351969 : y = (M.op y y) := by
    first
    | (have j0 := eq351963 y
       have j1 := eq89181 x y
       grind)
    | (have r₁ := eq351963 x
       have r₂ := eq89181 x y
       grind)
    | (have r₁ := eq351963 x
       have r₂ := eq89181 y y
       grind)
    | exact resolve eq351963 eq89181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89181 eq351963
  have eq351971 : ∀ X0 : G, (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq351969
       have i₂ := eq67 y X0
       grind)
    | (have i₁ := eq351969
       have i₂ := eq67 X0 y
       grind)
    | exact superpose eq67 eq351969
    | exact resolve eq351969 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq351969
  have eq355231 : ∀ X0 : G, y = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11687 x (τ (τ (M.op x x))) X0
       have i₂ := eq351971 (τ (τ (M.op x x)))
       grind)
    | exact superpose eq351971 eq11687
    | exact resolve eq11687 eq351971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11687
  have eq355348 : y = (σ y) := by
    first
    | (have i₁ := eq355231 x
       have i₂ := eq351971 x
       grind)
    | exact superpose eq351971 eq355231
    | exact resolve eq355231 eq351971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355231
  have eq356091 : y = (σ y) := by
    first
    | (have i₁ := eq355348
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq355348
    | exact resolve eq355348 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355348
  have eq356348 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq356091 eq27
    | exact resolve eq27 eq356091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq364694 : ∀ X0 X2 X3 X5 : G, y = (M.op X2 (M.op (M.op X3 (M.op X0 (M.op (M.op x y) y))) X5)) := by
    intro X0 X2 X3 X5
    first
    | (have i₁ := eq1350 X0 x X2 X3 X5
       have i₂ := eq351971 x
       grind)
    | exact superpose eq351971 eq1350
    | exact resolve eq1350 eq351971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1350 eq351971
  have eq365213 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | exact superpose eq364694 eq364694
    | exact resolve eq364694 eq364694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364694
  have eq412676 : y = (M.op x y) := by
    first
    | (have i₁ := eq365213 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq365213
    | (have j0 := eq365213 x
       grind)
    | exact resolve eq365213 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq414323 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq412676 eq21
    | exact resolve eq21 eq412676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq412676
  have eq414538 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq414323
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq414323
    | exact resolve eq414323 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq414323
  have eq414608 : y = (σ (M.op x y)) := by
    first
    | exact superpose eq356091 eq414538
    | exact resolve eq414538 eq356091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356091 eq414538
  have eq427906 : y = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq356348
       have i₂ := eq365213 sF2
       grind)
    | exact superpose eq365213 eq356348
    | exact resolve eq356348 eq365213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356348 eq365213
  have eq427907 : y ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq427906 eq28
    | exact resolve eq28 eq427906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq427906
  have eq428059 : False := by grind
  exact eq428059

/-- `Equation3506`: `x ◇ x = y ◇ ((z ◇ w) ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyy_pxy_pyy_pxy_Equation3506 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3506 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3506.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq32 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq32 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq32 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq32 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq46 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
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
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
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
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq54 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq55 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq56 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq52 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq52 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq57 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq54 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq54 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq54 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq58 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq55 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq55 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq55 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq64 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq58 X0 X1
       have j1 := eq56 X1 X0
       grind)
    | (have r₁ := eq58 X1 X0
       have r₂ := eq56 X0 X1
       grind)
    | exact resolve eq58 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq58
  have eq67 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq64 X0 X1
       have i₂ := eq34 X1
       grind)
    | exact superpose eq34 eq64
    | (have j0 := eq64 X0 X1
       grind)
    | exact resolve eq64 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq64
  have eq213 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq57 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq217 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq213 X0 X1
       have j1 := eq67 X0 X1
       grind)
    | (have r₁ := eq213 X0 X1
       have r₂ := eq67 X0 X1
       grind)
    | (have r₁ := eq213 X1 X1
       have r₂ := eq67 X1 X1
       grind)
    | exact resolve eq213 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq213
  have eq512 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq217 (σ X0) (σ X1)
       grind)
    | exact superpose eq217 eq15
    | exact resolve eq15 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq518 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq512 X0 X1
       have i₂ := eq217 X0 X1
       grind)
    | exact superpose eq217 eq512
    | exact resolve eq512 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217 eq512
  have eq520 : False := by grind
  exact eq520

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(Y,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyy_x_pxy_pyx_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
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
  clear eq36
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
  have eq51 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 y x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op (M.op X3 X1) X0) X0
       have i₂ := eq14 X0 X1 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X0 X1 X2 X3
       have i₂ := eq14 X2 X1 X0
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq59 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : (M.op x y) ≠ (M.op x x) ∨ (M.op y x) = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq27
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
    | (have i₁ := eq44
       have i₂ := eq68 x
       grind)
    | exact superpose eq68 eq44
    | exact resolve eq44 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq72 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq68 sF2
       grind)
    | exact superpose eq68 eq50
    | exact resolve eq50 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq73 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq72
       have i₂ := eq68 x
       grind)
    | exact superpose eq68 eq72
    | exact resolve eq72 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
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
  clear eq70
  have eq79 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
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
    | (have r₁ := eq11 (M.op X0 X0) X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq79 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq79
    | (have j0 := eq79 (σ X0) (σ X1)
       grind)
    | exact resolve eq79 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq79 x y
       grind)
    | exact superpose eq79 eq45
    | (have j1 := eq79 x y
       grind)
    | exact resolve eq45 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq90
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq90
    | exact resolve eq90 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq99 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq97
    | exact resolve eq97 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq105 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq106 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq107 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq110 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq106
       have i₂ := eq68 sF3
       grind)
    | exact superpose eq68 eq106
    | exact resolve eq106 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq112 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq110
       have i₂ := eq68 y
       grind)
    | exact superpose eq68 eq110
    | exact resolve eq110 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq119 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq105
       grind)
    | exact superpose eq105 eq16
    | exact resolve eq16 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq112
       grind)
    | exact superpose eq112 eq16
    | exact resolve eq16 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq145 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq148 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq145
       have i₂ := eq68 sF1
       grind)
    | exact superpose eq68 eq145
    | exact resolve eq145 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq150 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq148
       have i₂ := eq68 sF0
       grind)
    | exact superpose eq68 eq148
    | exact resolve eq148 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq239 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x y) X0)) = (M.op X1 (M.op (M.op X0 y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq241 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x y) X0)) = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq239 X0 X1
       have i₂ := eq14 X1 y X0
       grind)
    | exact superpose eq14 eq239
    | exact resolve eq239 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq246 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ x) (σ y)) X0)) = (M.op X1 (M.op (M.op X0 (σ y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq249 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ x) (σ y)) X0)) = (M.op X1 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq246 x X0
       have i₂ := eq14 X0 sF3 x
       grind)
    | exact superpose eq14 eq246
    | exact resolve eq246 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246
  have eq346 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq35 X0 (τ X0)
       have i₂ := eq68 (τ X0)
       grind)
    | exact superpose eq68 eq35
    | exact resolve eq35 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq357 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq346 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq346
    | exact resolve eq346 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346
  have eq359 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq357 X0
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq357
    | exact resolve eq357 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq357
  have eq379 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq39
  have eq718 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq85 X0 X1
       have i₂ := eq75 X1
       grind)
    | exact superpose eq75 eq85
    | (have j0 := eq85 X0 X1
       grind)
    | exact resolve eq85 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq776 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq99 eq79
    | (have j0 := eq79 (σ x) (σ y)
       grind)
    | exact resolve eq79 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq777 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq776
    | exact resolve eq776 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776
  have eq780 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq777
       have r₂ := eq28
       grind)
    | exact resolve eq777 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777
  have eq824 : ∀ X0 X1 X2 X3 : G, (M.op X2 (σ X1)) = (M.op X2 (M.op (σ (k X0 X1)) X3)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq55 X3 (σ X1) X2 (σ X0)
       have i₂ := eq718 X0 X1
       grind)
    | exact superpose eq718 eq55
    | (have j1 := eq718 X0 X1
       grind)
    | exact resolve eq55 eq718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq825 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq718 X0 X1
       grind)
    | exact superpose eq718 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq718 X0 X1
       grind)
    | exact resolve eq13 eq718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq831 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq825 X0 X1
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq825
    | (have j0 := eq825 X0 X1
       grind)
    | exact resolve eq825 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq825
  have eq847 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq831 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq831
    | (have j0 := eq831 X0 X1
       grind)
    | exact resolve eq831 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831
  have eq866 : (τ (σ x)) = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq780 eq130
    | exact resolve eq130 eq780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780
  have eq874 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq866
    | exact resolve eq866 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq866
  have eq875 : x = (M.op y y) := by grind
  clear eq874
  have eq876 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq112
       have i₂ := eq875
       grind)
    | exact superpose eq875 eq112
    | exact resolve eq112 eq875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq877 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X1 y X0 y
       have i₂ := eq875
       grind)
    | exact superpose eq875 eq55
    | exact resolve eq55 eq875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq881 : ∀ X0 : G, x ≠ (M.op y X0) ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq875
       grind)
    | exact superpose eq875 eq13
    | (have j0 := eq13 X0 y
       grind)
    | exact resolve eq13 eq875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq884 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq876
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq876
    | exact resolve eq876 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq876
  have eq886 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X1)) := by
    intro X0 X1
    first
    | exact superpose eq884 eq55
    | exact resolve eq55 eq884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq890 : ∀ X0 : G, (σ x) ≠ (M.op (σ y) X0) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq884 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | exact resolve eq13 eq884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq895 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq877 X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq877
    | (have j0 := eq877 X0 y
       grind)
    | exact resolve eq877 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq920 : ∀ X0 : G, (M.op (M.op x y) X0) ≠ (M.op (M.op x y) y) ∨ (k X0 (M.op x y)) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq895 eq13
    | (have j0 := eq13 X0 (M.op x y)
       grind)
    | (have r₁ := eq13 y (M.op x y)
       have r₂ := eq895 (M.op x y)
       grind)
    | (have r₁ := eq13 (M.op x y) y
       have r₂ := eq895 y
       grind)
    | exact resolve eq13 eq895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq927 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq895 eq150
    | exact resolve eq150 eq895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq934 : ∀ X0 : G, (M.op (M.op x y) X0) ≠ (M.op (M.op x y) y) ∨ (k X0 (M.op x y)) = (M.op X0 y) := by
    intro X0
    first
    | exact superpose eq895 eq920
    | (have j0 := eq920 X0
       grind)
    | (have r₁ := eq920 (M.op x y)
       have r₂ := eq895 (M.op x y)
       grind)
    | exact resolve eq920 eq895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq895 eq920
  have eq1002 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq27 eq886
    | (have j0 := eq886 X0 (σ y)
       grind)
    | exact resolve eq886 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1449 : (σ x) ≠ (M.op (σ y) (σ y)) ∨ (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq1002 eq890
    | (have j0 := eq890 (σ y)
       grind)
    | exact resolve eq890 eq1002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1002
  have eq1453 : (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have r₁ := eq1449
       have r₂ := eq884
       grind)
    | exact resolve eq1449 eq884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1449
  have eq5528 : (M.op y y) = (k y (M.op x y)) := by
    first
    | (have j0 := eq934 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq934
  have eq5533 : x = (k y (M.op x y)) := by
    first
    | (have i₁ := eq5528
       have i₂ := eq875
       grind)
    | exact superpose eq875 eq5528
    | exact resolve eq5528 eq875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5528
  have eq5540 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq5533 eq107
    | exact resolve eq107 eq5533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5533
  have eq5543 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq5540
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq5540
    | exact resolve eq5540 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5540
  have eq6657 : ∀ X0 X1 : G, (M.op X0 (σ (M.op x y))) = (M.op X0 (M.op (k (σ y) (σ (M.op x y))) X1)) ∨ (σ y) = (σ (M.op (M.op x y) (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq107 eq824
    | (have j0 := eq824 y (M.op x y) x x
       grind)
    | exact resolve eq824 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq824
  have eq6731 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) X1)) = (M.op X0 (σ (M.op x y))) ∨ (σ y) = (σ (M.op (M.op x y) (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq5543 eq6657
    | exact resolve eq6657 eq5543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5543 eq6657
  have eq6816 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) X1)) = (M.op X0 (σ (M.op x y))) ∨ (σ y) = (σ (M.op (M.op x y) (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq21 eq6731
    | (have j0 := eq6731 X0 X1
       grind)
    | exact resolve eq6731 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6731
  have eq6875 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) ∨ (σ y) = (σ (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq886 eq6816
    | exact resolve eq6816 eq886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6816
  have eq6918 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq150 eq6875
    | (have j0 := eq6875 X0
       grind)
    | exact resolve eq6875 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150 eq6875
  have eq6943 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq6918 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq6918
    | (have j0 := eq6918 X0
       grind)
    | exact resolve eq6918 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6918
  have eq9707 : ∀ X0 : G, (k (M.op X0 X0) X0) = (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq379 X0
       have i₂ := eq359 X0
       grind)
    | exact superpose eq359 eq379
    | (have j0 := eq379 X0
       grind)
    | exact resolve eq379 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359 eq379
  have eq9859 : (k (M.op (σ x) (σ x)) (σ x)) = (σ (M.op x (M.op x x))) ∨ (M.op x x) = (M.op x (M.op x x)) := by
    first
    | exact superpose eq29 eq9707
    | exact resolve eq9707 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq9707
  have eq9909 : (σ (M.op x y)) = (k (M.op (σ x) (σ x)) (σ x)) ∨ (M.op x x) = (M.op x (M.op x x)) := by
    first
    | (have i₁ := eq9859
       have i₂ := eq877 x x
       grind)
    | exact superpose eq877 eq9859
    | exact resolve eq9859 eq877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9859
  have eq9936 : (σ (M.op x y)) = (k (M.op (σ x) (σ x)) (σ x)) ∨ (M.op x x) = (M.op x (M.op x x)) := by
    first
    | (have i₁ := eq9909
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq9909
    | exact resolve eq9909 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9909
  have eq9963 : (σ (M.op x y)) = (k (M.op (σ x) (σ x)) (σ x)) ∨ (M.op x x) = (M.op x (M.op x x)) := by
    first
    | exact superpose eq21 eq9936
    | exact resolve eq9936 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9936
  have eq9988 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (k (M.op (σ x) (σ x)) (σ x)) := by
    first
    | (have i₁ := eq9963
       have i₂ := eq877 x x
       grind)
    | exact superpose eq877 eq9963
    | exact resolve eq9963 eq877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq877 eq9963
  have eq10010 : (σ (M.op x y)) = (k (M.op (σ x) (σ x)) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq9988
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq9988
    | exact resolve eq9988 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9988
  have eq10055 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq10010
  have eq10056 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq886 eq10055
    | exact resolve eq10055 eq886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10055
  have eq10058 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq27 eq10056
    | exact resolve eq10056 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10056
  have eq10060 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq10058
       have r₂ := eq28
       grind)
    | exact resolve eq10058 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10058
  have eq10062 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq886 eq10060
    | exact resolve eq10060 eq886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq886 eq10060
  have eq10064 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq27 eq10062
    | exact resolve eq10062 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10062
  have eq10069 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq10064 eq66
    | (have r₁ := eq66
       have r₂ := eq10064
       grind)
    | exact resolve eq66 eq10064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq10070 : (M.op x x) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq10064 eq73
    | exact resolve eq73 eq10064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10082 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) = (M.op X0 (σ x)) ∨ (M.op x y) = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq10064 eq55
    | exact resolve eq55 eq10064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10064
  have eq10090 : (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq10069
  have eq10093 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq249 eq10082
    | exact resolve eq10082 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249 eq10082
  have eq10477 : (M.op x y) ≠ (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq10070
  have eq10953 : (k y x) = (τ (M.op (σ y) (σ x))) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq10090 eq119
    | exact resolve eq119 eq10090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq10090
  have eq10966 : (σ x) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq884 eq10093
    | exact resolve eq10093 eq884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq884
  have eq11030 : (M.op y y) = (τ (M.op (σ y) (σ x))) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq10093 eq130
    | exact resolve eq130 eq10093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq10093
  have eq11040 : x = (τ (M.op (σ y) (σ x))) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq11030
       have i₂ := eq875
       grind)
    | exact superpose eq875 eq11030
    | exact resolve eq11030 eq875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11030
  have eq11047 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq10966 eq890
    | (have j0 := eq890 (σ x)
       grind)
    | (have r₁ := eq890 (σ x)
       have r₂ := eq10966
       grind)
    | exact resolve eq890 eq10966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10966
  have eq11055 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq11047
  have eq11059 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq27 eq11055
    | exact resolve eq11055 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11055
  have eq11246 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq11059 eq59
    | exact resolve eq59 eq11059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq11059
  have eq12253 : x = (k y x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq10953 eq11040
    | exact resolve eq11040 eq10953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10953 eq11040
  have eq12290 : (M.op x y) = (M.op x x) ∨ x = (k y x) := by grind
  clear eq12253
  have eq12298 : (M.op x y) ≠ (M.op x y) ∨ (M.op y x) = (k y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq65
       have i₂ := eq12290
       grind)
    | exact superpose eq12290 eq65
    | (have r₁ := eq65
       have r₂ := eq12290
       grind)
    | exact resolve eq65 eq12290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12311 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x y) X1)) = (M.op X0 x) ∨ x = (k y x) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X1 x X0 x
       have i₂ := eq12290
       grind)
    | exact superpose eq12290 eq55
    | exact resolve eq55 eq12290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq12290
  have eq12321 : (M.op y x) = (k y x) ∨ x = (k y x) := by grind
  clear eq12298
  have eq12323 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ x = (k y x) := by
    intro X0
    first
    | exact superpose eq241 eq12311
    | exact resolve eq12311 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241 eq12311
  have eq12378 : x ≠ (M.op y x) ∨ x = (k y x) := by grind
  clear eq12321
  have eq12446 : x = (M.op y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq875
       have i₂ := eq12323 y
       grind)
    | exact superpose eq12323 eq875
    | exact resolve eq875 eq12323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq875 eq12323
  have eq12490 : x = (k y x) := by
    first
    | (have r₁ := eq12446
       have r₂ := eq12378
       grind)
    | exact resolve eq12446 eq12378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12378 eq12446
  have eq12505 : y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq12490
       have i₂ := eq79 y x
       grind)
    | exact superpose eq79 eq12490
    | (have j1 := eq79 y x
       grind)
    | exact resolve eq12490 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12506 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq105
       have i₂ := eq12490
       grind)
    | exact superpose eq12490 eq105
    | exact resolve eq105 eq12490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq12508 : (σ x) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq847 y x
       have i₂ := eq12490
       grind)
    | exact superpose eq12490 eq847
    | (have j0 := eq847 y x
       grind)
    | exact resolve eq847 eq12490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq847
  have eq12512 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have j1 := eq718 x y
       grind)
    | (have r₁ := eq12508
       have r₂ := eq718 x y
       grind)
    | exact resolve eq12508 eq718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718 eq12508
  have eq12514 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq12506
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq12506
    | exact resolve eq12506 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12506
  have eq12516 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12512
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq12512
    | exact resolve eq12512 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12512
  have eq12519 : (k (σ x) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12516
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq12516
    | exact resolve eq12516 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12516
  have eq12522 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12519
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq12519
    | exact resolve eq12519 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12519
  have eq12524 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | exact superpose eq27 eq12522
    | exact resolve eq12522 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12522
  have eq12526 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq12524
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq12524
    | exact resolve eq12524 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq12524
  have eq12528 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq12526
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq12526
    | exact resolve eq12526 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12526
  have eq12531 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq12514
       have i₂ := eq79 sF3 sF2
       grind)
    | exact superpose eq79 eq12514
    | (have j1 := eq79 (σ y) (σ x)
       grind)
    | exact resolve eq12514 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq12549 : y ≠ (M.op x y) ∨ (M.op y x) = (k y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq65
       have i₂ := eq12505
       grind)
    | exact superpose eq12505 eq65
    | exact resolve eq65 eq12505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq12555 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq12505
  have eq12573 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq12555
       have i₂ := eq12490
       grind)
    | exact superpose eq12490 eq12555
    | exact resolve eq12555 eq12490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12555
  have eq12576 : x = (M.op y x) ∨ y ≠ (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq12549
       have i₂ := eq12490
       grind)
    | exact superpose eq12490 eq12549
    | exact resolve eq12549 eq12490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12490 eq12549
  have eq12577 : y ≠ (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq12576
  have eq12579 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq12573
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12573
    | exact resolve eq12573 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12573
  have eq12581 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq12579
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12579
    | exact resolve eq12579 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12579
  have eq12605 : (τ (σ y)) = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq12531 eq73
    | exact resolve eq73 eq12531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq12531
  have eq12635 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq30 eq12605
    | exact resolve eq12605 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq12605
  have eq12858 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq12635 eq890
    | (have j0 := eq890 (σ x)
       grind)
    | (have r₁ := eq890 (σ x)
       have r₂ := eq12635
       grind)
    | exact resolve eq890 eq12635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq890 eq12635
  have eq12868 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq12858
  have eq12872 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq12868
    | exact resolve eq12868 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12868
  have eq13039 : x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq12581
       have r₂ := eq12577
       grind)
    | exact resolve eq12581 eq12577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12577 eq12581
  have eq13042 : x ≠ x ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq881 x
       have i₂ := eq13039
       grind)
    | exact superpose eq13039 eq881
    | (have j0 := eq881 x
       grind)
    | (have r₁ := eq881 x
       have r₂ := eq13039
       grind)
    | exact resolve eq881 eq13039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq881 eq13039
  have eq13049 : (M.op x y) = (k x y) ∨ x = (M.op x y) := by grind
  clear eq13042
  have eq13053 : (M.op x y) = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13049
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq13049
    | exact resolve eq13049 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13049
  have eq13058 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11246
       have i₂ := eq13053
       grind)
    | exact superpose eq13053 eq11246
    | exact resolve eq11246 eq13053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11246
  have eq13060 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq13053
       grind)
    | exact superpose eq13053 eq45
    | exact resolve eq45 eq13053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq13053
  have eq13069 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq13060
    | exact resolve eq13060 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13060
  have eq13070 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq13058
       have r₂ := eq10477
       grind)
    | exact resolve eq13058 eq10477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10477 eq13058
  have eq13097 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13069 eq12528
    | exact resolve eq12528 eq13069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12528
  have eq13098 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13069 eq12872
    | exact resolve eq12872 eq13069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12872
  have eq13104 : y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq13098
       have r₂ := eq28
       grind)
    | exact resolve eq13098 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13098
  have eq13105 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq13097
       have r₂ := eq28
       grind)
    | exact resolve eq13097 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13097
  have eq13174 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13070
       have i₂ := eq13104
       grind)
    | exact superpose eq13104 eq13070
    | exact resolve eq13070 eq13104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13070 eq13104
  have eq13195 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq13174
  have eq13221 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13195 eq21
    | exact resolve eq21 eq13195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13195
  have eq13308 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13221
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq13221
    | exact resolve eq13221 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq13221
  have eq13575 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq13105
  have eq13595 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12514 eq13575
    | exact resolve eq13575 eq12514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12514 eq13575
  have eq13598 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq13595
    | exact resolve eq13595 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13595
  have eq13599 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq13598
    | exact resolve eq13598 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13598
  have eq14747 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13599 eq28
    | exact resolve eq28 eq13599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13599
  have eq14761 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq14747
       have r₂ := eq13308
       grind)
    | exact resolve eq14747 eq13308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13308 eq14747
  have eq14770 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14761 eq1453
    | exact resolve eq1453 eq14761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1453 eq14761
  have eq14780 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq14770
    | exact resolve eq14770 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14770
  have eq14791 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14780 eq13069
    | exact resolve eq13069 eq14780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13069 eq14780
  have eq14798 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq14791
  have eq14803 : x = (M.op x y) := by
    first
    | (have r₁ := eq14798
       have r₂ := eq28
       grind)
    | exact resolve eq14798 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14798
  have eq14806 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq14803 eq21
    | exact resolve eq21 eq14803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14822 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq14803 eq927
    | exact resolve eq927 eq14803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq927 eq14803
  have eq14890 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq14822
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14822
    | exact resolve eq14822 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq14822
  have eq14903 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq14806
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq14806
    | exact resolve eq14806 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq14806
  have eq14926 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq14890
    | exact resolve eq14890 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq14890
  have eq14936 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq14903 eq27
    | exact resolve eq27 eq14903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq14903
  have eq15296 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq14936 eq6943
    | exact resolve eq6943 eq14936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6943
  have eq15311 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq14926 eq15296
    | exact resolve eq15296 eq14926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15296
  have eq15324 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq15311
       have r₂ := eq28
       grind)
    | exact resolve eq15311 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15311
  have eq15336 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq14926 eq15324
    | exact resolve eq15324 eq14926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15324
  have eq15439 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq15336 eq14936
    | exact resolve eq14936 eq15336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14936 eq15336
  have eq15440 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14926 eq15439
    | exact resolve eq15439 eq14926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14926 eq15439
  have eq15497 : False := by grind
  exact eq15497

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,X) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pxx_pxx_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq36 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq36 (σ X0)
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq39
    | exact resolve eq39 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq39
  have eq63 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 (M.op X1 X1) (k X1 X0)
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 (M.op X1 X0) (M.op X1 X1)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) X2)) = (M.op X2 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X0 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq9 X0 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 (M.op X2 (M.op (M.op X0 X1) X2)) (M.op X2 X0)
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq63 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq73 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq68 X0 X1 X2
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq68
    | (have j0 := eq68 X0 X1 X2
       grind)
    | exact resolve eq68 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq180 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq72 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq182 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq180 X0 X1
       have j1 := eq73 (M.op X0 X1) (k X0 X1) x
       grind)
    | (have r₁ := eq180 X0 X1
       have r₂ := eq73 X0 X1 X0
       grind)
    | (have r₁ := eq180 X1 X0
       have r₂ := eq73 X0 X1 X1
       grind)
    | (have r₁ := eq180 X0 X1
       have r₂ := eq73 (M.op X0 X1) (M.op X0 X0) x
       grind)
    | exact resolve eq180 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq180
  have eq194 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq182 (σ X0) (σ X1)
       grind)
    | exact superpose eq182 eq15
    | (have j1 := eq182 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq182 (τ X0) X1
       grind)
    | exact superpose eq182 eq18
    | (have j1 := eq182 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq18 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq182
  have eq613 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq196 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq196
    | exact resolve eq196 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq642 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq613 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq613
    | (have j0 := eq613 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq613 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613
  have eq1378 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq194 x y
       grind)
    | exact superpose eq194 eq16
    | (have j1 := eq194 x y
       grind)
    | exact resolve eq16 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq1416 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1378
       have i₂ := eq642 x y
       grind)
    | exact superpose eq642 eq1378
    | (have j1 := eq642 (σ x) (σ y)
       grind)
    | (have r₁ := eq1378
       have r₂ := eq642 x y
       grind)
    | (have r₁ := eq1378
       have r₂ := eq642 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq1378
       have r₂ := eq642 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq1378 eq642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642 eq1378
  have eq1417 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq1416
  have eq1465 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1417
       grind)
    | exact superpose eq1417 eq16
    | exact resolve eq16 eq1417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1417
  have eq1466 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq1465
       have r₂ := eq44 x
       grind)
    | exact resolve eq1465 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1465
  have eq1467 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1466
       grind)
    | exact superpose eq1466 eq16
    | exact resolve eq16 eq1466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1468 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1466
       grind)
    | exact superpose eq1466 eq10
    | exact resolve eq10 eq1466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1466
  have eq1507 : x = y := by
    first
    | (have i₁ := eq1468
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1468
    | exact resolve eq1468 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1468
  have eq1508 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1467
       have i₂ := eq44 x
       grind)
    | exact superpose eq44 eq1467
    | exact resolve eq1467 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq1467
  have eq1509 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1508
       have i₂ := eq1507
       grind)
    | exact superpose eq1507 eq1508
    | exact resolve eq1508 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1507 eq1508
  have eq1510 : False := by grind
  exact eq1510

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,X) else if X = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pxx_pyx_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq36 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq36 (σ X0)
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq39
    | exact resolve eq39 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq39
  have eq63 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 (M.op X1 X1) (k X1 X0)
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 (M.op X1 X0) (M.op X1 X1)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) X2)) = (M.op X2 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X0 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq9 X0 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 (M.op X2 (M.op (M.op X0 X1) X2)) (M.op X2 X0)
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq63 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq73 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq68 X0 X1 X2
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq68
    | (have j0 := eq68 X0 X1 X2
       grind)
    | exact resolve eq68 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq180 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq72 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq182 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq180 X0 X1
       have j1 := eq73 (M.op X0 X1) (k X0 X1) x
       grind)
    | (have r₁ := eq180 X0 X1
       have r₂ := eq73 X0 X1 X0
       grind)
    | (have r₁ := eq180 X1 X0
       have r₂ := eq73 X0 X1 X1
       grind)
    | (have r₁ := eq180 X0 X1
       have r₂ := eq73 (M.op X0 X1) (M.op X0 X0) x
       grind)
    | exact resolve eq180 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq180
  have eq194 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq182 (σ X0) (σ X1)
       grind)
    | exact superpose eq182 eq15
    | (have j1 := eq182 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq182 (τ X0) X1
       grind)
    | exact superpose eq182 eq18
    | (have j1 := eq182 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq18 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq182
  have eq613 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq196 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq196
    | exact resolve eq196 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq642 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq613 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq613
    | (have j0 := eq613 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq613 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613
  have eq1378 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq194 x y
       grind)
    | exact superpose eq194 eq16
    | (have j1 := eq194 x y
       grind)
    | exact resolve eq16 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq1416 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1378
       have i₂ := eq642 x y
       grind)
    | exact superpose eq642 eq1378
    | (have j1 := eq642 (σ x) (σ y)
       grind)
    | (have r₁ := eq1378
       have r₂ := eq642 x y
       grind)
    | (have r₁ := eq1378
       have r₂ := eq642 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq1378
       have r₂ := eq642 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq1378 eq642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642 eq1378
  have eq1417 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq1416
  have eq1465 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1417
       grind)
    | exact superpose eq1417 eq16
    | exact resolve eq16 eq1417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1417
  have eq1466 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq1465
       have r₂ := eq44 x
       grind)
    | exact resolve eq1465 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1465
  have eq1467 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1466
       grind)
    | exact superpose eq1466 eq16
    | exact resolve eq16 eq1466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1468 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1466
       grind)
    | exact superpose eq1466 eq10
    | exact resolve eq10 eq1466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1466
  have eq1507 : x = y := by
    first
    | (have i₁ := eq1468
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1468
    | exact resolve eq1468 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1468
  have eq1508 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1467
       have i₂ := eq44 x
       grind)
    | exact superpose eq44 eq1467
    | exact resolve eq1467 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq1467
  have eq1509 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1508
       have i₂ := eq1507
       grind)
    | exact superpose eq1507 eq1508
    | exact resolve eq1508 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1507 eq1508
  have eq1510 : False := by grind
  exact eq1510

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pxy_pxx_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq36 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq36 (σ X0)
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq38
    | exact resolve eq38 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq38
  have eq62 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 (M.op X1 X0) (k X1 X0)
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 (M.op X1 X0) (M.op X1 X1)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq62 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq72 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq71 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq78 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq72 (σ X1) (σ X0)
       grind)
    | exact superpose eq72 eq15
    | (have j1 := eq72 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq72 X1 (τ X0)
       grind)
    | exact superpose eq72 eq18
    | (have j1 := eq72 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq18 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq72
  have eq401 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq79 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq79
    | exact resolve eq79 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq425 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq401 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq401
    | (have j0 := eq401 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq401 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401
  have eq734 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq78 x y
       grind)
    | exact superpose eq78 eq16
    | (have j1 := eq78 x y
       grind)
    | exact resolve eq16 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq763 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq734
       have i₂ := eq425 x y
       grind)
    | exact superpose eq425 eq734
    | (have j1 := eq425 (σ x) (σ y)
       grind)
    | (have r₁ := eq734
       have r₂ := eq425 x y
       grind)
    | (have r₁ := eq734
       have r₂ := eq425 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq734
       have r₂ := eq425 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq734 eq425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425 eq734
  have eq764 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq763
  have eq806 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq764
       grind)
    | exact superpose eq764 eq10
    | exact resolve eq10 eq764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764
  have eq837 : x = y ∨ x = y := by
    first
    | (have i₁ := eq806
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq806
    | exact resolve eq806 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806
  have eq838 : x = y := by grind
  clear eq837
  have eq840 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq838
       grind)
    | exact superpose eq838 eq16
    | exact resolve eq16 eq838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq838
  have eq841 : False := by grind
  exact eq841
