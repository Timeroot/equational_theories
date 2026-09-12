import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation842`: `x = x ◇ ((y ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyy_pyx_pxy_pyx_Equation842 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law842 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law842.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
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
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq122 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq122 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq122 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq122 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq131 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq123 (σ X0)
       grind)
    | exact superpose eq123 eq15
    | exact resolve eq15 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq144 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq131 X0
       have i₂ := eq123 X0
       grind)
    | exact superpose eq123 eq131
    | exact resolve eq131 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq131
  have eq168 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (M.op X1 X1) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq144 X0
       grind)
    | exact superpose eq144 eq13
    | (have j0 := eq13 (σ X0) X1
       grind)
    | exact resolve eq13 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq172 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 X0)) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0)
       have i₂ := eq144 X0
       grind)
    | exact superpose eq144 eq9
    | exact resolve eq9 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 (M.op X0 X0)
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq14 (M.op X1 X1) X1
       have r₂ := eq12 X0 (M.op X1 X1)
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq198 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (M.op (σ (M.op X1 X1)) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq172 X1 (σ X0)
       have i₂ := eq144 X0
       grind)
    | exact superpose eq144 eq172
    | exact resolve eq172 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172
  have eq210 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq183 (σ X1) (σ X0)
       grind)
    | exact superpose eq183 eq15
    | (have j1 := eq183 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq222 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq210 X0 X1
       have i₂ := eq144 X1
       grind)
    | exact superpose eq144 eq210
    | (have j0 := eq210 X0 X1
       grind)
    | exact resolve eq210 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq229 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq222 X0 X1
       have i₂ := eq144 X0
       grind)
    | exact superpose eq144 eq222
    | (have j0 := eq222 X0 X1
       grind)
    | exact resolve eq222 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq453 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq229 x y
       grind)
    | exact superpose eq229 eq16
    | (have j1 := eq229 x y
       grind)
    | exact resolve eq16 eq229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq634 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq198 X0 X0
       have i₂ := eq144 (M.op X0 X0)
       grind)
    | exact superpose eq144 eq198
    | exact resolve eq198 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq1096 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq453
       have i₂ := eq183 y x
       grind)
    | exact superpose eq183 eq453
    | (have j1 := eq183 y x
       grind)
    | exact resolve eq453 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq453
  have eq1099 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq1096
  have eq1114 : (M.op y y) = (τ (σ (M.op x x))) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq1099
       grind)
    | exact superpose eq1099 eq10
    | exact resolve eq10 eq1099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1099
  have eq1143 : (M.op x x) = (M.op y y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq1114
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq1114
    | exact resolve eq1114 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1114
  have eq1144 : (M.op x x) = (M.op y y) := by grind
  clear eq1143
  have eq1148 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ y = (M.op x x) ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq1144
       grind)
    | exact superpose eq1144 eq13
    | (have j0 := eq13 x X0
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1144
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1144
       grind)
    | exact resolve eq13 eq1144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3961 : (M.op x y) = (k x y) ∨ y = (M.op x x) := by
    first
    | (have j0 := eq1148 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1148
  have eq6762 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq168 X0 (σ X0)
       have i₂ := eq144 X0
       grind)
    | exact superpose eq144 eq168
    | (have j0 := eq168 X1 (σ X0)
       grind)
    | (have r₁ := eq168 X0 (σ X0)
       have r₂ := eq144 X0
       grind)
    | exact resolve eq168 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144 eq168
  have eq6777 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6762 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq6762
    | (have j0 := eq6762 X0 X1
       grind)
    | exact resolve eq6762 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6762
  have eq324124 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (M.op (σ X0) (σ y)) = (σ (k X0 y)) ∨ (σ y) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq6777 y x
       have i₂ := eq1144
       grind)
    | exact superpose eq1144 eq6777
    | (have j0 := eq6777 X0 x
       grind)
    | exact resolve eq6777 eq1144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6777
  have eq324485 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have j0 := eq324124 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324124
  have eq324500 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq324485
       grind)
    | exact superpose eq324485 eq16
    | exact resolve eq16 eq324485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324485
  have eq324683 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq324500
       have i₂ := eq3961
       grind)
    | exact superpose eq3961 eq324500
    | exact resolve eq324500 eq3961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3961 eq324500
  have eq324686 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq324683
  have eq324951 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq324686
       grind)
    | exact superpose eq324686 eq10
    | exact resolve eq10 eq324686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324686
  have eq325431 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq324951
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq324951
    | exact resolve eq324951 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324951
  have eq325432 : y = (M.op x x) := by grind
  clear eq325431
  have eq325605 : ∀ X0 : G, (M.op X0 (M.op y (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 x
       have i₂ := eq325432
       grind)
    | exact superpose eq325432 eq9
    | exact resolve eq9 eq325432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq325665 : (σ x) = (M.op (σ x) (σ (M.op y y))) := by
    first
    | (have i₁ := eq634 x
       have i₂ := eq325432
       grind)
    | exact superpose eq325432 eq634
    | exact resolve eq634 eq325432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634
  have eq326093 : (σ x) = (M.op (σ x) (σ (M.op x x))) := by
    first
    | (have i₁ := eq325665
       have i₂ := eq1144
       grind)
    | exact superpose eq1144 eq325665
    | exact resolve eq325665 eq1144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325665
  have eq326121 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq326093
       have i₂ := eq325432
       grind)
    | exact superpose eq325432 eq326093
    | exact resolve eq326093 eq325432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326093
  have eq327946 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq326121
       grind)
    | exact superpose eq326121 eq16
    | exact resolve eq16 eq326121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326121
  have eq329516 : x = (M.op x (M.op y y)) := by
    first
    | (have i₁ := eq325605 x
       have i₂ := eq325432
       grind)
    | exact superpose eq325432 eq325605
    | exact resolve eq325605 eq325432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325605
  have eq329601 : x = (M.op x (M.op x x)) := by
    first
    | (have i₁ := eq329516
       have i₂ := eq1144
       grind)
    | exact superpose eq1144 eq329516
    | exact resolve eq329516 eq1144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1144 eq329516
  have eq329638 : x = (M.op x y) := by
    first
    | (have i₁ := eq329601
       have i₂ := eq325432
       grind)
    | exact superpose eq325432 eq329601
    | exact resolve eq329601 eq325432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325432 eq329601
  have eq329675 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq327946
       have i₂ := eq329638
       grind)
    | exact superpose eq329638 eq327946
    | exact resolve eq327946 eq329638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327946 eq329638
  have eq329682 : False := by grind
  exact eq329682

/-- `Equation882`: `x = y ◇ ((x ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_pyy_pyx_Equation882 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law882 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law882.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq51 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq64 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (σ (M.op X0 X0)) = (k X1 (σ X0)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq13
    | (have j0 := eq13 (σ (M.op X0 X0)) (k X1 (σ X0))
       grind)
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq101 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) ∨ (τ X1) = X0 := by
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
  have eq102 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq99 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq99
    | (have j0 := eq99 X0 X1
       grind)
    | exact resolve eq99 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq281 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq102 x y
       grind)
    | exact superpose eq102 eq16
    | (have j1 := eq102 x y
       grind)
    | exact resolve eq16 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq290 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (k X1 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq102 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq910 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq101 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq101
    | exact resolve eq101 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq951 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq910 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq910
    | (have j0 := eq910 X0 X1
       grind)
    | exact resolve eq910 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq910
  have eq1596 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq281
       have i₂ := eq951 y x
       grind)
    | exact superpose eq951 eq281
    | (have j1 := eq951 y x
       grind)
    | (have r₁ := eq281
       have r₂ := eq951 y x
       grind)
    | (have r₁ := eq281
       have r₂ := eq951 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq281
       have r₂ := eq951 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq281 eq951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281 eq951
  have eq1597 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq1596
  have eq1799 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq290 (τ X1) (τ X0)
       have i₂ := eq51 X1 X0
       grind)
    | exact superpose eq51 eq290
    | (have j0 := eq290 (τ X1) (τ X0)
       grind)
    | exact resolve eq290 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq1827 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1799 X0 X1
       have i₂ := eq30 X1
       grind)
    | exact superpose eq30 eq1799
    | (have j0 := eq1799 X0 X1
       grind)
    | exact resolve eq1799 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1799
  have eq1847 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1827 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1827
    | (have j0 := eq1827 X0 X1
       grind)
    | exact resolve eq1827 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1827
  have eq1864 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1847 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1847
    | (have j0 := eq1847 X0 X1
       grind)
    | exact resolve eq1847 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1847
  have eq1877 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X1))) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1864 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1864
    | (have j0 := eq1864 X0 X1
       grind)
    | exact resolve eq1864 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1864
  have eq1886 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1877 X0 X1
       have i₂ := eq30 X1
       grind)
    | exact superpose eq30 eq1877
    | (have j0 := eq1877 X0 X1
       grind)
    | exact resolve eq1877 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1877
  have eq1895 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1886 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1886
    | (have j0 := eq1886 X0 X1
       grind)
    | exact resolve eq1886 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1886
  have eq1899 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1895 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1895
    | (have j0 := eq1895 X0 X1
       grind)
    | exact resolve eq1895 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1895
  have eq20205 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1597
       grind)
    | exact superpose eq1597 eq16
    | exact resolve eq16 eq1597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1597
  have eq20206 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq20205
       have r₂ := eq22 x
       grind)
    | exact resolve eq20205 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20205
  have eq20209 : (M.op x x) ≠ (M.op x x) ∨ (k y x) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq20206
       grind)
    | exact superpose eq20206 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq20206
       grind)
    | exact resolve eq13 eq20206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20206
  have eq20244 : x = y ∨ (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq20209
  have eq24271 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20244
       grind)
    | exact superpose eq20244 eq16
    | exact resolve eq16 eq20244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20244
  have eq24272 : (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq24271
       have r₂ := eq22 x
       grind)
    | exact resolve eq24271 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24271
  have eq24282 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq290 x y
       have i₂ := eq24272
       grind)
    | exact superpose eq24272 eq290
    | (have j0 := eq290 x y
       grind)
    | exact resolve eq290 eq24272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290 eq24272
  have eq24310 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by grind
  clear eq24282
  have eq24311 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by grind
  clear eq24310
  have eq24672 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24311
       grind)
    | exact superpose eq24311 eq16
    | exact resolve eq16 eq24311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24681 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq64 x (σ y)
       have i₂ := eq24311
       grind)
    | exact superpose eq24311 eq64
    | (have j0 := eq64 x (σ y)
       grind)
    | (have r₁ := eq64 x (σ y)
       have r₂ := eq24311
       grind)
    | exact resolve eq64 eq24311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq24311
  have eq24736 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq24681
  have eq24737 : (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq24736
  have eq24754 : (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq24737
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq24737
    | exact resolve eq24737 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24737
  have eq25040 : y = (τ (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq24754
       grind)
    | exact superpose eq24754 eq10
    | exact resolve eq10 eq24754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24754
  have eq25229 : x = y ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq25040
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq25040
    | exact resolve eq25040 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25040
  have eq25231 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25229
       grind)
    | exact superpose eq25229 eq16
    | exact resolve eq16 eq25229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25229
  have eq25232 : (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq25231
       have r₂ := eq22 x
       grind)
    | exact resolve eq25231 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25231
  have eq25489 : (k y x) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq25232
       grind)
    | exact superpose eq25232 eq10
    | exact resolve eq10 eq25232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25232
  have eq25679 : (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq25489
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq25489
    | exact resolve eq25489 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25489
  have eq25698 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq1899 y x
       have i₂ := eq25679
       grind)
    | exact superpose eq25679 eq1899
    | (have j0 := eq1899 y x
       grind)
    | (have r₁ := eq1899 y x
       have r₂ := eq25679
       grind)
    | exact resolve eq1899 eq25679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1899 eq25679
  have eq25719 : x = y ∨ (M.op x y) = (M.op x x) := by grind
  clear eq25698
  have eq26092 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25719
       grind)
    | exact superpose eq25719 eq16
    | exact resolve eq16 eq25719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25719
  have eq26095 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq26092
       have r₂ := eq22 x
       grind)
    | exact resolve eq26092 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26092
  have eq26096 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq24672
       have i₂ := eq26095
       grind)
    | exact superpose eq26095 eq24672
    | exact resolve eq24672 eq26095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24672
  have eq26135 : (σ x) = (σ y) := by grind
  clear eq26096
  have eq26494 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq26135
       grind)
    | exact superpose eq26135 eq16
    | exact resolve eq16 eq26135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26135
  have eq26685 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq26494
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq26494
    | exact resolve eq26494 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq26494
  have eq26686 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq26685
       have i₂ := eq26095
       grind)
    | exact superpose eq26095 eq26685
    | exact resolve eq26685 eq26095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26095 eq26685
  have eq26687 : False := by grind
  exact eq26687

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,Y) else if m(X,X) = m(Y,X) then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxx_pyx_pyy_x_pyx_Equation909 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law909 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a ≠ M.op b a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0))) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : ∀ X0 : G, (τ (σ X0)) = (τ (σ X0)) := by
    intro X0
    grind
  have eq18 : ∀ X0 : G, (τ (σ X0)) = (τ (σ X0)) := by
    intro X0
    first
    | (have j0 := eq17 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq19 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq10 X0
       grind)
    | exact resolve eq10 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 : G, (σ (τ X0)) = (σ (τ X0)) := by
    intro X0
    grind
  have eq21 : ∀ X0 : G, (σ (τ X0)) = (σ (τ X0)) := by
    intro X0
    first
    | (have j0 := eq20 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq22 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0
       grind)
    | exact resolve eq11 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : (M.op x y) = (M.op x y) := by grind
  have eq24 : (M.op x y) = (M.op x y) := by grind
  clear eq23
  have eq25 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq26 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq25
  have eq27 : (σ x) = (σ x) := by grind
  have eq28 : (σ x) = (σ x) := by grind
  clear eq27
  have eq29 : (σ y) = (σ y) := by grind
  have eq30 : (σ y) = (σ y) := by grind
  clear eq29
  have eq31 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq32 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq31
  have eq33 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq34 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    first
    | exact superpose eq19 eq18
    | (have j1 := eq19 X0
       grind)
    | exact resolve eq18 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq19
  have eq35 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    first
    | exact superpose eq22 eq21
    | (have j1 := eq22 X0
       grind)
    | exact resolve eq21 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq22
  have eq36 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq26 eq34
    | (have j0 := eq34 (M.op x y)
       grind)
    | exact resolve eq34 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq34 x
       have i₂ := eq28
       grind)
    | exact superpose eq28 eq34
    | (have j0 := eq34 x
       grind)
    | exact resolve eq34 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq40 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq34 y
       have i₂ := eq30
       grind)
    | exact superpose eq30 eq34
    | (have j0 := eq34 y
       grind)
    | exact resolve eq34 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq41 : (M.op x y) = (M.op (τ (σ x)) y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq38
       grind)
    | exact superpose eq38 eq24
    | exact resolve eq24 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq38
  have eq42 : (M.op x y) = (M.op (τ (σ x)) (τ (σ y))) := by
    first
    | (have i₁ := eq41
       have i₂ := eq40
       grind)
    | exact superpose eq40 eq41
    | exact resolve eq41 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq41
  have eq46 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq34 (k X0 X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq34
    | exact resolve eq34 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq47 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq46 (τ X0) X1
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq46
    | exact resolve eq46 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 X2 : G, (k (k X0 X1) X2) = (τ (k (k (σ X0) (σ X1)) (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq46 (k X0 X1) X2
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq46
    | exact resolve eq46 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq26 eq46
    | (have j0 := eq46 (M.op x y) X0
       grind)
    | exact resolve eq46 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (k (σ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq46 X1 (τ X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq46
    | exact resolve eq46 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (k X0 (M.op x y)) = (τ (k (σ X0) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq26 eq46
    | (have j0 := eq46 X0 (M.op x y)
       grind)
    | exact resolve eq46 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : (τ (σ y)) = (M.op (τ (σ x)) (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq42 eq9
    | exact resolve eq9 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : (σ y) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq32 eq9
    | (have j0 := eq9 (σ y) (σ x)
       grind)
    | exact resolve eq9 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq26 eq51
    | (have j0 := eq51 (M.op x y)
       grind)
    | exact resolve eq51 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : (M.op (M.op x y) (M.op x y)) = (M.op (τ (σ x)) (M.op (τ (σ y)) (τ (σ y)))) := by
    first
    | exact superpose eq63 eq9
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : (M.op (M.op x y) (M.op x y)) = (M.op (τ (σ x)) (k (τ (σ y)) (τ (σ y)))) := by
    first
    | (have i₁ := eq106
       have i₂ := eq83 (τ sF5)
       grind)
    | exact superpose eq83 eq106
    | exact resolve eq106 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq109 : (k (M.op x y) (M.op x y)) = (M.op (τ (σ x)) (k (τ (σ y)) (τ (σ y)))) := by
    first
    | (have i₁ := eq107
       have i₂ := eq83 sF2
       grind)
    | exact superpose eq83 eq107
    | exact resolve eq107 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq130 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (M.op (τ (σ y)) (τ (σ y))) ∨ (M.op (τ (σ y)) (τ (σ y))) = (M.op (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq42 eq14
    | (have j0 := eq14 (τ (σ y)) (τ (σ x))
       grind)
    | exact resolve eq14 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq32 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq133
       have i₂ := eq83 sF5
       grind)
    | exact superpose eq83 eq133
    | exact resolve eq133 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq156 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op (τ (σ y)) (τ (σ y))) = (M.op (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq130
       have i₂ := eq83 (τ sF5)
       grind)
    | exact superpose eq83 eq130
    | exact resolve eq130 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq167 : (k (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq153
       have i₂ := eq83 sF5
       grind)
    | exact superpose eq83 eq153
    | exact resolve eq153 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq170 : (k (τ (σ y)) (τ (σ y))) = (M.op (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq156
       have i₂ := eq83 (τ sF5)
       grind)
    | exact superpose eq83 eq156
    | exact resolve eq156 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156
  have eq203 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq47 X1 (τ X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq47
    | exact resolve eq47 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq289 : (k (τ (σ y)) (τ (σ y))) = (M.op (τ (σ x)) (M.op (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq109 eq9
    | exact resolve eq9 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq290 : (k (τ (σ y)) (τ (σ y))) = (M.op (τ (σ x)) (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq289
       have i₂ := eq83 (k sF2 sF2)
       grind)
    | exact superpose eq83 eq289
    | exact resolve eq289 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289
  have eq298 : ∀ X0 : G, (M.op X0 (M.op (k X0 X0) (k X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq9
    | exact resolve eq9 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq299 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X0 X0) ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq13
    | (have j0 := eq13 X0 X1
       grind)
    | exact resolve eq13 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq301 : ∀ X0 X1 : G, (M.op X0 (k (M.op X0 X1) (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0
       have i₂ := eq83 (M.op X0 X1)
       grind)
    | exact superpose eq83 eq9
    | exact resolve eq9 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq303 : (σ y) = (M.op (σ x) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq65
       have i₂ := eq83 sF6
       grind)
    | exact superpose eq83 eq65
    | exact resolve eq65 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq305 : ∀ X0 : G, (M.op X0 (k (k X0 X0) (k X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq298 X0
       have i₂ := eq83 (k X0 X0)
       grind)
    | exact superpose eq83 eq298
    | exact resolve eq298 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq441 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq62 X0 X1
       grind)
    | exact superpose eq62 eq9
    | exact resolve eq9 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq442 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq83 (M.op X0 X1)
       have i₂ := eq62 X1 X0
       grind)
    | exact superpose eq62 eq83
    | exact resolve eq83 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq448 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op X0 X1)) = (M.op X0 (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq442 X0 X1
       have i₂ := eq83 X1
       grind)
    | exact superpose eq83 eq442
    | exact resolve eq442 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442
  have eq449 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (k (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq441 X0 X1
       have i₂ := eq83 (M.op X0 (M.op X1 X1))
       grind)
    | exact superpose eq83 eq441
    | exact resolve eq441 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441
  have eq466 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq449 X0 X1
       have i₂ := eq448 (M.op X0 X1) (M.op X0 (M.op X1 X1))
       grind)
    | exact superpose eq448 eq449
    | exact resolve eq449 eq448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449
  have eq481 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op (M.op X0 X1) (M.op X0 (k X1 X1))) (M.op (M.op X0 X1) (M.op X0 (k X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq466 X0 X0
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq466
    | exact resolve eq466 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466
  have eq493 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op (M.op X0 X1) (k (M.op X0 X1) (M.op X0 X1))) (M.op (M.op X0 X1) (k (M.op X0 X1) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq481 X0 X1
       have i₂ := eq448 X0 X1
       grind)
    | exact superpose eq448 eq481
    | exact resolve eq481 eq448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481
  have eq498 : ∀ X0 X1 : G, (M.op X0 X1) = (k (k (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X0 X1))) (k (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq493 X0 X1
       have i₂ := eq448 (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq448 eq493
    | exact resolve eq493 eq448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493
  have eq500 : ∀ X0 X1 : G, (M.op X0 X1) = (k (k (k (M.op X0 X1) (M.op X0 X1)) (k (M.op X0 X1) (M.op X0 X1))) (k (k (M.op X0 X1) (M.op X0 X1)) (k (M.op X0 X1) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq498 X0 X1
       have i₂ := eq83 (M.op X0 X1)
       grind)
    | exact superpose eq83 eq498
    | exact resolve eq498 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498
  have eq602 : (M.op (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y)))) = (M.op (τ (σ x)) (M.op (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))))) := by
    first
    | exact superpose eq290 eq62
    | exact resolve eq62 eq290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq609 : (M.op (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y)))) = (M.op (τ (σ x)) (k (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))))) := by
    first
    | (have i₁ := eq602
       have i₂ := eq83 (k (k sF2 sF2) (k sF2 sF2))
       grind)
    | exact superpose eq83 eq602
    | exact resolve eq602 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602
  have eq614 : (M.op (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y)))) = (k (M.op (τ (σ x)) (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y)))) (M.op (τ (σ x)) (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))))) := by
    first
    | (have i₁ := eq609
       have i₂ := eq448 (τ sF4) (k (k sF2 sF2) (k sF2 sF2))
       grind)
    | exact superpose eq448 eq609
    | exact resolve eq609 eq448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609
  have eq617 : (M.op (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y)))) = (k (k (M.op (τ (σ x)) (k (M.op x y) (M.op x y))) (M.op (τ (σ x)) (k (M.op x y) (M.op x y)))) (k (M.op (τ (σ x)) (k (M.op x y) (M.op x y))) (M.op (τ (σ x)) (k (M.op x y) (M.op x y))))) := by
    first
    | (have i₁ := eq614
       have i₂ := eq448 (τ sF4) (k sF2 sF2)
       grind)
    | exact superpose eq448 eq614
    | exact resolve eq614 eq448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614
  have eq619 : (M.op (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y)))) = (k (k (k (M.op (τ (σ x)) (M.op x y)) (M.op (τ (σ x)) (M.op x y))) (k (M.op (τ (σ x)) (M.op x y)) (M.op (τ (σ x)) (M.op x y)))) (k (k (M.op (τ (σ x)) (M.op x y)) (M.op (τ (σ x)) (M.op x y))) (k (M.op (τ (σ x)) (M.op x y)) (M.op (τ (σ x)) (M.op x y))))) := by
    first
    | (have i₁ := eq617
       have i₂ := eq448 (τ sF4) sF2
       grind)
    | exact superpose eq448 eq617
    | exact resolve eq617 eq448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617
  have eq621 : (M.op (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y)))) = (M.op (τ (σ x)) (M.op x y)) := by
    first
    | (have i₁ := eq619
       have i₂ := eq500 (τ sF4) sF2
       grind)
    | exact superpose eq500 eq619
    | exact resolve eq619 eq500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500 eq619
  have eq623 : (k (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y)))) = (M.op (τ (σ x)) (M.op x y)) := by
    first
    | (have i₁ := eq621
       have i₂ := eq83 (k (τ sF5) (τ sF5))
       grind)
    | exact superpose eq83 eq621
    | exact resolve eq621 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621
  have eq625 : (M.op (τ (σ x)) (M.op (M.op x y) (M.op x y))) = (M.op (k (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y)))) (k (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y))))) := by
    first
    | exact superpose eq623 eq62
    | exact resolve eq62 eq623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq632 : (M.op (τ (σ x)) (M.op (M.op x y) (M.op x y))) = (k (k (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y)))) (k (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y))))) := by
    first
    | (have i₁ := eq625
       have i₂ := eq83 (k (k (τ sF5) (τ sF5)) (k (τ sF5) (τ sF5)))
       grind)
    | exact superpose eq83 eq625
    | exact resolve eq625 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625
  have eq637 : (τ (σ y)) = (k (k (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y)))) (k (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y))))) := by
    first
    | exact superpose eq63 eq632
    | exact resolve eq632 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq632
  have eq650 : (τ (σ x)) = (M.op (τ (σ y)) (M.op (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y))))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq170 eq9
    | exact resolve eq9 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170
  have eq651 : (τ (σ x)) = (M.op (τ (σ y)) (k (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y))))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq650
       have i₂ := eq83 (k (τ sF5) (τ sF5))
       grind)
    | exact superpose eq83 eq650
    | exact resolve eq650 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650
  have eq656 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq651
       have i₂ := eq305 (τ sF5)
       grind)
    | exact superpose eq305 eq651
    | exact resolve eq651 eq305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651
  have eq671 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ y)))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq656 eq15
    | exact resolve eq15 eq656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656
  have eq675 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq671
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq671
    | exact resolve eq671 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671
  have eq679 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq675
    | exact resolve eq675 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq675
  have eq704 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq679 eq15
    | exact resolve eq15 eq679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679
  have eq705 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq704
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq704
    | exact resolve eq704 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704
  have eq706 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq705
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq705
    | exact resolve eq705 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705
  have eq707 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq706
    | exact resolve eq706 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706
  have eq708 : (M.op x y) = (τ (k (σ y) (σ y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq707 eq36
    | exact resolve eq36 eq707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707
  have eq724 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq708
       have i₂ := eq203 sF5 sF5
       grind)
    | exact superpose eq203 eq708
    | exact resolve eq708 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708
  have eq1464 : ∀ X0 : G, (k (M.op X0 (τ (σ y))) (M.op X0 (τ (σ y)))) = (M.op X0 (M.op x y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq724 eq448
    | exact resolve eq448 eq724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724
  have eq1484 : ∀ X0 : G, (k (M.op X0 (k X0 X0)) (M.op X0 (k X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq305 X0
       have i₂ := eq448 X0 (k X0 X0)
       grind)
    | exact superpose eq448 eq305
    | exact resolve eq305 eq448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1485 : ∀ X0 X1 : G, (k (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq301 X0 X1
       have i₂ := eq448 X0 (M.op X0 X1)
       grind)
    | exact superpose eq448 eq301
    | exact resolve eq301 eq448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1502 : (σ y) = (k (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq303
       have i₂ := eq448 sF4 sF6
       grind)
    | exact superpose eq448 eq303
    | exact resolve eq303 eq448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1517 : ∀ X0 : G, (k (k (M.op X0 X0) (M.op X0 X0)) (k (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1484 x
       have i₂ := eq448 x x
       grind)
    | exact superpose eq448 eq1484
    | exact resolve eq1484 eq448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1484
  have eq1534 : ∀ X0 : G, (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1517 X0
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq1517
    | exact resolve eq1517 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1517
  have eq1751 : (M.op x y) ≠ (k (τ (σ y)) (τ (σ y))) ∨ (k (τ (σ y)) (τ (σ y))) = (M.op (τ (σ y)) (τ (σ x))) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq42 eq299
    | (have j0 := eq299 (τ (σ y)) (τ (σ x))
       grind)
    | exact resolve eq299 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1760 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (k (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq32 eq299
    | (have j0 := eq299 (σ y) (σ x)
       grind)
    | exact resolve eq299 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299
  have eq1990 : ∀ X0 : G, (τ (σ y)) = (M.op X0 (M.op X0 (M.op x y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq1464 eq301
    | exact resolve eq301 eq1464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301 eq1464
  have eq2046 : (τ (σ y)) = (M.op (M.op x y) (k (M.op x y) (M.op x y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq1990 sF2
       have i₂ := eq83 sF2
       grind)
    | exact superpose eq83 eq1990
    | exact resolve eq1990 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1990
  have eq2072 : (τ (σ y)) = (k (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq2046
       have i₂ := eq448 sF2 sF2
       grind)
    | exact superpose eq448 eq2046
    | exact resolve eq2046 eq448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2046
  have eq2082 : (τ (σ y)) = (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq2072
       have i₂ := eq83 sF2
       grind)
    | exact superpose eq83 eq2072
    | exact resolve eq2072 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2072
  have eq2110 : (σ y) = (σ (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y)))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq2082 eq35
    | exact resolve eq35 eq2082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2082
  have eq2125 : (σ y) = (k (σ (k (M.op x y) (M.op x y))) (σ (k (M.op x y) (M.op x y)))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq2110
       have i₂ := eq15 (k sF2 sF2) (k sF2 sF2)
       grind)
    | exact superpose eq15 eq2110
    | exact resolve eq2110 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2110
  have eq2141 : (σ y) = (k (k (σ (M.op x y)) (σ (M.op x y))) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq2125
       have i₂ := eq15 sF2 sF2
       grind)
    | exact superpose eq15 eq2125
    | exact resolve eq2125 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2125
  have eq2149 : (σ y) = (k (k (σ (M.op x y)) (σ (M.op x y))) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq2141
    | exact resolve eq2141 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2141
  have eq2211 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq2149 eq305
    | exact resolve eq305 eq2149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2149
  have eq2246 : (M.op x y) = (τ (k (σ y) (σ x))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq2211 eq36
    | exact resolve eq36 eq2211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2247 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (k (σ y) (σ x)) (σ X0))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq2211 eq51
    | exact resolve eq51 eq2211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq2248 : ∀ X0 : G, (k X0 (M.op x y)) = (τ (k (σ X0) (k (σ y) (σ x)))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq2211 eq56
    | exact resolve eq56 eq2211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq2261 : ∀ X0 : G, (k X0 (M.op x y)) = (k X0 (τ (k (σ y) (σ x)))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq2248 x
       have i₂ := eq52 (k sF5 sF4) x
       grind)
    | exact superpose eq52 eq2248
    | exact resolve eq2248 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq2248
  have eq2262 : ∀ X0 : G, (k (M.op x y) X0) = (k (τ (k (σ y) (σ x))) X0) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq2247 x
       have i₂ := eq47 (k sF5 sF4) x
       grind)
    | exact superpose eq47 eq2247
    | exact resolve eq2247 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq2247
  have eq2263 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq2246
       have i₂ := eq203 sF4 sF5
       grind)
    | exact superpose eq203 eq2246
    | exact resolve eq2246 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2246
  have eq2270 : ∀ X0 : G, (k X0 (M.op x y)) = (k X0 (k (τ (σ y)) (τ (σ x)))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq2261 X0
       have i₂ := eq203 sF4 sF5
       grind)
    | exact superpose eq203 eq2261
    | exact resolve eq2261 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2261
  have eq2271 : ∀ X0 : G, (k (M.op x y) X0) = (k (k (τ (σ y)) (τ (σ x))) X0) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq2262 X0
       have i₂ := eq203 sF4 sF5
       grind)
    | exact superpose eq203 eq2262
    | exact resolve eq2262 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2262
  have eq8078 : ∀ X0 X1 : G, (τ X0) = (k (τ (M.op X1 (M.op X1 X0))) (τ (M.op X1 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq203 (M.op X1 (M.op X1 X0)) (M.op X1 (M.op X1 X0))
       have i₂ := eq1485 X1 X0
       grind)
    | exact superpose eq1485 eq203
    | exact resolve eq203 eq1485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8198 : (τ (σ x)) = (k (τ (M.op (σ y) (k (σ y) (σ y)))) (τ (M.op (σ y) (k (σ y) (σ y))))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq167 eq8078
    | exact resolve eq8078 eq167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq8245 : (τ (σ x)) = (k (τ (k (M.op (σ y) (σ y)) (M.op (σ y) (σ y)))) (τ (k (M.op (σ y) (σ y)) (M.op (σ y) (σ y))))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq8198
       have i₂ := eq448 sF5 sF5
       grind)
    | exact superpose eq448 eq8198
    | exact resolve eq8198 eq448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8198
  have eq8294 : (τ (σ x)) = (k (k (τ (M.op (σ y) (σ y))) (τ (M.op (σ y) (σ y)))) (k (τ (M.op (σ y) (σ y))) (τ (M.op (σ y) (σ y))))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq8245
       have i₂ := eq203 (M.op sF5 sF5) (M.op sF5 sF5)
       grind)
    | exact superpose eq203 eq8245
    | exact resolve eq8245 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8245
  have eq8337 : (τ (σ x)) = (k (k (τ (k (σ y) (σ y))) (τ (k (σ y) (σ y)))) (k (τ (k (σ y) (σ y))) (τ (k (σ y) (σ y))))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq8294
       have i₂ := eq83 sF5
       grind)
    | exact superpose eq83 eq8294
    | exact resolve eq8294 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8294
  have eq8373 : (τ (σ x)) = (k (k (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y)))) (k (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y))))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq8337
       have i₂ := eq203 sF5 sF5
       grind)
    | exact superpose eq203 eq8337
    | exact resolve eq8337 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8337
  have eq8401 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq637 eq8373
    | exact resolve eq8373 eq637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8373
  have eq8470 : (σ (M.op x y)) ≠ (k (σ y) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq8401 eq33
    | exact resolve eq33 eq8401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8480 : (k (σ y) (σ y)) ≠ (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  have eq8863 : (k (σ y) (σ y)) ≠ (k (σ y) (σ y)) ∨ (k (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq8401 eq1760
    | (have r₁ := eq1760
       have r₂ := eq8401
       grind)
    | exact resolve eq1760 eq8401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1760 eq8401
  have eq8867 : (k (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq8863
  have eq11375 : (τ (σ x)) = (k (τ (M.op (σ y) (k (σ y) (σ y)))) (τ (M.op (σ y) (k (σ y) (σ y))))) ∨ (σ y) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq8867 eq8078
    | exact resolve eq8078 eq8867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8078 eq8867
  have eq11378 : (τ (σ x)) = (k (τ (k (M.op (σ y) (σ y)) (M.op (σ y) (σ y)))) (τ (k (M.op (σ y) (σ y)) (M.op (σ y) (σ y))))) ∨ (σ y) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq11375
       have i₂ := eq448 sF5 sF5
       grind)
    | exact superpose eq448 eq11375
    | exact resolve eq11375 eq448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11375
  have eq11398 : (τ (σ x)) = (k (k (τ (M.op (σ y) (σ y))) (τ (M.op (σ y) (σ y)))) (k (τ (M.op (σ y) (σ y))) (τ (M.op (σ y) (σ y))))) ∨ (σ y) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq11378
       have i₂ := eq203 (M.op sF5 sF5) (M.op sF5 sF5)
       grind)
    | exact superpose eq203 eq11378
    | exact resolve eq11378 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11378
  have eq11412 : (τ (σ x)) = (k (k (τ (k (σ y) (σ y))) (τ (k (σ y) (σ y)))) (k (τ (k (σ y) (σ y))) (τ (k (σ y) (σ y))))) ∨ (σ y) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq11398
       have i₂ := eq83 sF5
       grind)
    | exact superpose eq83 eq11398
    | exact resolve eq11398 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11398
  have eq11418 : (τ (σ x)) = (k (k (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y)))) (k (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y))))) ∨ (σ y) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq11412
       have i₂ := eq203 sF5 sF5
       grind)
    | exact superpose eq203 eq11412
    | exact resolve eq11412 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11412
  have eq11419 : (τ (σ x)) = (τ (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq637 eq11418
    | exact resolve eq11418 eq637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11418
  have eq11420 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) := by grind
  clear eq11419
  have eq11424 : (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq11420 eq33
    | exact resolve eq33 eq11420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11420
  have eq11530 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq2211 eq11424
    | (have r₁ := eq11424
       have r₂ := eq2211
       grind)
    | exact resolve eq11424 eq2211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11424
  have eq11533 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq11530
  have eq11534 : (σ y) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq11533
  have eq11542 : (τ (σ y)) = (k (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq11534 eq203
    | exact resolve eq203 eq11534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11901 : ∀ X0 : G, (k X0 (M.op x y)) = (k X0 (τ (σ y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq11542 eq2270
    | exact resolve eq2270 eq11542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2270
  have eq11902 : ∀ X0 : G, (k (M.op x y) X0) = (k (τ (σ y)) X0) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq11542 eq2271
    | exact resolve eq2271 eq11542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2271
  have eq11913 : ∀ X0 : G, (k (M.op x y) X0) = (k (τ (σ y)) X0) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | (have j0 := eq11902 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11902
  have eq11914 : ∀ X0 : G, (k X0 (M.op x y)) = (k X0 (τ (σ y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | (have j0 := eq11901 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11901
  have eq12356 : (M.op x y) = (k (M.op x y) (τ (σ x))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq11913 eq2263
    | exact resolve eq2263 eq11913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2263
  have eq12364 : (τ (σ y)) = (k (M.op x y) (τ (σ x))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq11913 eq11542
    | exact resolve eq11542 eq11913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11542 eq11913
  have eq12422 : (τ (σ y)) = (k (M.op x y) (τ (σ x))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq12364
  have eq12427 : (M.op x y) = (k (M.op x y) (τ (σ x))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq12356
  have eq12465 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (τ (σ x)))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq12427 eq15
    | exact resolve eq15 eq12427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12427
  have eq12481 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq12465
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq12465
    | exact resolve eq12465 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12465
  have eq12486 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq26 eq12481
    | exact resolve eq12481 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12481
  have eq12634 : (σ (σ (M.op x y))) = (k (σ (σ (M.op x y))) (σ (σ x))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq12486 eq15
    | exact resolve eq15 eq12486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12486
  have eq12713 : (σ y) = (σ (k (M.op x y) (τ (σ x)))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq12422 eq35
    | exact resolve eq35 eq12422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12422
  have eq12726 : (σ y) = (k (σ (M.op x y)) (σ (τ (σ x)))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq12713
       have i₂ := eq15 sF2 (τ sF4)
       grind)
    | exact superpose eq15 eq12713
    | exact resolve eq12713 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12713
  have eq12747 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq12726
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq12726
    | exact resolve eq12726 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12726
  have eq12753 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq26 eq12747
    | exact resolve eq12747 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12747
  have eq12829 : (σ (σ y)) = (k (σ (σ (M.op x y))) (σ (σ x))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq12753 eq15
    | exact resolve eq15 eq12753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12753
  have eq15183 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (τ (σ y)))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq11914 eq15
    | exact resolve eq15 eq11914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11914
  have eq15258 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (k X0 (M.op x y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15183 X0
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq15183
    | exact resolve eq15183 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15183
  have eq15260 : ∀ X0 : G, (k (σ X0) (σ y)) = (k (σ X0) (σ (M.op x y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15258 X0
       have i₂ := eq15 X0 sF2
       grind)
    | exact superpose eq15 eq15258
    | exact resolve eq15258 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15258
  have eq15261 : ∀ X0 : G, (k (σ X0) (σ y)) = (k (σ X0) (σ (M.op x y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq15260
    | (have j0 := eq15260 X0
       grind)
    | exact resolve eq15260 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15260
  have eq16223 : ∀ X0 : G, (k (k (σ (M.op x y)) (σ x)) X0) = (τ (k (σ (σ (M.op x y))) (σ X0))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq12634 eq48
    | exact resolve eq48 eq12634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12634
  have eq16251 : ∀ X0 : G, (k (σ (M.op x y)) X0) = (k (k (σ (M.op x y)) (σ x)) X0) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16223 x
       have i₂ := eq46 sF3 x
       grind)
    | exact superpose eq46 eq16223
    | exact resolve eq16223 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16223
  have eq16268 : ∀ X0 : G, (τ (k (σ (σ y)) (σ X0))) = (k (k (σ (M.op x y)) (σ x)) X0) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq12829 eq48
    | exact resolve eq48 eq12829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq12829
  have eq16298 : ∀ X0 : G, (k (σ y) X0) = (k (k (σ (M.op x y)) (σ x)) X0) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16268 x
       have i₂ := eq46 sF5 x
       grind)
    | exact superpose eq46 eq16268
    | exact resolve eq16268 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq16268
  have eq19041 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (k X0 (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15261 (τ X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq15261
    | exact resolve eq15261 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15261
  have eq23353 : (k (σ (M.op x y)) (σ (M.op x y))) = (k (k (σ (M.op x y)) (σ x)) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq16251 eq19041
    | exact resolve eq19041 eq16251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16251 eq19041
  have eq23354 : (k (σ (M.op x y)) (σ (M.op x y))) = (k (k (σ (M.op x y)) (σ x)) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq23353
  have eq26672 : (k (σ (M.op x y)) (σ (M.op x y))) = (k (σ y) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq23354 eq16298
    | exact resolve eq16298 eq23354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16298 eq23354
  have eq26687 : (k (σ (M.op x y)) (σ (M.op x y))) = (k (σ y) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq26672
  have eq26746 : (k (M.op x y) (M.op x y)) = (τ (k (σ y) (σ y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq26687 eq72
    | exact resolve eq72 eq26687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq26916 : (k (M.op x y) (M.op x y)) = (k (τ (σ y)) (τ (σ y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq26746
       have i₂ := eq203 sF5 sF5
       grind)
    | exact superpose eq203 eq26746
    | exact resolve eq26746 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26746
  have eq29825 : (k (M.op x y) (M.op x y)) = (M.op (τ (σ x)) (k (M.op x y) (M.op x y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq26916 eq109
    | exact resolve eq109 eq26916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq26916
  have eq29933 : (k (M.op x y) (M.op x y)) = (k (M.op (τ (σ x)) (M.op x y)) (M.op (τ (σ x)) (M.op x y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq29825
       have i₂ := eq448 (τ sF4) sF2
       grind)
    | exact superpose eq448 eq29825
    | exact resolve eq29825 eq448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29825
  have eq29949 : (k (M.op x y) (M.op x y)) = (k (k (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y)))) (k (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y))))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq623 eq29933
    | exact resolve eq29933 eq623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623 eq29933
  have eq29954 : (τ (σ y)) = (k (M.op x y) (M.op x y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq637 eq29949
    | exact resolve eq29949 eq637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637 eq29949
  have eq30030 : (σ y) = (σ (k (M.op x y) (M.op x y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq29954 eq35
    | exact resolve eq35 eq29954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29954
  have eq30048 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq30030
       have i₂ := eq15 sF2 sF2
       grind)
    | exact superpose eq15 eq30030
    | exact resolve eq30030 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30030
  have eq30084 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq26 eq30048
    | exact resolve eq30048 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30048
  have eq31361 : (σ y) = (k (σ y) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq30084 eq26687
    | exact resolve eq26687 eq30084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26687 eq30084
  have eq31434 : (σ y) = (k (σ y) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq31361
  have eq31945 : (σ y) ≠ (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq31434 eq8480
    | exact resolve eq8480 eq31434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8480 eq31434
  have eq32014 : (σ y) ≠ (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq31945
  have eq32044 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have r₁ := eq32014
       have r₂ := eq11534
       grind)
    | exact resolve eq32014 eq11534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11534 eq32014
  have eq32517 : (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq32044 eq33
    | exact resolve eq33 eq32044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32044
  have eq32571 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | (have r₁ := eq32517
       have r₂ := eq2211
       grind)
    | exact resolve eq32517 eq2211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2211 eq32517
  have eq32604 : (σ y) = (k (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq32571 eq1485
    | exact resolve eq1485 eq32571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32571
  have eq32637 : (σ y) = (k (k (σ (M.op x y)) (σ (M.op x y))) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | (have i₁ := eq32604
       have i₂ := eq83 sF3
       grind)
    | exact superpose eq83 eq32604
    | exact resolve eq32604 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32604
  have eq33031 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq32637 eq1534
    | exact resolve eq1534 eq32637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1534 eq32637
  have eq33171 : (M.op x y) = (τ (k (σ y) (σ y))) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq33031 eq36
    | exact resolve eq36 eq33031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq33219 : (k (σ y) (σ y)) ≠ (k (σ y) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq33031 eq8470
    | (have r₁ := eq8470
       have r₂ := eq33031
       grind)
    | exact resolve eq8470 eq33031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8470
  have eq33361 : (k (σ y) (σ y)) ≠ (k (σ y) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq33219
  have eq33362 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) := by grind
  clear eq33361
  have eq33418 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | (have i₁ := eq33171
       have i₂ := eq203 sF5 sF5
       grind)
    | exact superpose eq203 eq33171
    | exact resolve eq33171 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203 eq33171
  have eq33630 : (σ y) = (k (M.op (σ x) (k (σ y) (σ x))) (M.op (σ x) (k (σ y) (σ x)))) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq33362 eq1502
    | exact resolve eq1502 eq33362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1502 eq33362
  have eq33726 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (τ (σ y)) (τ (σ x))) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq33418 eq1751
    | (have r₁ := eq1751
       have r₂ := eq33418
       grind)
    | exact resolve eq1751 eq33418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1751
  have eq33734 : (τ (σ y)) = (M.op (τ (σ y)) (k (M.op x y) (M.op x y))) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq33418 eq305
    | exact resolve eq305 eq33418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305 eq33418
  have eq33782 : (τ (σ y)) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (M.op (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (τ (σ y)) := by grind
  clear eq33726
  have eq33801 : (τ (σ y)) = (k (M.op (τ (σ y)) (M.op x y)) (M.op (τ (σ y)) (M.op x y))) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | (have i₁ := eq33734
       have i₂ := eq448 (τ sF5) sF2
       grind)
    | exact superpose eq448 eq33734
    | exact resolve eq33734 eq448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448 eq33734
  have eq236101 : (σ (τ (σ y))) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (M.op x y) = (M.op (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq33782 eq15
    | exact resolve eq15 eq33782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33782
  have eq236138 : (σ (τ (σ y))) = (k (σ (τ (σ y))) (σ x)) ∨ (M.op x y) = (M.op (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | (have i₁ := eq236101
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq236101
    | exact resolve eq236101 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236101
  have eq236144 : (M.op x y) = (M.op (τ (σ y)) (τ (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | (have i₁ := eq236138
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq236138
    | exact resolve eq236138 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236138
  have eq236176 : (τ (σ x)) = (k (M.op (τ (σ y)) (M.op x y)) (M.op (τ (σ y)) (M.op x y))) ∨ (σ y) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq236144 eq1485
    | exact resolve eq1485 eq236144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1485 eq236144
  have eq2057954 : (τ (σ x)) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq236176 eq33801
    | exact resolve eq33801 eq236176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33801 eq236176
  have eq2057960 : (σ y) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) := by grind
  clear eq2057954
  have eq2057981 : (σ y) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq2057960 eq33630
    | exact resolve eq33630 eq2057960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33630 eq2057960
  have eq2058039 : (σ y) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (τ (σ x)) = (τ (σ y)) := by grind
  clear eq2057981
  have eq2058067 : (σ y) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq32 eq2058039
    | exact resolve eq2058039 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2058039
  have eq2058184 : (σ y) = (M.op (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq2058067 eq303
    | exact resolve eq303 eq2058067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq2058278 : (τ (σ x)) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32 eq2058184
    | exact resolve eq2058184 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2058184
  have eq2058298 : (σ y) = (σ (τ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2058278 eq35
    | exact resolve eq35 eq2058278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2058278
  have eq2058300 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2058298
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq2058298
    | exact resolve eq2058298 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2058298
  have eq2058320 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2058300 eq33
    | exact resolve eq33 eq2058300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2058466 : (σ y) = (k (σ y) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2058300 eq2058067
    | exact resolve eq2058067 eq2058300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2058067 eq2058300
  have eq2058564 : (σ y) ≠ (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq33031 eq2058320
    | exact resolve eq2058320 eq33031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33031 eq2058320
  have eq2058599 : (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq2058564
       have r₂ := eq2058466
       grind)
    | exact resolve eq2058564 eq2058466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2058466 eq2058564
  have eq2058783 : (σ y) = (σ (τ (σ x))) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2058599 eq35
    | exact resolve eq35 eq2058599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2058599
  have eq2058792 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2058783
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq2058783
    | exact resolve eq2058783 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2058783
  have eq2058793 : (σ x) = (σ y) := by grind
  clear eq2058792
  have eq2058796 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2058793 eq32
    | exact resolve eq32 eq2058793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq2058797 : (M.op x y) = (M.op (τ (σ x)) (τ (σ x))) := by
    first
    | exact superpose eq2058793 eq42
    | exact resolve eq42 eq2058793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq2058793
  have eq2058862 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) := by
    first
    | (have i₁ := eq2058797
       have i₂ := eq83 (τ sF4)
       grind)
    | exact superpose eq83 eq2058797
    | exact resolve eq2058797 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2058797
  have eq2058863 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq2058796
       have i₂ := eq83 sF4
       grind)
    | exact superpose eq83 eq2058796
    | exact resolve eq2058796 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq2058796
  have eq2058890 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) := by
    first
    | exact superpose eq2058863 eq33
    | exact resolve eq33 eq2058863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq2058863
  have eq2059244 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (τ (σ x)))) := by
    first
    | exact superpose eq2058862 eq15
    | exact resolve eq15 eq2058862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2058862
  have eq2059270 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq2059244
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq2059244
    | exact resolve eq2059244 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq2059244
  have eq2059615 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq2059270 eq26
    | exact resolve eq26 eq2059270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq2059270
  have eq2059674 : False := by grind
  exact eq2059674

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_y_pyx_pyy_pyx_Equation909 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law909 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0))) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
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
  have eq20 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
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
  have eq33 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k (M.op (M.op X1 X0) (M.op X1 X0)) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq12
    | (have r₁ := eq12 (M.op (M.op X0 X0) (M.op X0 X0)) X0
       have r₂ := eq9 X0 X0
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k (M.op X1 (M.op X0 X0)) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq33 X0 X1
       have i₂ := eq20 X0 X1
       grind)
    | exact superpose eq20 eq33
    | (have j0 := eq33 X0 X1
       grind)
    | (have r₁ := eq33 (M.op (M.op X1 X0) (M.op X1 X0)) (M.op X1 (M.op X0 X0))
       have r₂ := eq20 X0 X1
       grind)
    | (have r₁ := eq33 (M.op X1 (M.op X0 X0)) (M.op (M.op X1 X0) (M.op X1 X0))
       have r₂ := eq20 X0 X1
       grind)
    | exact resolve eq33 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq35 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  clear eq24
  have eq56 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq73 : ∀ X0 : G, (k (M.op X0 (M.op X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq34 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq80 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (M.op (τ X0) (M.op (τ X0) (τ X0)))
       have i₂ := eq73 (τ X0)
       grind)
    | exact superpose eq73 eq19
    | exact resolve eq19 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 : G, (k (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq80 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq80
    | exact resolve eq80 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq89 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op (M.op X1 X0) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq20 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq20
    | exact resolve eq20 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) = (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq20 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq20 X0 X1
       grind)
    | exact superpose eq20 eq20
    | exact resolve eq20 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq9
    | exact resolve eq9 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) = (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq91 X0 X1
       have i₂ := eq20 (M.op X1 X1) X0
       grind)
    | exact superpose eq20 eq91
    | exact resolve eq91 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq102 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X0) (M.op (M.op X1 X0) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq89 X0 X1
       have i₂ := eq20 (M.op X1 X0) (M.op X1 X0)
       grind)
    | exact superpose eq20 eq89
    | exact resolve eq89 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq105 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) = (M.op X0 (M.op X1 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq101 X0 X1
       have i₂ := eq20 X1 X1
       grind)
    | exact superpose eq20 eq101
    | exact resolve eq101 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq106 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq102 X0 X1
       have i₂ := eq20 X0 X1
       grind)
    | exact superpose eq20 eq102
    | exact resolve eq102 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq107 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X1 (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq106 X0 X1
       have i₂ := eq105 X1 X0
       grind)
    | exact superpose eq105 eq106
    | exact resolve eq106 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq106
  have eq116 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq93 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq93 (M.op X0 X0) X0
       grind)
    | exact superpose eq93 eq93
    | exact resolve eq93 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (M.op (σ X2) (σ X2)) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 (k X1 (τ X0)) X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq56
    | exact resolve eq56 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (M.op X1 (σ (k X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq93 X1 (σ X0)
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq93
    | (have j1 := eq56 X0 X0
       grind)
    | exact resolve eq93 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq152 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op X1 (M.op X1 (σ (k X0 X0)))) := by
    intro X0 X1
    first
    | (have j0 := eq139 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq169 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq107 (M.op X0 X0) X1
       have i₂ := eq93 (M.op X0 X0) X0
       grind)
    | exact superpose eq93 eq107
    | exact resolve eq107 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq107
  have eq183 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq169 X0 X1
       have i₂ := eq20 X0 X0
       grind)
    | exact superpose eq20 eq169
    | exact resolve eq169 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq207 : ∀ X0 X1 : G, (k (M.op X0 (M.op X0 X1)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq73 X1
       have i₂ := eq183 X1 X0
       grind)
    | (have i₁ := eq73 X0
       have i₂ := eq183 X0 X0
       grind)
    | exact superpose eq183 eq73
    | exact resolve eq73 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq183
  have eq244 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (M.op X1 (M.op X1 (τ X0)))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 (M.op X1 (M.op X1 (τ X0)))
       have i₂ := eq207 X1 (τ X0)
       grind)
    | exact superpose eq207 eq19
    | exact resolve eq19 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq247 : ∀ X0 X1 : G, (k (σ (M.op X1 (M.op X1 (τ X0)))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq244 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq244
    | exact resolve eq244 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244
  have eq22161 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 (M.op X1 (σ (k (τ X0) (τ X0))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq152 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq152
    | exact resolve eq152 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq22329 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (k (σ (τ X0)) X0))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq22161 X0 X1
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq22161
    | (have j0 := eq22161 X0 X1
       grind)
    | exact resolve eq22161 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22161
  have eq22339 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (k X0 X0))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq22329 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq22329
    | (have j0 := eq22329 X0 X1
       grind)
    | exact resolve eq22329 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22329
  have eq22426 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 (k X0 X0)) (M.op X1 (k X0 X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq20 (M.op X1 (k X0 X0)) X1
       have i₂ := eq22339 X0 X1
       grind)
    | exact superpose eq22339 eq20
    | (have j1 := eq22339 X0 X1
       grind)
    | exact resolve eq20 eq22339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22339
  have eq22506 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq22426 X0 x
       have i₂ := eq9 (k X0 X0) x
       grind)
    | exact superpose eq9 eq22426
    | (have j0 := eq22426 X0 x
       grind)
    | exact resolve eq22426 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22426
  have eq22534 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq22506 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq22506 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq22506 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22506
  have eq22562 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq22534 (σ X0)
       grind)
    | exact superpose eq22534 eq15
    | exact resolve eq15 eq22534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22568 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0 X0
       have i₂ := eq22534 (τ X0)
       grind)
    | exact superpose eq22534 eq35
    | exact resolve eq35 eq22534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq22586 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq22568 X0
       have i₂ := eq22534 X0
       grind)
    | exact superpose eq22534 eq22568
    | exact resolve eq22568 eq22534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22568
  have eq22592 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq22562 X0
       have i₂ := eq22534 X0
       grind)
    | exact superpose eq22534 eq22562
    | exact resolve eq22562 eq22534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22534 eq22562
  have eq22806 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ (M.op X0 X0)))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq247 X0 (τ X0)
       have i₂ := eq22586 X0
       grind)
    | exact superpose eq22586 eq247
    | exact resolve eq247 eq22586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247
  have eq22857 : ∀ X0 : G, (M.op (τ X0) (τ (M.op X0 X0))) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq20 (τ X0) (τ X0)
       have i₂ := eq22586 X0
       grind)
    | exact superpose eq22586 eq20
    | exact resolve eq20 eq22586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22925 : ∀ X0 : G, (M.op (τ X0) (τ (M.op X0 X0))) = (τ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq22857 X0
       have i₂ := eq22586 (M.op X0 X0)
       grind)
    | exact superpose eq22586 eq22857
    | exact resolve eq22857 eq22586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22857
  have eq22949 : ∀ X0 : G, (τ (M.op X0 (M.op X0 X0))) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq22925 X0
       have i₂ := eq20 X0 X0
       grind)
    | exact superpose eq20 eq22925
    | exact resolve eq22925 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq22925
  have eq23008 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq116 (σ X0)
       have i₂ := eq22592 X0
       grind)
    | exact superpose eq22592 eq116
    | exact resolve eq116 eq22592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24292 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (k (σ (σ (M.op (τ (τ X0)) (τ (M.op (τ X0) (τ X0)))))) X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (k (σ (σ (M.op (τ (τ X0)) (τ (M.op (τ X0) (τ X0)))))) X0) ∨ (k (σ (σ (M.op (τ (τ X0)) (τ (M.op (τ X0) (τ X0)))))) X0) = (M.op (k (σ (σ (M.op (τ (τ X0)) (τ (M.op (τ X0) (τ X0)))))) X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq133 (σ (M.op (τ (τ X0)) (τ (M.op (τ X0) (τ X0))))) X0 X1
       have i₂ := eq22806 (τ X0)
       grind)
    | exact superpose eq22806 eq133
    | (have j0 := eq133 (σ (M.op (τ (τ X0)) (τ (M.op (τ X0) (τ X0))))) X0 X1
       grind)
    | exact resolve eq133 eq22806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq22806
  have eq24309 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (k (σ (σ (τ (M.op (τ X0) (M.op (τ X0) (τ X0)))))) X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (k (σ (σ (M.op (τ (τ X0)) (τ (M.op (τ X0) (τ X0)))))) X0) ∨ (k (σ (σ (M.op (τ (τ X0)) (τ (M.op (τ X0) (τ X0)))))) X0) = (M.op (k (σ (σ (M.op (τ (τ X0)) (τ (M.op (τ X0) (τ X0)))))) X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq24292 X0 X1
       have i₂ := eq22949 (τ X0)
       grind)
    | exact superpose eq22949 eq24292
    | (have j0 := eq24292 X0 X1
       grind)
    | exact resolve eq24292 eq22949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24292
  have eq24352 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (k (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (k (σ (σ (M.op (τ (τ X0)) (τ (M.op (τ X0) (τ X0)))))) X0) ∨ (k (σ (σ (M.op (τ (τ X0)) (τ (M.op (τ X0) (τ X0)))))) X0) = (M.op (k (σ (σ (M.op (τ (τ X0)) (τ (M.op (τ X0) (τ X0)))))) X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq24309 X0 X1
       have i₂ := eq11 (M.op (τ X0) (M.op (τ X0) (τ X0)))
       grind)
    | exact superpose eq11 eq24309
    | (have j0 := eq24309 X0 X1
       grind)
    | exact resolve eq24309 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24309
  have eq24387 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (k (σ (σ (M.op (τ (τ X0)) (τ (M.op (τ X0) (τ X0)))))) X0) ∨ (k (σ (σ (M.op (τ (τ X0)) (τ (M.op (τ X0) (τ X0)))))) X0) = (M.op (k (σ (σ (M.op (τ (τ X0)) (τ (M.op (τ X0) (τ X0)))))) X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq24352 X0 X1
       have i₂ := eq87 X0
       grind)
    | exact superpose eq87 eq24352
    | (have j0 := eq24352 X0 X1
       grind)
    | exact resolve eq24352 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24352
  have eq24411 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (k (σ (σ (M.op (τ (τ X0)) (τ (M.op (τ X0) (τ X0)))))) X0) ∨ (k (σ (σ (M.op (τ (τ X0)) (τ (M.op (τ X0) (τ X0)))))) X0) = (M.op (k (σ (σ (M.op (τ (τ X0)) (τ (M.op (τ X0) (τ X0)))))) X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq24387 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq24387
    | (have j0 := eq24387 X0 X1
       grind)
    | exact resolve eq24387 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24387
  have eq24423 : ∀ X0 X1 : G, (M.op (σ X1) (σ X1)) = (k (σ (σ (τ (M.op (τ X0) (M.op (τ X0) (τ X0)))))) X0) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (k (σ (σ (M.op (τ (τ X0)) (τ (M.op (τ X0) (τ X0)))))) X0) = (M.op (k (σ (σ (M.op (τ (τ X0)) (τ (M.op (τ X0) (τ X0)))))) X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq24411 X0 X1
       have i₂ := eq22949 (τ X0)
       grind)
    | exact superpose eq22949 eq24411
    | (have j0 := eq24411 X0 X1
       grind)
    | exact resolve eq24411 eq22949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24411
  have eq24430 : ∀ X0 X1 : G, (M.op (σ X1) (σ X1)) = (k (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) X0) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (k (σ (σ (M.op (τ (τ X0)) (τ (M.op (τ X0) (τ X0)))))) X0) = (M.op (k (σ (σ (M.op (τ (τ X0)) (τ (M.op (τ X0) (τ X0)))))) X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq24423 X0 X1
       have i₂ := eq11 (M.op (τ X0) (M.op (τ X0) (τ X0)))
       grind)
    | exact superpose eq11 eq24423
    | (have j0 := eq24423 X0 X1
       grind)
    | exact resolve eq24423 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24423
  have eq24435 : ∀ X0 X1 : G, (M.op (σ X1) (σ X1)) = X0 ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (k (σ (σ (M.op (τ (τ X0)) (τ (M.op (τ X0) (τ X0)))))) X0) = (M.op (k (σ (σ (M.op (τ (τ X0)) (τ (M.op (τ X0) (τ X0)))))) X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq24430 X0 X1
       have i₂ := eq87 X0
       grind)
    | exact superpose eq87 eq24430
    | (have j0 := eq24430 X0 X1
       grind)
    | exact resolve eq24430 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24430
  have eq24439 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = X0 ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (k (σ (σ (M.op (τ (τ X0)) (τ (M.op (τ X0) (τ X0)))))) X0) = (M.op (k (σ (σ (M.op (τ (τ X0)) (τ (M.op (τ X0) (τ X0)))))) X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq24435 X0 X1
       have i₂ := eq22592 X1
       grind)
    | exact superpose eq22592 eq24435
    | (have j0 := eq24435 X0 X1
       grind)
    | exact resolve eq24435 eq22592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22592 eq24435
  have eq24443 : ∀ X0 X1 : G, (k (σ (σ (τ (M.op (τ X0) (M.op (τ X0) (τ X0)))))) X0) = (M.op (k (σ (σ (τ (M.op (τ X0) (M.op (τ X0) (τ X0)))))) X0) (σ X1)) ∨ (σ (M.op X1 X1)) = X0 ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq24439 X0 X1
       have i₂ := eq22949 (τ X0)
       grind)
    | exact superpose eq22949 eq24439
    | (have j0 := eq24439 X0 X1
       grind)
    | exact resolve eq24439 eq22949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22949 eq24439
  have eq24447 : ∀ X0 X1 : G, (k (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) X0) = (M.op (k (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) X0) (σ X1)) ∨ (σ (M.op X1 X1)) = X0 ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq24443 X0 X1
       have i₂ := eq11 (M.op (τ X0) (M.op (τ X0) (τ X0)))
       grind)
    | exact superpose eq11 eq24443
    | (have j0 := eq24443 X0 X1
       grind)
    | exact resolve eq24443 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24443
  have eq24449 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (σ (M.op X1 X1)) = X0 ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq24447 X0 X1
       have i₂ := eq87 X0
       grind)
    | exact superpose eq87 eq24447
    | (have j0 := eq24447 X0 X1
       grind)
    | exact resolve eq24447 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq24447
  have eq24450 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq24449 X0 X1
       have j1 := eq12 (σ X1) X0
       grind)
    | (have r₁ := eq24449 X1 X1
       have r₂ := eq12 (σ X1) X1
       grind)
    | (have r₁ := eq24449 (M.op (σ (M.op X1 X1)) X0) X1
       have r₂ := eq12 X0 (σ (M.op X1 X1))
       grind)
    | exact resolve eq24449 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24449
  have eq88201 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq24450 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq24450
    | (have j0 := eq24450 X1 (τ X0)
       grind)
    | exact resolve eq24450 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88275 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq24450 (σ X0) X1
       grind)
    | exact superpose eq24450 eq15
    | (have j1 := eq24450 (σ X0) X1
       grind)
    | exact resolve eq15 eq24450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24450
  have eq88411 : ∀ X0 X1 : G, (σ (τ (M.op X0 X0))) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq88201 X0 X1
       have i₂ := eq22586 X0
       grind)
    | exact superpose eq22586 eq88201
    | (have j0 := eq88201 X0 X1
       grind)
    | exact resolve eq88201 eq22586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22586 eq88201
  have eq88439 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq88411 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq88411
    | (have j0 := eq88411 X0 X1
       grind)
    | exact resolve eq88411 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88411
  have eq89088 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq88439 X1 (τ X0)
       grind)
    | exact superpose eq88439 eq19
    | (have j1 := eq88439 X1 (τ X0)
       grind)
    | exact resolve eq19 eq88439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq88439
  have eq327065 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq89088 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq89088
    | exact resolve eq89088 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89088
  have eq327900 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq327065 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq327065
    | (have j0 := eq327065 X0 X1
       grind)
    | exact resolve eq327065 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327065
  have eq759698 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq88275 x y
       grind)
    | exact superpose eq88275 eq16
    | (have j1 := eq88275 x y
       grind)
    | exact resolve eq16 eq88275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88275
  have eq761543 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq759698
       have i₂ := eq327900 x y
       grind)
    | exact superpose eq327900 eq759698
    | (have j1 := eq327900 x y
       grind)
    | (have r₁ := eq759698
       have r₂ := eq327900 x y
       grind)
    | exact resolve eq759698 eq327900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327900 eq759698
  have eq761546 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq761543
  have eq765094 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq761546
       grind)
    | exact superpose eq761546 eq10
    | exact resolve eq10 eq761546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq761546
  have eq765704 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq765094
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq765094
    | exact resolve eq765094 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765094
  have eq765705 : x = (M.op y y) := by grind
  clear eq765704
  have eq765858 : x = (M.op x y) := by
    first
    | (have i₁ := eq116 y
       have i₂ := eq765705
       grind)
    | exact superpose eq765705 eq116
    | exact resolve eq116 eq765705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq765910 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq23008 y
       have i₂ := eq765705
       grind)
    | exact superpose eq765705 eq23008
    | exact resolve eq23008 eq765705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23008 eq765705
  have eq792662 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq765910
       grind)
    | exact superpose eq765910 eq16
    | exact resolve eq16 eq765910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765910
  have eq793134 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq792662
       have i₂ := eq765858
       grind)
    | exact superpose eq765858 eq792662
    | exact resolve eq792662 eq765858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765858 eq792662
  have eq793135 : False := by grind
  exact eq793135

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,X) else if m(X,X) = m(X,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pxy_pxx_pyy_pyx_Equation909 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law909 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0))) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
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
  have eq62 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 : G, (M.op X0 (k (M.op X0 X0) X0)) = X0 := by
    intro X0
    grind
  have eq68 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq9 (k (M.op X0 X0) X0) X0
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq9
    | exact resolve eq9 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq78 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1
       have i₂ := eq62 X0 X1
       grind)
    | exact superpose eq62 eq9
    | exact resolve eq9 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op X2 (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq78 (M.op X0 X1) X2
       have i₂ := eq62 X1 X0
       grind)
    | exact superpose eq62 eq78
    | exact resolve eq78 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq78 X0 (M.op X0 X0)
       have i₂ := eq62 X0 X0
       grind)
    | exact superpose eq62 eq78
    | exact resolve eq78 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq78 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq78 X0 (M.op X0 X0)
       grind)
    | exact superpose eq78 eq78
    | exact resolve eq78 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 (M.op X1 X1)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq89 (M.op X1 X0)
       have i₂ := eq62 X0 X1
       grind)
    | exact superpose eq62 eq89
    | exact resolve eq89 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq88 (M.op X0 X0)
       have i₂ := eq78 X0 (M.op X0 X0)
       grind)
    | exact superpose eq78 eq88
    | exact resolve eq88 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq96 X0
       have i₂ := eq62 X0 X0
       grind)
    | exact superpose eq62 eq96
    | exact resolve eq96 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq111 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq87 (M.op X0 X0) (M.op X0 X0) X1
       have i₂ := eq78 X0 (M.op X0 X0)
       grind)
    | exact superpose eq78 eq87
    | exact resolve eq87 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq111 X0 X1
       have i₂ := eq62 X0 X0
       grind)
    | exact superpose eq62 eq111
    | exact resolve eq111 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq146 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq135 X1 X2
       have i₂ := eq135 X1 X0
       grind)
    | (have i₁ := eq135 X0 X1
       have i₂ := eq135 X0 X0
       grind)
    | exact superpose eq135 eq135
    | exact resolve eq135 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq151 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X2 (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq87 X1 X1 X2
       have i₂ := eq135 X1 X0
       grind)
    | (have i₁ := eq87 X0 X0 X2
       have i₂ := eq135 X0 X0
       grind)
    | exact superpose eq135 eq87
    | exact resolve eq87 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq152 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq78 X1 X1
       have i₂ := eq135 X1 X0
       grind)
    | (have i₁ := eq78 X0 X0
       have i₂ := eq135 X0 X0
       grind)
    | exact superpose eq135 eq78
    | exact resolve eq78 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq156 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 (M.op X0 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq99 X1
       have i₂ := eq135 X1 X0
       grind)
    | (have i₁ := eq99 X0
       have i₂ := eq135 X0 X0
       grind)
    | exact superpose eq135 eq99
    | exact resolve eq99 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq157 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq88 X1
       have i₂ := eq135 X1 X0
       grind)
    | (have i₁ := eq88 X0
       have i₂ := eq135 X0 X0
       grind)
    | exact superpose eq135 eq88
    | exact resolve eq88 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq135
  have eq269 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X0)) = (M.op (M.op X2 (M.op X2 X0)) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq146 X1 X0 (M.op X2 (M.op X2 X0))
       have i₂ := eq156 X2 X0
       grind)
    | exact superpose eq156 eq146
    | exact resolve eq146 eq156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq271 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 (M.op X1 X0)) (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq152 (M.op X1 (M.op X1 X0)) X0
       have i₂ := eq156 X1 X0
       grind)
    | exact superpose eq156 eq152
    | exact resolve eq152 eq156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq305 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op (M.op (M.op X2 X1) (M.op X2 X1)) (M.op X2 (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq157 X2 (M.op X2 X1)
       have i₂ := eq146 X2 X1 X0
       grind)
    | (have i₁ := eq157 X2 (M.op X2 X1)
       have i₂ := eq146 X0 X1 X2
       grind)
    | exact superpose eq146 eq157
    | exact resolve eq157 eq146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq347 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op (M.op X2 (M.op X1 X1)) (M.op X2 (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq305 X0 X1 X2
       have i₂ := eq62 X1 X2
       grind)
    | exact superpose eq62 eq305
    | exact resolve eq305 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305
  have eq391 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X1 (M.op X0 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq151 X1 X2 X1
       have i₂ := eq146 X1 (M.op X1 X2) X0
       grind)
    | (have i₁ := eq151 X1 X2 X1
       have i₂ := eq146 X0 (M.op X1 X2) X1
       grind)
    | exact superpose eq146 eq151
    | exact resolve eq151 eq146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq591 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq625 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X0 X0))) = (M.op (M.op (M.op X1 (M.op X1 X0)) (M.op X0 X0)) (M.op (M.op X1 (M.op X1 X0)) (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq151 X0 (M.op (M.op X1 (M.op X1 X0)) (M.op X0 X0)) X2
       have i₂ := eq271 X0 X1
       grind)
    | exact superpose eq271 eq151
    | exact resolve eq151 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq631 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X0 X0))) = (M.op (M.op X1 (M.op X1 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq625 X0 X1 X2
       have i₂ := eq62 (M.op X0 X0) (M.op X1 (M.op X1 X0))
       grind)
    | exact superpose eq62 eq625
    | exact resolve eq625 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625
  have eq652 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X0 X0))) = (M.op (M.op X1 (M.op X1 X0)) (M.op X0 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq631 X0 X1 X2
       have i₂ := eq62 X0 X0
       grind)
    | exact superpose eq62 eq631
    | exact resolve eq631 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631
  have eq665 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X1 X0)) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq652 X0 X1 x
       have i₂ := eq78 X0 x
       grind)
    | exact superpose eq78 eq652
    | exact resolve eq652 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652
  have eq864 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X2 X1)) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq665 X1 X2
       have i₂ := eq146 X1 X1 X0
       grind)
    | (have i₁ := eq665 X1 X2
       have i₂ := eq146 X0 X1 X1
       grind)
    | exact superpose eq146 eq665
    | exact resolve eq665 eq146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq874 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (k X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq68 (M.op X0 (M.op X0 X0))
       have i₂ := eq665 X0 X0
       grind)
    | exact superpose eq665 eq68
    | exact resolve eq68 eq665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq665
  have eq905 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq874 X0
       have i₂ := eq156 X0 X0
       grind)
    | exact superpose eq156 eq874
    | exact resolve eq874 eq156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156 eq874
  have eq986 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X1 X0)) (M.op X1 (M.op X1 X0))) = (k (M.op X1 (M.op X1 X0)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq905 (M.op X1 (M.op X1 X0))
       have i₂ := eq151 X1 X0 (M.op X1 (M.op X1 X0))
       grind)
    | exact superpose eq151 eq905
    | exact resolve eq905 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151 eq905
  have eq993 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0))) = (k (M.op X1 (M.op X1 X0)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq986 X0 X1
       have i₂ := eq62 (M.op X1 X0) X1
       grind)
    | exact superpose eq62 eq986
    | exact resolve eq986 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq986
  have eq997 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = (k (M.op X1 (M.op X1 X0)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq993 X0 X1
       have i₂ := eq62 X0 X1
       grind)
    | exact superpose eq62 eq993
    | exact resolve eq993 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq993
  have eq999 : ∀ X0 X1 : G, (k (M.op X1 (M.op X1 X0)) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq997 X0 X1
       have i₂ := eq78 X0 X1
       grind)
    | exact superpose eq78 eq997
    | exact resolve eq997 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq997
  have eq1094 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (k (M.op (M.op X0 X0) X0) (M.op (M.op X1 (M.op X1 X0)) (M.op X1 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq999 (M.op X1 (M.op X1 X0)) (M.op X0 X0)
       have i₂ := eq157 X1 X0
       grind)
    | exact superpose eq157 eq999
    | exact resolve eq999 eq157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157
  have eq1127 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (k (M.op (M.op X0 X0) X0) (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1094 X0 X1
       have i₂ := eq62 (M.op X1 X0) X1
       grind)
    | exact superpose eq62 eq1094
    | exact resolve eq1094 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1094
  have eq1141 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (k (M.op (M.op X0 X0) X0) (M.op X1 (M.op X1 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1127 X0 X1
       have i₂ := eq62 X0 X1
       grind)
    | exact superpose eq62 eq1127
    | exact resolve eq1127 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1127
  have eq1152 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (k (M.op (M.op X0 X0) X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1141 X0 X1
       have i₂ := eq78 X0 X1
       grind)
    | exact superpose eq78 eq1141
    | exact resolve eq1141 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1141
  have eq1160 : ∀ X0 X1 : G, (k (M.op X0 X0) X0) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1152 X0 X1
       have i₂ := eq89 X0
       grind)
    | exact superpose eq89 eq1152
    | exact resolve eq1152 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq1152
  have eq4327 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 (M.op X0 X1)) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq152 x X1
       have i₂ := eq269 X1 x X0
       grind)
    | exact superpose eq269 eq152
    | exact resolve eq152 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4677 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X1 X0)) (M.op X0 X0)) = (k (M.op X0 X0) (M.op (M.op (M.op X1 (M.op X1 X0)) (M.op X0 X0)) (M.op (M.op X1 (M.op X1 X0)) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq999 (M.op (M.op X1 (M.op X1 X0)) (M.op X0 X0)) X0
       have i₂ := eq4327 X1 X0
       grind)
    | exact superpose eq4327 eq999
    | exact resolve eq999 eq4327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq999 eq4327
  have eq4682 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X1 X0)) (M.op X0 X0)) = (k (M.op X0 X0) (M.op (M.op X1 (M.op X1 X0)) (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq4677 X0 X1
       have i₂ := eq62 (M.op X0 X0) (M.op X1 (M.op X1 X0))
       grind)
    | exact superpose eq62 eq4677
    | exact resolve eq4677 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4677
  have eq4739 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X1 X0)) (M.op X0 X0)) = (k (M.op X0 X0) (M.op (M.op X1 (M.op X1 X0)) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq4682 X0 X1
       have i₂ := eq62 X0 X0
       grind)
    | exact superpose eq62 eq4682
    | exact resolve eq4682 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4682
  have eq4785 : ∀ X0 X1 : G, (k (M.op X0 X0) X0) = (M.op (M.op X1 (M.op X1 X0)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4739 X0 X1
       have i₂ := eq864 X0 X0 X1
       grind)
    | exact superpose eq864 eq4739
    | exact resolve eq4739 eq864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq864 eq4739
  have eq11308 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq591 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X0)
       have i₂ := eq591 X0 X1
       grind)
    | exact superpose eq591 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq591 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq591 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq591 X1 X1
       grind)
    | exact resolve eq13 eq591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11309 : ∀ X0 X1 : G, (M.op (M.op (σ X0) (σ X0)) (M.op (σ X0) (σ X0))) = (M.op (σ X0) (M.op (σ X1) (σ X1))) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq62 (σ X0) (σ X0)
       have i₂ := eq591 X0 X1
       grind)
    | (have i₁ := eq62 (σ X1) (σ X0)
       have i₂ := eq591 X0 X1
       grind)
    | exact superpose eq591 eq62
    | (have j1 := eq591 X0 X1
       grind)
    | exact resolve eq62 eq591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591
  have eq11344 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq11308 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11308
  have eq11345 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq11344 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11344
  have eq11357 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ X0) (σ X0))) = (M.op (σ X0) (M.op (σ X1) (σ X1))) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11309 X0 X1
       have i₂ := eq62 (σ X0) (σ X0)
       grind)
    | exact superpose eq62 eq11309
    | (have j0 := eq11309 X0 X1
       grind)
    | exact resolve eq11309 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11309
  have eq11358 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11345 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq11345
    | (have j0 := eq11345 X0 X1
       grind)
    | exact resolve eq11345 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11345
  have eq22959 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq11358 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11358
  have eq25563 : ∀ X0 X1 : G, (M.op (σ X1) (σ X1)) = (M.op (σ X1) (M.op (σ X0) (M.op (σ X0) (M.op (σ X0) (σ X0))))) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq391 (σ X0) (σ X1) (σ X1)
       have i₂ := eq11357 X0 X1
       grind)
    | (have i₁ := eq391 (σ X0) (σ X0) (σ X0)
       have i₂ := eq11357 X0 X1
       grind)
    | exact superpose eq11357 eq391
    | (have j1 := eq11357 X0 X1
       grind)
    | exact resolve eq391 eq11357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391 eq11357
  have eq25692 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq25563 X0 X1
       have i₂ := eq78 (σ X0) (σ X0)
       grind)
    | exact superpose eq78 eq25563
    | (have j0 := eq25563 X0 X1
       grind)
    | exact resolve eq25563 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25563
  have eq25887 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq25692 X0 X1
       have j1 := eq22959 X0 X1
       grind)
    | (have r₁ := eq25692 X0 X1
       have r₂ := eq22959 X0 X1
       grind)
    | (have r₁ := eq25692 X0 X0
       have r₂ := eq22959 X0 X0
       grind)
    | exact resolve eq25692 eq22959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22959 eq25692
  have eq25972 : ∀ X0 X2 : G, (σ X2) = (M.op (σ X0) (σ X0)) ∨ (σ (k X2 X0)) = (M.op (σ X0) (σ X2)) := by
    intro X0 X2
    first
    | (have j0 := eq25887 X2 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25887
  have eq26010 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq25972 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25972
  have eq26024 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq26010 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26010
  have eq26247 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq26024 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26024
  have eq26281 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq26247 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26247
  have eq26313 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq26281 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26281
  have eq26620 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq26313 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26313
  have eq26665 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq26620 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26620
  have eq26672 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq26665 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26665
  have eq26916 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq26672 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26672
  have eq27060 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq26916 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26916
  have eq27156 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq27060 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27060
  have eq27407 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq27156 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27156
  have eq27557 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq27407 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27407
  have eq27633 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq27557 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27557
  have eq27643 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq27633 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27633
  have eq35561 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X0 X1)) = (M.op (M.op X3 (M.op X3 (M.op X0 (M.op X2 (M.op X2 X1))))) (M.op (M.op X0 (M.op X2 (M.op X2 X1))) (M.op X0 (M.op X2 (M.op X2 X1))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq269 (M.op X0 (M.op X2 (M.op X2 X1))) (M.op X0 (M.op X1 X1)) X3
       have i₂ := eq347 X2 X1 X0
       grind)
    | exact superpose eq347 eq269
    | exact resolve eq269 eq347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269 eq347
  have eq35653 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X0 X1)) = (k (M.op (M.op X0 (M.op X2 (M.op X2 X1))) (M.op X0 (M.op X2 (M.op X2 X1)))) (M.op X0 (M.op X2 (M.op X2 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq35561 X0 X1 X2 x
       have i₂ := eq4785 (M.op X0 (M.op X2 (M.op X2 X1))) x
       grind)
    | exact superpose eq4785 eq35561
    | exact resolve eq35561 eq4785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4785 eq35561
  have eq35914 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X0 X1)) = (k (M.op X0 (M.op (M.op X2 (M.op X2 X1)) (M.op X2 (M.op X2 X1)))) (M.op X0 (M.op X2 (M.op X2 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq35653 X0 X1 X2
       have i₂ := eq62 (M.op X2 (M.op X2 X1)) X0
       grind)
    | exact superpose eq62 eq35653
    | exact resolve eq35653 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35653
  have eq36114 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X0 X1)) = (k (M.op X0 (M.op X2 (M.op (M.op X2 X1) (M.op X2 X1)))) (M.op X0 (M.op X2 (M.op X2 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq35914 X0 X1 X2
       have i₂ := eq62 (M.op X2 X1) X2
       grind)
    | exact superpose eq62 eq35914
    | exact resolve eq35914 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35914
  have eq36265 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X0 X1)) = (k (M.op X0 (M.op X2 (M.op X2 (M.op X1 X1)))) (M.op X0 (M.op X2 (M.op X2 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq36114 X0 X1 X2
       have i₂ := eq62 X1 X2
       grind)
    | exact superpose eq62 eq36114
    | exact resolve eq36114 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq36114
  have eq36351 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X0 X1)) = (k (M.op X0 X1) (M.op X0 (M.op X2 (M.op X2 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq36265 X0 X1 X2
       have i₂ := eq78 X1 X2
       grind)
    | exact superpose eq78 eq36265
    | exact resolve eq36265 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq36265
  have eq36382 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (k (M.op X0 X1) (M.op X0 (M.op X2 (M.op X2 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq36351 X0 X1 X2
       have i₂ := eq92 X0 X1
       grind)
    | exact superpose eq92 eq36351
    | exact resolve eq36351 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq36351
  have eq43486 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq27643 (τ X0) (τ X1)
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq27643
    | (have j0 := eq27643 (τ X0) (τ X1)
       grind)
    | exact resolve eq27643 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq43532 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq43486 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq43486
    | (have j0 := eq43486 X0 X1
       grind)
    | exact resolve eq43486 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43486
  have eq43550 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq43532 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq43532
    | (have j0 := eq43532 X0 X1
       grind)
    | exact resolve eq43532 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43532
  have eq43556 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq43550 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq43550
    | (have j0 := eq43550 X0 X1
       grind)
    | exact resolve eq43550 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43550
  have eq43561 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq43556 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq43556
    | (have j0 := eq43556 X0 X1
       grind)
    | exact resolve eq43556 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43556
  have eq43566 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq43561 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq43561
    | (have j0 := eq43561 X0 X1
       grind)
    | exact resolve eq43561 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43561
  have eq43582 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq27643 X1 X0
       have i₂ := eq43566 X1 X0
       grind)
    | exact superpose eq43566 eq27643
    | (have j0 := eq27643 X1 X0
       have j1 := eq43566 (σ X1) (σ X0)
       grind)
    | exact resolve eq27643 eq43566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq205709 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq43582 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43582
  have eq206259 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq205709 x y
       grind)
    | exact superpose eq205709 eq16
    | (have j1 := eq205709 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq205709 x y
       grind)
    | exact resolve eq16 eq205709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205709
  have eq206562 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq206259
  have eq206929 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (σ y) (M.op (σ x) (M.op X0 (M.op X0 (σ x))))) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq36382 (σ x) (σ x) x
       have i₂ := eq206562
       grind)
    | exact superpose eq206562 eq36382
    | exact resolve eq36382 eq206562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206562
  have eq207031 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq206929 x
       have i₂ := eq152 x (σ x)
       grind)
    | exact superpose eq152 eq206929
    | exact resolve eq206929 eq152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206929
  have eq207149 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq207031
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq207031
    | exact resolve eq207031 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207031
  have eq207234 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq43566 eq207149
    | (have j1 := eq43566 y x
       grind)
    | exact resolve eq207149 eq43566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43566 eq207149
  have eq207248 : y = (M.op x x) := by
    first
    | (have r₁ := eq207234
       have r₂ := eq16
       grind)
    | exact resolve eq207234 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207234
  have eq207447 : ∀ X0 : G, (M.op x y) = (k y (M.op x (M.op X0 (M.op X0 x)))) := by
    intro X0
    first
    | (have i₁ := eq36382 x x x
       have i₂ := eq207248
       grind)
    | exact superpose eq207248 eq36382
    | exact resolve eq36382 eq207248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36382 eq207248
  have eq207537 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq207447 x
       have i₂ := eq152 x x
       grind)
    | exact superpose eq152 eq207447
    | exact resolve eq207447 eq152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq207447
  have eq210206 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq27643 y x
       have i₂ := eq207537
       grind)
    | exact superpose eq207537 eq27643
    | (have j0 := eq27643 y x
       grind)
    | exact resolve eq27643 eq207537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27643
  have eq210207 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq210206
       have r₂ := eq16
       grind)
    | exact resolve eq210206 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210206
  have eq211245 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq1160 (σ x) (σ x)
       have i₂ := eq210207
       grind)
    | exact superpose eq210207 eq1160
    | exact resolve eq1160 eq210207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1160 eq210207
  have eq211436 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq211245
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq211245
    | exact resolve eq211245 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211245
  have eq211550 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq211436
       have i₂ := eq207537
       grind)
    | exact superpose eq207537 eq211436
    | exact resolve eq211436 eq207537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207537 eq211436
  have eq211616 : False := by grind
  exact eq211616

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = m(X,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pxy_pyx_pyy_pyx_Equation909 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law909 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0))) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq61 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1
       have i₂ := eq61 X0 X1
       grind)
    | exact superpose eq61 eq9
    | exact resolve eq9 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op X2 (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 (M.op X0 X1) X2
       have i₂ := eq61 X1 X0
       grind)
    | exact superpose eq61 eq62
    | exact resolve eq62 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq67 (M.op X0 X0) (M.op X0 X0) X1
       have i₂ := eq62 X0 (M.op X0 X0)
       grind)
    | exact superpose eq62 eq67
    | exact resolve eq67 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq91 X0 X1
       have i₂ := eq61 X0 X0
       grind)
    | exact superpose eq61 eq91
    | exact resolve eq91 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq126 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq115 X1 X2
       have i₂ := eq115 X1 X0
       grind)
    | (have i₁ := eq115 X0 X1
       have i₂ := eq115 X0 X0
       grind)
    | exact superpose eq115 eq115
    | exact resolve eq115 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X2 (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq67 X1 X1 X2
       have i₂ := eq115 X1 X0
       grind)
    | (have i₁ := eq67 X0 X0 X2
       have i₂ := eq115 X0 X0
       grind)
    | exact superpose eq115 eq67
    | exact resolve eq67 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq371 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X1 (M.op X0 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq131 X1 X2 X1
       have i₂ := eq126 X1 (M.op X1 X2) X0
       grind)
    | (have i₁ := eq131 X1 X2 X1
       have i₂ := eq126 X0 (M.op X1 X2) X1
       grind)
    | exact superpose eq126 eq131
    | exact resolve eq131 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq743 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq747 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq743 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq743 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq743 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743
  have eq795 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq747 (σ X0)
       grind)
    | exact superpose eq747 eq15
    | exact resolve eq15 eq747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq799 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq747 (τ X0)
       grind)
    | exact superpose eq747 eq18
    | exact resolve eq18 eq747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq802 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq799 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq799
    | exact resolve eq799 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq799
  have eq806 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq795 X0
       have i₂ := eq747 X0
       grind)
    | exact superpose eq747 eq795
    | exact resolve eq795 eq747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq795
  have eq810 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq802 X0
       have i₂ := eq747 X0
       grind)
    | exact superpose eq747 eq802
    | exact resolve eq802 eq747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747 eq802
  have eq820 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (M.op X1 (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq62 (σ X0) X1
       have i₂ := eq806 X0
       grind)
    | exact superpose eq806 eq62
    | exact resolve eq62 eq806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq851 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq810 X0
       grind)
    | exact superpose eq810 eq10
    | exact resolve eq10 eq810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq810
  have eq864 : ∀ X0 X1 : G, (τ X0) = (M.op X1 (M.op X1 (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq62 (τ X0) X1
       have i₂ := eq851 X0
       grind)
    | exact superpose eq851 eq62
    | exact resolve eq62 eq851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq898 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (σ X0))) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq67 (σ (M.op X0 X0)) (σ (M.op X0 X0)) X1
       have i₂ := eq820 X0 (σ (M.op X0 X0))
       grind)
    | exact superpose eq820 eq67
    | exact resolve eq67 eq820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq930 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (σ X0))) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq898 X0 X1
       have i₂ := eq806 (M.op X0 X0)
       grind)
    | exact superpose eq806 eq898
    | exact resolve eq898 eq806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq898
  have eq948 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (σ X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq930 X0 X1
       have i₂ := eq61 X0 X0
       grind)
    | exact superpose eq61 eq930
    | exact resolve eq930 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq930
  have eq962 : ∀ X0 X1 X2 X3 : G, (τ X2) = (M.op X3 (M.op X3 (τ (M.op X0 (M.op X0 (M.op X1 (M.op X1 X2))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq864 X2 X3
       have i₂ := eq131 X1 X2 X0
       grind)
    | exact superpose eq131 eq864
    | exact resolve eq864 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq978 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (τ X0))) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq131 x (τ (M.op X0 X0)) X1
       have i₂ := eq864 X0 x
       grind)
    | exact superpose eq864 eq131
    | exact resolve eq131 eq864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq864
  have eq1003 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (τ X0))) = (τ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq978 X0 X1
       have i₂ := eq851 (M.op X0 X0)
       grind)
    | exact superpose eq851 eq978
    | exact resolve eq978 eq851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851 eq978
  have eq1021 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (τ X0))) = (τ (M.op X0 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1003 X0 X1
       have i₂ := eq61 X0 X0
       grind)
    | exact superpose eq61 eq1003
    | exact resolve eq1003 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq1003
  have eq1882 : ∀ X0 X1 X2 : G, (σ (M.op X0 (M.op X0 X1))) = (M.op X2 (M.op X2 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq948 X1 X2
       have i₂ := eq126 X1 X1 X0
       grind)
    | (have i₁ := eq948 X1 X2
       have i₂ := eq126 X0 X1 X1
       grind)
    | exact superpose eq126 eq948
    | exact resolve eq948 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq1921 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (τ (M.op X0 (M.op X0 (σ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 (M.op X1 X1))
       have i₂ := eq948 X1 X0
       grind)
    | exact superpose eq948 eq10
    | exact resolve eq10 eq948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq948
  have eq2149 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (σ (M.op X0 (M.op X0 (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X1 (M.op X1 X1))
       have i₂ := eq1021 X1 X0
       grind)
    | exact superpose eq1021 eq11
    | exact resolve eq11 eq1021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1021
  have eq2442 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X1 (τ (M.op X0 (M.op X0 (σ (M.op X1 X2)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq371 (M.op X1 X2) X1 X2
       have i₂ := eq1921 X0 (M.op X1 X2)
       grind)
    | exact superpose eq1921 eq371
    | exact resolve eq371 eq1921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1921
  have eq3087 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X1 (σ (M.op X0 (M.op X0 (τ (M.op X1 X2)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq371 (M.op X1 X2) X1 X2
       have i₂ := eq2149 X0 (M.op X1 X2)
       grind)
    | exact superpose eq2149 eq371
    | exact resolve eq371 eq2149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371 eq2149
  have eq3635 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) := by
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
  have eq4157 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq3635 (σ X1) (σ X0)
       grind)
    | exact superpose eq3635 eq15
    | (have j1 := eq3635 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq3635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4166 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4157 X0 X1
       have i₂ := eq806 X1
       grind)
    | exact superpose eq806 eq4157
    | (have j0 := eq4157 X0 X1
       grind)
    | exact resolve eq4157 eq806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4157
  have eq4809 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4166 X0 X1
       have i₂ := eq3635 X1 X0
       grind)
    | exact superpose eq3635 eq4166
    | (have j0 := eq4166 X0 X1
       have j1 := eq3635 X1 X0
       grind)
    | exact resolve eq4166 eq3635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3635 eq4166
  have eq61793 : ∀ X0 X1 : G, (σ (M.op X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op X0 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq4809 X1 X0
       grind)
    | exact superpose eq4809 eq10
    | (have j1 := eq4809 X1 X0
       grind)
    | exact resolve eq10 eq4809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4809
  have eq281461 : ∀ X0 X1 X2 X3 : G, (τ (σ X1)) = (M.op X2 (M.op X2 (τ (M.op X3 (M.op X3 (σ (M.op X0 (M.op X0 X1)))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq962 X3 x (σ X1) X2
       have i₂ := eq1882 X0 X1 x
       grind)
    | exact superpose eq1882 eq962
    | exact resolve eq962 eq1882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq962 eq1882
  have eq282318 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 (τ (M.op X3 (M.op X3 (σ (M.op X0 (M.op X0 X1)))))))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq281461 X0 X1 X2 X3
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq281461
    | exact resolve eq281461 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281461
  have eq634743 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op y y) = (τ (M.op (σ y) (σ x))) ∨ (M.op y x) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq61793 y x
       grind)
    | exact superpose eq61793 eq16
    | (have j1 := eq61793 y x
       grind)
    | (have r₁ := eq16
       have r₂ := eq61793 y x
       grind)
    | exact resolve eq16 eq61793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61793
  have eq635041 : (M.op y y) = (τ (M.op (σ y) (σ x))) ∨ (M.op y x) = (M.op y y) := by grind
  clear eq634743
  have eq636066 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ y) (σ (M.op X0 (M.op X0 (M.op y y))))) ∨ (M.op y x) = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq3087 X0 (σ y) (σ x)
       have i₂ := eq635041
       grind)
    | exact superpose eq635041 eq3087
    | exact resolve eq3087 eq635041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3087 eq635041
  have eq636260 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op y x) = (M.op y y) := by
    first
    | (have i₁ := eq636066 x
       have i₂ := eq62 y x
       grind)
    | exact superpose eq62 eq636066
    | exact resolve eq636066 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq636066
  have eq636334 : (σ (M.op y y)) = (M.op (σ x) (σ x)) ∨ (M.op y x) = (M.op y y) := by
    first
    | (have i₁ := eq636260
       have i₂ := eq806 y
       grind)
    | exact superpose eq806 eq636260
    | exact resolve eq636260 eq806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636260
  have eq636382 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op y x) = (M.op y y) := by
    first
    | (have i₁ := eq636334
       have i₂ := eq806 x
       grind)
    | exact superpose eq806 eq636334
    | exact resolve eq636334 eq806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636334
  have eq636460 : ∀ X0 : G, (M.op y y) = (M.op y (τ (M.op X0 (M.op X0 (σ (M.op x x)))))) ∨ (M.op y x) = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq2442 X0 y y
       have i₂ := eq636382
       grind)
    | exact superpose eq636382 eq2442
    | exact resolve eq2442 eq636382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2442 eq636382
  have eq636844 : (M.op y y) = (M.op y (τ (σ x))) ∨ (M.op y x) = (M.op y y) := by
    first
    | (have i₁ := eq636460 x
       have i₂ := eq820 x x
       grind)
    | exact superpose eq820 eq636460
    | exact resolve eq636460 eq820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq820 eq636460
  have eq636943 : (M.op y x) = (M.op y y) ∨ (M.op y x) = (M.op y y) := by
    first
    | (have i₁ := eq636844
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq636844
    | exact resolve eq636844 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636844
  have eq636944 : (M.op y x) = (M.op y y) := by grind
  clear eq636943
  have eq637367 : ∀ X0 X1 : G, y = (M.op X0 (M.op X0 (τ (M.op X1 (M.op X1 (σ (M.op y (M.op y x)))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq282318 y y X0 X1
       have i₂ := eq636944
       grind)
    | exact superpose eq636944 eq282318
    | exact resolve eq282318 eq636944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636944
  have eq637392 : x = y := by
    first
    | (have i₁ := eq637367 x x
       have i₂ := eq282318 y x x x
       grind)
    | exact superpose eq282318 eq637367
    | exact resolve eq637367 eq282318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282318 eq637367
  have eq637540 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq637392
       grind)
    | exact superpose eq637392 eq16
    | exact resolve eq16 eq637392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637392
  have eq637544 : False := by grind
  exact eq637544

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pyx_pxy_pyx_Equation909 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law909 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0))) = X0 := by
    intro X0 X1
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
  have eq51 : y = (M.op x (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : (σ y) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : (M.op (M.op x y) (M.op x y)) = (M.op x (M.op y y)) := by
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
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
    | (have r₁ := eq11 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       have r₂ := eq13 X0 (M.op X0 X0)
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ y) X0) := by
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
  have eq72 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq73 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq80 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq66 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq66
    | (have j0 := eq66 (σ X0) (σ X1)
       grind)
    | exact resolve eq66 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq37 eq66
    | (have j0 := eq66 (σ y) (σ X0)
       grind)
    | exact resolve eq66 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq87 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq66 y x
       grind)
    | exact superpose eq66 eq72
    | (have j1 := eq66 y x
       grind)
    | exact resolve eq72 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq87
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq87
    | exact resolve eq87 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq93
    | exact resolve eq93 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq95 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq66 y y
       grind)
    | exact superpose eq66 eq73
    | (have j1 := eq66 y y
       grind)
    | exact resolve eq73 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq16
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq329 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op (M.op X1 X0) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq330 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) = (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq332 : (M.op y y) = (M.op x (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq335 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq337 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq338 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq339 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) = (k (M.op X0 X1) (M.op X0 (M.op X1 X1))) ∨ (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1
    grind
  have eq340 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 (M.op X1 X1)) ∨ (M.op (M.op X0 X1) X2) = (k X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op X0 X1)
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq13
    | (have j0 := eq13 X2 (M.op X0 X1)
       grind)
    | exact resolve eq13 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq341 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1))) ∨ (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) = (k (M.op X0 X1) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq339 X0 X1
       have i₂ := eq53 (M.op X1 X1) X0
       grind)
    | exact superpose eq53 eq339
    | (have j0 := eq339 X0 X1
       grind)
    | exact resolve eq339 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339
  have eq342 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq338 X0 X1
       have i₂ := eq53 (M.op X1 X1) X0
       grind)
    | exact superpose eq53 eq338
    | exact resolve eq338 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq344 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq335
       have i₂ := eq53 sF4 sF4
       grind)
    | exact superpose eq53 eq335
    | exact resolve eq335 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335
  have eq346 : (M.op y y) = (M.op x (M.op (M.op x y) (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq332
       have i₂ := eq53 sF0 sF0
       grind)
    | exact superpose eq53 eq332
    | exact resolve eq332 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332
  have eq347 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) = (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq330 X0 X1
       have i₂ := eq53 (M.op X1 X1) X0
       grind)
    | exact superpose eq53 eq330
    | exact resolve eq330 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330
  have eq348 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X0) (M.op (M.op X1 X0) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq329 X0 X1
       have i₂ := eq53 (M.op X1 X0) (M.op X1 X0)
       grind)
    | exact superpose eq53 eq329
    | exact resolve eq329 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329
  have eq349 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op X1 (M.op X1 X1))) ∨ (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) = (k (M.op X0 X1) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq341 X0 X1
       have i₂ := eq53 X1 X1
       grind)
    | exact superpose eq53 eq341
    | (have j0 := eq341 X0 X1
       grind)
    | exact resolve eq341 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341
  have eq350 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 (M.op X1 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq342 X0 X1
       have i₂ := eq53 X1 X1
       grind)
    | exact superpose eq53 eq342
    | exact resolve eq342 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342
  have eq353 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) = (M.op X0 (M.op X1 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq347 X0 X1
       have i₂ := eq53 X1 X1
       grind)
    | exact superpose eq53 eq347
    | exact resolve eq347 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347
  have eq354 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq348 X0 X1
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq348
    | exact resolve eq348 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348
  have eq355 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op X2 (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq337 X2 (M.op X0 X1)
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq337
    | exact resolve eq337 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq356 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq337 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq337 (M.op X0 X0) X0
       grind)
    | exact superpose eq337 eq337
    | exact resolve eq337 eq337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq438 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (M.op (σ (k X0 X1)) (σ (k X0 X1)))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq80 X0 X1
       grind)
    | exact superpose eq80 eq14
    | (have j1 := eq80 X0 X1
       grind)
    | exact resolve eq14 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq625 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq94 eq66
    | (have j0 := eq66 (σ y) (σ x)
       grind)
    | exact resolve eq66 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq626 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq625
    | exact resolve eq625 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625
  have eq629 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq626
       have r₂ := eq28
       grind)
    | exact resolve eq626 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626
  have eq634 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq629 eq356
    | exact resolve eq356 eq629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629
  have eq638 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq634
    | exact resolve eq634 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634
  have eq639 : (M.op (M.op x y) (M.op x y)) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq54
       have i₂ := eq638
       grind)
    | exact superpose eq638 eq54
    | exact resolve eq54 eq638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq643 : ∀ X0 : G, y = (M.op X0 (M.op X0 x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq337 X0 y
       have i₂ := eq638
       grind)
    | exact superpose eq638 eq337
    | exact resolve eq337 eq638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq647 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) := by
    first
    | exact superpose eq344 eq53
    | exact resolve eq53 eq344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq650 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) := by
    first
    | (have i₁ := eq647
       have i₂ := eq53 (M.op sF4 sF4) sF4
       grind)
    | exact superpose eq53 eq647
    | exact resolve eq647 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647
  have eq651 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq650
       have i₂ := eq14 sF4 sF4
       grind)
    | exact superpose eq14 eq650
    | exact resolve eq650 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650
  have eq652 : (M.op (σ y) (M.op (σ y) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq651
       have i₂ := eq53 sF3 sF3
       grind)
    | exact superpose eq53 eq651
    | exact resolve eq651 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651
  have eq665 : (M.op (M.op y y) (M.op y y)) = (M.op x (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) (M.op (M.op x y) (M.op (M.op x y) (M.op x y))))) := by
    first
    | exact superpose eq346 eq53
    | exact resolve eq53 eq346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346
  have eq668 : (M.op (M.op y y) (M.op y y)) = (M.op x (M.op (M.op x y) (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))))) := by
    first
    | (have i₁ := eq665
       have i₂ := eq53 (M.op sF0 sF0) sF0
       grind)
    | exact superpose eq53 eq665
    | exact resolve eq665 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665
  have eq669 : (M.op x (M.op x y)) = (M.op (M.op y y) (M.op y y)) := by
    first
    | (have i₁ := eq668
       have i₂ := eq14 sF0 sF0
       grind)
    | exact superpose eq14 eq668
    | exact resolve eq668 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668
  have eq670 : (M.op x (M.op x y)) = (M.op y (M.op y y)) := by
    first
    | (have i₁ := eq669
       have i₂ := eq53 y y
       grind)
    | exact superpose eq53 eq669
    | exact resolve eq669 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669
  have eq674 : (M.op x y) = (M.op (M.op x y) (M.op (M.op x x) (M.op x x))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq639 eq14
    | exact resolve eq14 eq639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq681 : (M.op x y) = (M.op (M.op x y) (M.op x (M.op x x))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq674
       have i₂ := eq53 x x
       grind)
    | exact superpose eq53 eq674
    | exact resolve eq674 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674
  have eq737 : ∀ X0 : G, (M.op X0 (M.op y y)) = (M.op X0 x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14 (M.op X0 x) X0
       have i₂ := eq643 X0
       grind)
    | exact superpose eq643 eq14
    | exact resolve eq14 eq643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1028 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq681
       have i₂ := eq643 x
       grind)
    | exact superpose eq643 eq681
    | exact resolve eq681 eq643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643
  have eq1029 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op (M.op x (M.op x x)) (M.op x (M.op x x)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq681 eq53
    | exact resolve eq53 eq681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681
  have eq1031 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1028
  have eq1032 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x (M.op (M.op x x) (M.op x x)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1029
       have i₂ := eq53 (M.op x x) x
       grind)
    | exact superpose eq53 eq1029
    | exact resolve eq1029 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1029
  have eq1033 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1032
       have i₂ := eq14 x x
       grind)
    | exact superpose eq14 eq1032
    | exact resolve eq1032 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032
  have eq1035 : y = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1031 eq14
    | exact resolve eq14 eq1031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1031
  have eq1037 : (M.op x x) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1033 eq639
    | exact resolve eq639 eq1033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1033
  have eq1046 : (M.op x x) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1037
  have eq1099 : (M.op y y) = (M.op (M.op x y) (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1035 eq53
    | exact resolve eq53 eq1035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1035
  have eq1103 : (M.op x y) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1099
       have i₂ := eq14 sF0 sF0
       grind)
    | exact superpose eq14 eq1099
    | exact resolve eq1099 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1099
  have eq1872 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq737 X0
       have i₂ := eq1103
       grind)
    | exact superpose eq1103 eq737
    | exact resolve eq737 eq1103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq737 eq1103
  have eq1891 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq1872 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1872
  have eq2231 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op (M.op X1 X0) (M.op X1 X0)))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq350 X1 (M.op (M.op X1 X0) (M.op X1 X0))
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq350
    | exact resolve eq350 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2246 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ (k y X0)) (M.op (σ X0) (M.op (σ y) (M.op (σ y) (σ y))))) ∨ (σ X0) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq82 eq350
    | (have j1 := eq82 X0
       grind)
    | exact resolve eq350 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq2286 : (σ y) = (M.op (σ y) (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))))) := by
    first
    | exact superpose eq52 eq350
    | exact resolve eq350 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq2344 : (σ y) = (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq2286
       have i₂ := eq337 (M.op sF4 sF4) sF4
       grind)
    | exact superpose eq337 eq2286
    | exact resolve eq2286 eq337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2286
  have eq2372 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2231 X0 X1
       have i₂ := eq337 (M.op (M.op X1 X0) (M.op X1 X0)) (M.op X1 X0)
       grind)
    | exact superpose eq337 eq2231
    | exact resolve eq2231 eq337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2231
  have eq2492 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X1 (M.op (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0))) (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0))) X1
       have i₂ := eq354 X0 X1
       grind)
    | exact superpose eq354 eq53
    | exact resolve eq53 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2495 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X1 (M.op (M.op X1 X0) (M.op (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq2492 X0 X1
       have i₂ := eq53 (M.op X1 (M.op X0 X0)) (M.op X1 X0)
       grind)
    | exact superpose eq53 eq2492
    | exact resolve eq2492 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2492
  have eq2542 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X1 (M.op (M.op X1 X0) (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq2495 X0 X1
       have i₂ := eq53 (M.op X0 X0) X1
       grind)
    | exact superpose eq53 eq2495
    | exact resolve eq2495 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2495
  have eq2569 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X1 X0) (M.op X1 (M.op X0 (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq2542 X0 X1
       have i₂ := eq53 X0 X0
       grind)
    | exact superpose eq53 eq2542
    | exact resolve eq2542 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2542
  have eq2576 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2569 X0 X1
       have i₂ := eq350 X1 X0
       grind)
    | exact superpose eq350 eq2569
    | exact resolve eq2569 eq350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350 eq2569
  have eq3843 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 (M.op X1 X1))) ≠ (M.op X2 (M.op X0 X1)) ∨ (M.op (M.op X2 (M.op X0 X1)) X3) = (k X3 (M.op X2 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq340 X2 (M.op X0 X1) X3
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq340
    | (have j0 := eq340 X2 (M.op X0 X1) X3
       grind)
    | exact resolve eq340 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340
  have eq3969 : ∀ X0 : G, (σ y) = (M.op (σ (τ X0)) (M.op (k (σ y) X0) (k (σ y) X0))) ∨ (σ (τ X0)) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq438 y (τ X0)
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq438
    | (have j0 := eq438 y (τ X0)
       grind)
    | exact resolve eq438 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq3986 : ∀ X0 X1 : G, (M.op (σ X1) (M.op (M.op (σ (k X0 X1)) (σ (k X0 X1))) (M.op (M.op (σ (k X0 X1)) (σ (k X0 X1))) (M.op (σ (k X0 X1)) (σ (k X0 X1)))))) = (M.op (σ X0) (M.op (σ X1) (M.op (M.op (σ (k X0 X1)) (σ (k X0 X1))) (M.op (σ (k X0 X1)) (σ (k X0 X1)))))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq353 (σ X1) (M.op (σ (k X0 X1)) (σ (k X0 X1)))
       have i₂ := eq438 X0 X1
       grind)
    | exact superpose eq438 eq353
    | (have j1 := eq438 X0 X1
       grind)
    | exact resolve eq353 eq438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438
  have eq3994 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ X1) (M.op (σ (k X0 X1)) (M.op (σ (k X0 X1)) (σ (k X0 X1)))))) = (M.op (σ X1) (M.op (M.op (σ (k X0 X1)) (σ (k X0 X1))) (M.op (σ (k X0 X1)) (M.op (σ (k X0 X1)) (σ (k X0 X1)))))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3986 X0 X1
       have i₂ := eq53 (σ (k X0 X1)) (σ (k X0 X1))
       grind)
    | exact superpose eq53 eq3986
    | (have j0 := eq3986 X0 X1
       grind)
    | exact resolve eq3986 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3986
  have eq4006 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (k (σ y) X0) (k (σ y) X0))) ∨ (σ (τ X0)) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq3969 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3969
    | (have j0 := eq3969 X0
       grind)
    | exact resolve eq3969 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3969
  have eq4032 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ X1) (M.op (σ (k X0 X1)) (M.op (σ (k X0 X1)) (σ (k X0 X1)))))) = (M.op (σ X1) (M.op (σ (k X0 X1)) (M.op (σ (k X0 X1)) (M.op (σ (k X0 X1)) (σ (k X0 X1)))))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3994 X0 X1
       have i₂ := eq353 (σ (k X0 X1)) (σ (k X0 X1))
       grind)
    | exact superpose eq353 eq3994
    | (have j0 := eq3994 X0 X1
       grind)
    | exact resolve eq3994 eq353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3994
  have eq4044 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (k (σ y) X0) (k (σ y) X0))) ∨ (σ (τ X0)) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq4006 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq4006
    | (have j0 := eq4006 X0
       grind)
    | exact resolve eq4006 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4006
  have eq4068 : ∀ X0 X1 : G, (M.op (σ X1) (σ (k X0 X1))) = (M.op (σ X0) (M.op (σ X1) (M.op (σ (k X0 X1)) (M.op (σ (k X0 X1)) (σ (k X0 X1)))))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4032 X0 X1
       have i₂ := eq337 (σ (k X0 X1)) (σ (k X0 X1))
       grind)
    | exact superpose eq337 eq4032
    | (have j0 := eq4032 X0 X1
       grind)
    | exact resolve eq4032 eq337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4032
  have eq4078 : ∀ X0 : G, (σ (τ X0)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op X0 (M.op (k (σ y) X0) (k (σ y) X0))) := by
    intro X0
    first
    | (have i₁ := eq4044 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq4044
    | (have j0 := eq4044 X0
       grind)
    | exact resolve eq4044 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4044
  have eq4105 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (k (σ y) X0) (k (σ y) X0))) ∨ (M.op (σ y) (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq4078 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq4078
    | (have j0 := eq4078 X0
       grind)
    | exact resolve eq4078 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4078
  have eq4960 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op X0 (M.op X1 X1))) = (M.op X0 (M.op X1 (M.op X1 X1))) ∨ (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op X1 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq349 X0 X1
       have i₂ := eq353 X0 X1
       grind)
    | exact superpose eq353 eq349
    | (have j0 := eq349 X0 X1
       grind)
    | exact resolve eq349 eq353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349 eq353
  have eq5199 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op (M.op X1 X0) (M.op X1 X0)))) = (k (M.op X1 (M.op X1 X0)) X0) ∨ (M.op X1 (M.op (M.op X1 X0) (M.op (M.op X1 X0) (M.op X1 X0)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4960 X1 (M.op X1 X0)
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq4960
    | exact resolve eq4960 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4960
  have eq5247 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0)))) = (k (M.op X1 (M.op X1 X0)) X0) ∨ (M.op X1 (M.op (M.op X1 X0) (M.op (M.op X1 X0) (M.op X1 X0)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5199 X0 X1
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq5199
    | (have j0 := eq5199 X0 X1
       grind)
    | exact resolve eq5199 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5199
  have eq5328 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X1 (M.op X1 X0)) X0) ∨ (M.op X1 (M.op (M.op X1 X0) (M.op (M.op X1 X0) (M.op X1 X0)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5247 X0 X1
       have i₂ := eq354 X0 X1
       grind)
    | exact superpose eq354 eq5247
    | (have j0 := eq5247 X0 X1
       grind)
    | exact resolve eq5247 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5247
  have eq5403 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0)))) = X0 ∨ (M.op X0 X0) = (k (M.op X1 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq5328 X0 X1
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq5328
    | (have j0 := eq5328 X0 X1
       grind)
    | exact resolve eq5328 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5328
  have eq5471 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X1 (M.op X1 X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5403 X0 X1
       have i₂ := eq354 X0 X1
       grind)
    | exact superpose eq354 eq5403
    | (have j0 := eq5403 X0 X1
       grind)
    | exact resolve eq5403 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354 eq5403
  have eq6548 : x = (M.op x (M.op (M.op x y) (M.op x x))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1046 eq2372
    | exact resolve eq2372 eq1046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1046
  have eq8563 : ∀ X0 : G, (M.op (M.op x y) (M.op x x)) = (M.op X0 (M.op X0 (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq639 eq2576
    | exact resolve eq2576 eq639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639 eq2576
  have eq18607 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq95
       have i₂ := eq638
       grind)
    | exact superpose eq638 eq95
    | exact resolve eq95 eq638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq638
  have eq18653 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18607
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq18607
    | exact resolve eq18607 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18607
  have eq18658 : (τ (σ x)) = (k y y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18653 eq100
    | exact resolve eq100 eq18653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18667 : x = (k y y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29 eq18658
    | exact resolve eq18658 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18658
  have eq80655 : ∀ X0 : G, x = (M.op x (M.op X0 (M.op X0 (M.op x y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq8563 eq6548
    | exact resolve eq6548 eq8563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6548 eq8563
  have eq80734 : ∀ X0 : G, x = (M.op x (M.op X0 (M.op X0 (M.op x y)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq80655 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80655
  have eq242846 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ (k y X0)) (M.op (σ X0) (M.op (σ x) (M.op (σ x) (σ y))))) ∨ (σ X0) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq652 eq2246
    | (have j0 := eq2246 X0
       grind)
    | exact resolve eq2246 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652 eq2246
  have eq242852 : (σ x) = (M.op (σ x) (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y))))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq242846 y
       have i₂ := eq18667
       grind)
    | exact superpose eq18667 eq242846
    | (have j0 := eq242846 y
       grind)
    | exact resolve eq242846 eq18667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18667 eq242846
  have eq243296 : (σ x) = (M.op (σ x) (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y))))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq242852
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq242852
    | exact resolve eq242852 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242852
  have eq243360 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2344 eq243296
    | exact resolve eq243296 eq2344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2344 eq243296
  have eq243390 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq243360
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq243360
    | exact resolve eq243360 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243360
  have eq243409 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq243390
    | exact resolve eq243390 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243390
  have eq243410 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by grind
  clear eq243409
  have eq243419 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq243410
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq243410
    | exact resolve eq243410 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243410
  have eq243510 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq243419 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq243419
       grind)
    | exact resolve eq13 eq243419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243419
  have eq243553 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq243510 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243510
  have eq246113 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq243553 eq18653
    | exact resolve eq18653 eq243553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18653 eq243553
  have eq246305 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq246113
  have eq246429 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq246305 eq356
    | exact resolve eq356 eq246305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246305
  have eq246487 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq246429
    | exact resolve eq246429 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246429
  have eq246488 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq246487
  have eq290808 : ∀ X0 : G, x ≠ (M.op x (M.op (M.op x y) (M.op x y))) ∨ (M.op (M.op x (M.op (M.op x y) (M.op x y))) X0) = (k X0 (M.op x (M.op (M.op x y) (M.op x y)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq80734 eq3843
    | (have j0 := eq3843 (M.op x y) (M.op x y) x X0
       grind)
    | exact resolve eq3843 eq80734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3843 eq80734
  have eq290959 : ∀ X0 : G, x ≠ y ∨ (M.op (M.op x (M.op (M.op x y) (M.op x y))) X0) = (k X0 (M.op x (M.op (M.op x y) (M.op x y)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq51 eq290808
    | (have j0 := eq290808 X0
       grind)
    | exact resolve eq290808 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290808
  have eq291032 : ∀ X0 : G, (M.op (M.op x (M.op (M.op x y) (M.op x y))) X0) = (k X0 (M.op x (M.op (M.op x y) (M.op x y)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq290959 X0
       grind)
    | (have r₁ := eq290959 X0
       have r₂ := eq246488
       grind)
    | exact resolve eq290959 eq246488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290959
  have eq291095 : ∀ X0 : G, (k X0 y) = (M.op y X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq51 eq291032
    | exact resolve eq291032 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq291032
  have eq291331 : ∀ X0 : G, (M.op y y) = (M.op y (M.op X0 (M.op X0 y))) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq5471 y X0
       have i₂ := eq291095 (M.op X0 (M.op X0 y))
       grind)
    | exact superpose eq291095 eq5471
    | (have j0 := eq5471 y x
       grind)
    | exact resolve eq5471 eq291095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5471 eq291095
  have eq291664 : y = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq291331 x
       have i₂ := eq2372 y x
       grind)
    | exact superpose eq2372 eq291331
    | exact resolve eq291331 eq2372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291331
  have eq291665 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq291664
  have eq297246 : y = (M.op y (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2372 y y
       have i₂ := eq291665
       grind)
    | exact superpose eq291665 eq2372
    | exact resolve eq2372 eq291665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2372 eq291665
  have eq297348 : y = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq297246
       have i₂ := eq670
       grind)
    | exact superpose eq670 eq297246
    | exact resolve eq297246 eq670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670 eq297246
  have eq297860 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq297348 eq1891
    | exact resolve eq1891 eq297348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1891 eq297348
  have eq297937 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq297860
  have eq298992 : ∀ X0 : G, x ≠ y ∨ (k X0 x) = (M.op x X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq297937
       grind)
    | exact superpose eq297937 eq13
    | (have j0 := eq13 X0 x
       grind)
    | exact resolve eq13 eq297937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297937
  have eq299278 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq298992 X0
       grind)
    | (have r₁ := eq298992 X0
       have r₂ := eq246488
       grind)
    | exact resolve eq298992 eq246488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246488 eq298992
  have eq378092 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq299278 y
       grind)
    | exact superpose eq299278 eq72
    | exact resolve eq72 eq299278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq299278
  have eq378545 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq378092
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq378092
    | exact resolve eq378092 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378092
  have eq378599 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq378545
    | exact resolve eq378545 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378545
  have eq379084 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq378599 eq66
    | (have j0 := eq66 (σ y) (σ x)
       grind)
    | exact resolve eq66 eq378599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378599
  have eq379095 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq379084
    | exact resolve eq379084 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379084
  have eq379101 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq379095
       have r₂ := eq28
       grind)
    | exact resolve eq379095 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379095
  have eq379357 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq379101 eq356
    | exact resolve eq356 eq379101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379101
  have eq379430 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq379357
    | exact resolve eq379357 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq379357
  have eq379431 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq379430
  have eq379887 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq379431 eq28
    | exact resolve eq28 eq379431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq379889 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ x)))) := by
    first
    | exact superpose eq379431 eq344
    | exact resolve eq344 eq379431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344 eq379431
  have eq380593 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq379889
       have i₂ := eq337 sF2 sF2
       grind)
    | exact superpose eq337 eq379889
    | exact resolve eq379889 eq337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337 eq379889
  have eq380696 : ∀ X0 : G, (σ x) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
    intro X0
    first
    | exact superpose eq380593 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | exact resolve eq13 eq380593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq419737 : (M.op (σ y) (k (σ y) (σ y))) = (M.op (σ y) (M.op (σ y) (M.op (k (σ y) (σ y)) (M.op (k (σ y) (σ y)) (k (σ y) (σ y)))))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq4068 y y
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq4068
    | (have j0 := eq4068 y y
       grind)
    | exact resolve eq4068 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq4068
  have eq419916 : (M.op (k (σ y) (σ y)) (k (σ y) (σ y))) = (M.op (σ y) (k (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq419737
       have i₂ := eq355 (k sF3 sF3) (k sF3 sF3) (σ y)
       grind)
    | exact superpose eq355 eq419737
    | exact resolve eq419737 eq355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355 eq419737
  have eq420356 : (M.op (k (σ y) (σ y)) (k (σ y) (σ y))) = (M.op (σ y) (k (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq419916
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq419916
    | exact resolve eq419916 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419916
  have eq420761 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (k (σ y) (σ y)) (k (σ y) (σ y))) = (M.op (σ y) (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq420356
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq420356
    | exact resolve eq420356 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq420356
  have eq421098 : (M.op (k (σ y) (σ y)) (k (σ y) (σ y))) = (M.op (σ y) (k (σ y) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq380593 eq420761
    | exact resolve eq420761 eq380593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420761
  have eq639974 : (σ y) = (M.op (σ y) (M.op (σ y) (k (σ y) (σ y)))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq421098 eq4105
    | (have j0 := eq4105 (σ y)
       grind)
    | exact resolve eq4105 eq421098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4105 eq421098
  have eq640051 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (M.op (σ y) (k (σ y) (σ y)))) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq380593 eq639974
    | exact resolve eq639974 eq380593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639974
  have eq640052 : (σ y) = (M.op (σ y) (M.op (σ y) (k (σ y) (σ y)))) ∨ (σ x) = (σ y) := by grind
  clear eq640051
  have eq640085 : (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (M.op (σ y) (k (σ y) (σ y))) (M.op (σ y) (k (σ y) (σ y))))) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq640052 eq53
    | exact resolve eq53 eq640052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq640052
  have eq640132 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq640085
       have i₂ := eq14 (k sF3 sF3) sF3
       grind)
    | exact superpose eq14 eq640085
    | exact resolve eq640085 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640085
  have eq640156 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have j1 := eq380696 (σ y)
       grind)
    | (have r₁ := eq640132
       have r₂ := eq380696 x
       grind)
    | exact resolve eq640132 eq380696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380696 eq640132
  have eq640168 : (σ x) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq380593 eq640156
    | exact resolve eq640156 eq380593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380593 eq640156
  have eq640183 : (τ (σ x)) = (k y y) := by
    first
    | exact superpose eq640168 eq100
    | exact resolve eq100 eq640168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq640168
  have eq640265 : x = (k y y) := by
    first
    | exact superpose eq29 eq640183
    | exact resolve eq640183 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq640183
  have eq640272 : y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq640265
       have i₂ := eq66 y y
       grind)
    | exact superpose eq66 eq640265
    | (have j1 := eq66 y y
       grind)
    | exact resolve eq640265 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq640895 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op y X0) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq640272
       grind)
    | exact superpose eq640272 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq640272
       grind)
    | exact resolve eq13 eq640272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640272
  have eq640956 : ∀ X0 : G, (k X0 y) = (M.op y X0) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq640895 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640895
  have eq643996 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq640265
       have i₂ := eq640956 y
       grind)
    | exact superpose eq640956 eq640265
    | exact resolve eq640265 eq640956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640265 eq640956
  have eq644355 : x = (M.op y y) := by grind
  clear eq643996
  have eq645338 : x = (M.op x y) := by
    first
    | (have i₁ := eq356 y
       have i₂ := eq644355
       grind)
    | exact superpose eq644355 eq356
    | exact resolve eq356 eq644355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356 eq644355
  have eq645421 : x = (M.op x y) := by
    first
    | (have i₁ := eq645338
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq645338
    | exact resolve eq645338 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq645338
  have eq645447 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq645421 eq21
    | exact resolve eq21 eq645421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq645421
  have eq646331 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq645447
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq645447
    | exact resolve eq645447 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq645447
  have eq646335 : False := by grind
  exact eq646335

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pxy_x_pxy_Equation909 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law909 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0))) = X0 := by
    intro X0 X1
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq53 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq9
    | (have j1 := eq53 X1 X0
       grind)
    | exact resolve eq9 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq168 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (k X1 (M.op X1 X0)) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq67 (M.op X1 X0) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq67
    | (have j0 := eq67 (M.op X1 X0) X1
       grind)
    | exact resolve eq67 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq981 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq168 (M.op X0 X0) X1
       have i₂ := eq67 X0 X1
       grind)
    | exact superpose eq67 eq168
    | (have j0 := eq168 X0 X0
       have j1 := eq67 X0 X1
       grind)
    | exact resolve eq168 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq168
  have eq1003 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq981 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq981
  have eq1007 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1003 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq1003 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq1003 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1003
  have eq2762 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq1007 X1 (τ X0)
       grind)
    | exact superpose eq1007 eq17
    | exact resolve eq17 eq1007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq2769 : ∀ X0 X1 : G, (σ (M.op (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2762 X0 X1
       have i₂ := eq1007 (σ X1) X0
       grind)
    | exact superpose eq1007 eq2762
    | exact resolve eq2762 eq1007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1007 eq2762
  have eq2986 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2769 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2769
    | exact resolve eq2769 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2769
  have eq3535 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2986 x y
       grind)
    | exact superpose eq2986 eq16
    | (have r₁ := eq16
       have r₂ := eq2986 x y
       grind)
    | exact resolve eq16 eq2986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2986
  have eq3592 : False := by grind
  exact eq3592
