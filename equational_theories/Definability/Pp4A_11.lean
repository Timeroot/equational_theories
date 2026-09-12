import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,X) else if m(Y,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pxx_pxy_pyx_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq34 : ∀ X0 : G, (M.op (k (M.op X0 X0) X0) (k (M.op X0 X0) X0)) = (k (k (M.op X0 X0) X0) (M.op X0 X0)) := by
    intro X0
    grind
  have eq35 : ∀ X0 : G, (M.op (k (M.op X0 X0) X0) (M.op X0 X0)) = X0 := by
    intro X0
    grind
  have eq37 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X0 X0) X2)) (k (M.op X0 X0) X0)) := by
    intro X0 X1 X2
    grind
  have eq38 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq60 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq64 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op (τ X0) X1) ∨ (M.op (τ X0) (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) ∨ (τ X1) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 X1
       have i₂ := eq14 (τ X1) (τ X0)
       grind)
    | exact superpose eq14 eq38
    | (have j1 := eq14 (τ X1) (τ X0)
       grind)
    | exact resolve eq38 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (k (M.op X0 X0) X0)) := by
    intro X0
    grind
  have eq80 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq25 X0
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 : G, (M.op X0 X0) = (M.op (k (k (M.op X0 X0) X0) (M.op X0 X0)) (k (M.op X0 X0) X0)) := by
    intro X0
    grind
  clear eq35
  have eq123 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X2 X0) (k (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq37 (M.op X0 X1) X2 (M.op X0 X0)
       have i₂ := eq9 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq9 eq37
    | exact resolve eq37 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq170 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X0 X1 X2 (M.op X0 X0)
       have i₂ := eq25 X0
       grind)
    | exact superpose eq25 eq24
    | exact resolve eq24 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op X3 (M.op X0 (M.op X1 X2))) (k (M.op X1 X1) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq37 X1 X3 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))
       have i₂ := eq24 X1 X1 X0 X2
       grind)
    | exact superpose eq24 eq37
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq37
  have eq251 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op X1 (M.op (σ X0) X2)) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X1 X2
       have i₂ := eq60 X0 X0
       grind)
    | exact superpose eq60 eq9
    | (have j1 := eq60 X0 X0
       grind)
    | exact resolve eq9 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq252 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ (k X0 X0))) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq253 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq25 (σ X0)
       have i₂ := eq60 X0 X0
       grind)
    | exact superpose eq60 eq25
    | (have j1 := eq60 X0 X0
       grind)
    | exact resolve eq25 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq263 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq60 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq264 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq263 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263
  have eq270 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq253 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253
  have eq271 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ (k X0 X0))) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq252 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252
  have eq272 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (M.op X1 (M.op (σ X0) X2)) (σ (k X0 X0))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq251 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251
  have eq278 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ (k X0 X0)) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq271 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq271
    | (have j0 := eq271 X0
       grind)
    | exact resolve eq271 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq334 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    grind
  have eq647 : ∀ X0 X1 X2 : G, (τ (k (k (σ X0) X1) X2)) = (k (M.op (τ X1) X0) (τ X2)) ∨ (τ X1) = (M.op (τ X1) X0) ∨ (M.op (τ X1) (τ X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31 (M.op (τ X1) X0) X2
       have i₂ := eq64 X1 X0
       grind)
    | exact superpose eq64 eq31
    | (have j1 := eq64 X1 X0
       grind)
    | exact resolve eq31 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq693 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq78 X0
       have i₂ := eq334 X0
       grind)
    | exact superpose eq334 eq78
    | exact resolve eq78 eq334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq935 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq170 X0 X0 X1
       have i₂ := eq80 X0 X0
       grind)
    | exact superpose eq80 eq170
    | exact resolve eq170 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq170
  have eq1018 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq264 (τ X0)
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq264
    | (have j0 := eq264 (τ X0)
       grind)
    | exact resolve eq264 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264
  have eq1020 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1018 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1018
    | (have j0 := eq1018 X0
       grind)
    | exact resolve eq1018 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1018
  have eq1023 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1020 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1020
    | (have j0 := eq1020 X0
       grind)
    | exact resolve eq1020 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1020
  have eq1029 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1023 (τ X0)
       have i₂ := eq38 X0 X0
       grind)
    | exact superpose eq38 eq1023
    | (have j0 := eq1023 (τ X0)
       grind)
    | exact resolve eq1023 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1023
  have eq1078 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op X3 (M.op X0 (M.op X1 X2))) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq180 X0 X1 X2 X3
       have i₂ := eq334 X1
       grind)
    | exact superpose eq334 eq180
    | exact resolve eq180 eq334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq1254 : ∀ X0 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (k (σ (τ X0)) X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq270 (τ X0)
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq270
    | (have j0 := eq270 (τ X0)
       grind)
    | exact resolve eq270 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq270
  have eq1268 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1254 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1254
    | (have j0 := eq1254 X0
       grind)
    | exact resolve eq1254 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1254
  have eq1272 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1268 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1268
    | (have j0 := eq1268 X0
       grind)
    | exact resolve eq1268 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1268
  have eq1293 : ∀ X0 : G, (M.op X0 X0) = (M.op (k X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq81 X0
       have i₂ := eq334 X0
       grind)
    | exact superpose eq334 eq81
    | exact resolve eq81 eq334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq1797 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (M.op (M.op X1 (M.op X0 X2)) (σ (k (τ X0) (τ X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq272 (τ X0) X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq272
    | exact resolve eq272 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq1843 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (k X0 (σ (τ X0)))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1797 X0 X1 X2
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq1797
    | (have j0 := eq1797 X0 X1 X2
       grind)
    | exact resolve eq1797 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1797
  have eq1846 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1843 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1843
    | (have j0 := eq1843 X0 X1 X2
       grind)
    | exact resolve eq1843 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1843
  have eq1889 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1846 X0 x (M.op (k X0 X0) x)
       have i₂ := eq1078 X0 (k X0 X0) x x
       grind)
    | exact superpose eq1078 eq1846
    | (have j0 := eq1846 X0 x x
       grind)
    | exact resolve eq1846 eq1078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1078 eq1846
  have eq2066 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X2 X0) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq123 X0 X1 X2
       have i₂ := eq334 (M.op X0 X1)
       grind)
    | exact superpose eq334 eq123
    | exact resolve eq123 eq334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq2124 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2066 X0 (k X0 X0) x
       have i₂ := eq1272 X0
       grind)
    | exact superpose eq1272 eq2066
    | (have j1 := eq1272 X0
       grind)
    | exact resolve eq2066 eq1272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1272 eq2066
  have eq2246 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 X0) X1 (k X0 X0)
       have i₂ := eq1889 X0
       grind)
    | exact superpose eq1889 eq9
    | (have j1 := eq1889 X0
       grind)
    | exact resolve eq9 eq1889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1889
  have eq2410 : ∀ X0 : G, (k (k (σ X0) (σ X0)) (σ X0)) = (M.op (k (σ X0) (σ X0)) (k (σ X0) (σ X0))) ∨ (M.op (σ (k X0 X0)) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq34 (σ X0)
       have i₂ := eq278 X0
       grind)
    | exact superpose eq278 eq34
    | (have j1 := eq278 X0
       grind)
    | exact resolve eq34 eq278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278
  have eq2443 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ (k X0 X0))) = (k (σ (k X0 X0)) (σ X0)) ∨ (M.op (σ (k X0 X0)) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq2410 x
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq2410
    | (have j0 := eq2410 X0
       grind)
    | exact resolve eq2410 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2410
  have eq2448 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) ∨ (M.op (σ (k X0 X0)) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq2443 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq2443
    | (have j0 := eq2443 X0
       grind)
    | exact resolve eq2443 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2443
  have eq2449 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have j0 := eq2448 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2448
  have eq2488 : ∀ X0 : G, (k (k (M.op X0 X0) X0) (M.op X0 X0)) = (M.op (k (k (M.op X0 X0) X0) (M.op X0 X0)) (k (M.op X0 X0) X0)) ∨ (k (M.op X0 X0) X0) = (k (k (M.op X0 X0) X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2124 (k (M.op X0 X0) X0) (k (M.op X0 X0) X0)
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq2124
    | exact resolve eq2124 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq2124
  have eq2532 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op (k X0 (M.op X0 X0)) X0) ∨ (k (M.op X0 X0) X0) = (k (k (M.op X0 X0) X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2488 X0
       have i₂ := eq334 X0
       grind)
    | exact superpose eq334 eq2488
    | (have j0 := eq2488 X0
       grind)
    | exact resolve eq2488 eq334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2488
  have eq2548 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (k (M.op X0 X0) X0) = (k (k (M.op X0 X0) X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2532 X0
       have i₂ := eq1293 X0
       grind)
    | exact superpose eq1293 eq2532
    | (have j0 := eq2532 X0
       grind)
    | exact resolve eq2532 eq1293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1293 eq2532
  have eq2556 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq2548 X0
       have i₂ := eq334 X0
       grind)
    | exact superpose eq334 eq2548
    | (have j0 := eq2548 X0
       grind)
    | exact resolve eq2548 eq334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2548
  have eq2973 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (k X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq334 X0
       have i₂ := eq2246 X0 X1
       grind)
    | exact superpose eq2246 eq334
    | (have j1 := eq2246 X0 X1
       grind)
    | exact resolve eq334 eq2246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2246
  have eq6289 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq2556 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2556
  have eq23481 : ∀ X0 : G, (τ X0) = (τ (k (k (σ (τ X0)) X0) X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq334 (τ X0)
       have i₂ := eq647 (τ X0) X0 X0
       grind)
    | exact superpose eq647 eq334
    | (have j1 := eq647 (τ X0) X0 x
       grind)
    | exact resolve eq334 eq647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334 eq647
  have eq23505 : ∀ X0 : G, (τ X0) = (τ (k (k (σ (τ X0)) X0) X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq23481 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23481
  have eq23525 : ∀ X0 : G, (τ X0) = (τ (k (k X0 X0) X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq23505 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq23505
    | (have j0 := eq23505 X0
       grind)
    | exact resolve eq23505 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23505
  have eq28844 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq23525 X0
       have i₂ := eq2973 X0 X1
       grind)
    | exact superpose eq2973 eq23525
    | (have j0 := eq23525 X0
       have j1 := eq2973 X0 X1
       grind)
    | exact resolve eq23525 eq2973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2973 eq23525
  have eq28951 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have j0 := eq28844 X0 X1
       have j1 := eq1029 X0
       grind)
    | (have r₁ := eq28844 X0 X1
       have r₂ := eq1029 X0
       grind)
    | exact resolve eq28844 eq1029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1029 eq28844
  have eq28957 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq28951 X0 x
       have i₂ := eq935 X0 x
       grind)
    | exact superpose eq935 eq28951
    | (have j0 := eq28951 X0 x
       grind)
    | exact resolve eq28951 eq935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28951
  have eq29026 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (k (τ X0) (τ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq6289 (τ X0)
       have i₂ := eq28957 X0
       grind)
    | exact superpose eq28957 eq6289
    | (have j1 := eq28957 X0
       grind)
    | (have r₁ := eq6289 (τ X0)
       have r₂ := eq28957 X0
       grind)
    | exact resolve eq6289 eq28957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6289 eq28957
  have eq29091 : ∀ X0 : G, (τ X0) = (k (τ X0) (τ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq29026 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29026
  have eq29117 : ∀ X0 : G, (τ X0) = (τ (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq29091 X0
       have i₂ := eq38 X0 X0
       grind)
    | exact superpose eq38 eq29091
    | (have j0 := eq29091 X0
       grind)
    | exact resolve eq29091 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29091
  have eq29192 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 (σ X0)
       have i₂ := eq29117 (σ X0)
       grind)
    | exact superpose eq29117 eq31
    | (have j1 := eq29117 (σ X0)
       grind)
    | exact resolve eq31 eq29117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq29117
  have eq29264 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq29192 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq29192
    | (have j0 := eq29192 X0
       grind)
    | exact resolve eq29192 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29192
  have eq29269 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq29264 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq29264
    | (have j0 := eq29264 X0
       grind)
    | exact resolve eq29264 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29264
  have eq30254 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2449 X0
       have i₂ := eq29269 X0
       grind)
    | exact superpose eq29269 eq2449
    | (have j1 := eq29269 X0
       grind)
    | exact resolve eq2449 eq29269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2449 eq29269
  have eq30430 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq30254 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30254
  have eq30609 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq30430 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq30430
    | exact resolve eq30430 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30679 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq693 (σ X0)
       have i₂ := eq30430 X0
       grind)
    | exact superpose eq30430 eq693
    | exact resolve eq693 eq30430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30881 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq30609 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq30609
    | exact resolve eq30609 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30609
  have eq30926 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq30881 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq30881
    | exact resolve eq30881 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30881
  have eq31218 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq38 X0 X0
       have i₂ := eq30926 (τ X0)
       grind)
    | exact superpose eq30926 eq38
    | exact resolve eq38 eq30926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq31246 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq31218 X0
       have i₂ := eq30926 X0
       grind)
    | exact superpose eq30926 eq31218
    | exact resolve eq31218 eq30926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31218
  have eq33454 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq25 (τ X0)
       have i₂ := eq31246 X0
       grind)
    | exact superpose eq31246 eq25
    | exact resolve eq25 eq31246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq37245 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq30679 X0
       have i₂ := eq30926 X0
       grind)
    | exact superpose eq30926 eq30679
    | exact resolve eq30679 eq30926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30679
  have eq2929251 : ∀ X0 X1 : G, (τ X1) = (τ (M.op X0 X0)) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq72 X0 X1
       have i₂ := eq31246 X0
       grind)
    | exact superpose eq31246 eq72
    | (have j0 := eq72 X0 X1
       grind)
    | exact resolve eq72 eq31246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq31246
  have eq2929828 : ∀ X0 X1 : G, (τ X1) = (M.op (τ X1) (τ X0)) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq33454 X1
       have i₂ := eq2929251 X1 X0
       grind)
    | (have i₁ := eq33454 X0
       have i₂ := eq2929251 X0 (M.op X0 X0)
       grind)
    | exact superpose eq2929251 eq33454
    | (have j1 := eq2929251 X1 X0
       grind)
    | exact resolve eq33454 eq2929251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33454 eq2929251
  have eq2930113 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2929828 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2929828
  have eq2931235 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (τ (k X1 (σ X0))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2930113 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2930113
    | exact resolve eq2930113 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2930113
  have eq2933374 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (k (τ X1) X0) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2931235 X0 X1
       have i₂ := eq23 X1 X0
       grind)
    | exact superpose eq23 eq2931235
    | (have j0 := eq2931235 X0 X1
       grind)
    | exact resolve eq2931235 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq2931235
  have eq2935290 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2933374 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2933374
    | exact resolve eq2933374 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2935350 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq2933374 X0 X1
       grind)
    | exact superpose eq2933374 eq18
    | (have j1 := eq2933374 X0 X1
       grind)
    | exact resolve eq18 eq2933374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2933374
  have eq2936385 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2935290 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2935290
    | (have j0 := eq2935290 (σ X0) (σ X1)
       grind)
    | exact resolve eq2935290 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2935290
  have eq2939059 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2935350 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2935350
    | exact resolve eq2935350 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2935350
  have eq2940162 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2939059 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2939059
    | (have j0 := eq2939059 X0 X1
       grind)
    | exact resolve eq2939059 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2939059
  have eq2951221 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2936385 y x
       grind)
    | exact superpose eq2936385 eq16
    | (have j1 := eq2936385 y x
       grind)
    | exact resolve eq16 eq2936385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2936385
  have eq2954875 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2951221
       have i₂ := eq2940162 y x
       grind)
    | exact superpose eq2940162 eq2951221
    | (have j1 := eq2940162 (σ y) (σ x)
       grind)
    | (have r₁ := eq2951221
       have r₂ := eq2940162 y x
       grind)
    | exact resolve eq2951221 eq2940162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2940162 eq2951221
  have eq2954891 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2954875
  have eq2954921 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq935 y x
       have i₂ := eq2954891
       grind)
    | exact superpose eq2954891 eq935
    | exact resolve eq935 eq2954891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2964930 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2954921
       grind)
    | exact superpose eq2954921 eq16
    | exact resolve eq16 eq2954921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2954921
  have eq2969118 : (σ x) ≠ (σ x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2964930
       have i₂ := eq2954891
       grind)
    | exact superpose eq2954891 eq2964930
    | exact resolve eq2964930 eq2954891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2954891 eq2964930
  have eq2969128 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq2969118
  have eq2969242 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq935 (σ y) (σ x)
       have i₂ := eq2969128
       grind)
    | exact superpose eq2969128 eq935
    | exact resolve eq935 eq2969128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq935
  have eq2970257 : (M.op (σ x) (σ y)) = (σ (k y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2969242
       have i₂ := eq30430 y
       grind)
    | exact superpose eq30430 eq2969242
    | exact resolve eq2969242 eq30430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30430 eq2969242
  have eq2970466 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2970257
       have i₂ := eq30926 y
       grind)
    | exact superpose eq30926 eq2970257
    | exact resolve eq2970257 eq30926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30926 eq2970257
  have eq2992227 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2969128
       have i₂ := eq2970466
       grind)
    | exact superpose eq2970466 eq2969128
    | exact resolve eq2969128 eq2970466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2969128 eq2970466
  have eq2993065 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq2992227
  have eq2994202 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq2993065
       grind)
    | exact superpose eq2993065 eq10
    | exact resolve eq10 eq2993065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2993065
  have eq2994768 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2994202
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2994202
    | exact resolve eq2994202 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2994202
  have eq2994769 : x = (M.op y y) := by grind
  clear eq2994768
  have eq2996595 : x = (M.op x y) := by
    first
    | (have i₁ := eq693 y
       have i₂ := eq2994769
       grind)
    | exact superpose eq2994769 eq693
    | exact resolve eq693 eq2994769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693
  have eq2996665 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq37245 y
       have i₂ := eq2994769
       grind)
    | exact superpose eq2994769 eq37245
    | exact resolve eq37245 eq2994769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37245 eq2994769
  have eq3078025 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2996665
       grind)
    | exact superpose eq2996665 eq16
    | exact resolve eq16 eq2996665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2996665
  have eq3079273 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq3078025
       have i₂ := eq2996595
       grind)
    | exact superpose eq2996595 eq3078025
    | exact resolve eq3078025 eq2996595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2996595 eq3078025
  have eq3079274 : False := by grind
  exact eq3079274

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_y_pxx_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq22 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq9 X0 x x
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
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq10
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    grind
  clear eq19
  have eq30 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq29 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq29
    | (have j0 := eq29 X0
       grind)
    | exact resolve eq29 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq32 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    grind
  have eq38 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq10
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq42 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq32 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq32
    | exact resolve eq32 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq43 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq47 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq26
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    grind
  have eq155 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq43 x y
       grind)
    | exact superpose eq43 eq16
    | (have j1 := eq43 x y
       grind)
    | exact resolve eq16 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq387 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq30 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq30
    | exact resolve eq30 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq390 : ∀ X0 : G, (k (σ (τ X0)) X0) = X0 ∨ (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq42 X0
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq42
    | (have j1 := eq30 X0
       grind)
    | exact resolve eq42 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq42
  have eq400 : ∀ X0 : G, (k X0 X0) = X0 ∨ (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq390 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq390
    | (have j0 := eq390 X0
       grind)
    | exact resolve eq390 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390
  have eq401 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ (k X0 X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq387 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq387
    | (have j0 := eq387 X0
       grind)
    | exact resolve eq387 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387
  have eq494 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq22 (M.op X0 X0)
       have i₂ := eq61 X0 X0
       grind)
    | exact superpose eq61 eq22
    | exact resolve eq22 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq496 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    grind
  clear eq61
  have eq700 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq155
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq155
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq155
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq155
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq155 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq701 : x = y ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by grind
  clear eq700
  have eq1023 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq400
  have eq1043 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1023 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1023
  have eq3332 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq38 X0 (M.op (σ X0) (σ X0))
       have i₂ := eq496 (σ X0)
       grind)
    | exact superpose eq496 eq38
    | exact resolve eq38 eq496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq496
  have eq5263 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq1043 X0
       grind)
    | exact superpose eq1043 eq10
    | (have j1 := eq1043 X0
       grind)
    | exact resolve eq10 eq1043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1043
  have eq5754 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq701
       grind)
    | exact superpose eq701 eq16
    | exact resolve eq16 eq701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701
  have eq5989 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq5263 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5263
    | (have j0 := eq5263 (σ X0)
       grind)
    | exact resolve eq5263 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5263
  have eq6052 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq5989 X0
       have i₂ := eq26 (σ X0) X0
       grind)
    | exact superpose eq26 eq5989
    | (have j0 := eq5989 X0
       grind)
    | exact resolve eq5989 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5989
  have eq6057 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq6052 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6052
    | (have j0 := eq6052 X0
       grind)
    | exact resolve eq6052 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6052
  have eq7182 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ X0))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq3332 X0
       have i₂ := eq6057 X0
       grind)
    | exact superpose eq6057 eq3332
    | (have j1 := eq6057 X0
       grind)
    | exact resolve eq3332 eq6057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3332 eq6057
  have eq7217 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq7182 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7182
    | (have j0 := eq7182 X0
       grind)
    | exact resolve eq7182 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7182
  have eq7313 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (τ X0) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq7217 (τ X0)
       have i₂ := eq47 X0 X0
       grind)
    | exact superpose eq47 eq7217
    | exact resolve eq7217 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq7217
  have eq234534 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq110 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq234544 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq234534 X0
       have j1 := eq7313 X0
       grind)
    | (have r₁ := eq234534 X0
       have r₂ := eq7313 X0
       grind)
    | exact resolve eq234534 eq7313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7313 eq234534
  have eq234612 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq234544 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq234544
    | exact resolve eq234544 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234544
  have eq234950 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq234612 X0
       have i₂ := eq26 (σ X0) X0
       grind)
    | exact superpose eq26 eq234612
    | exact resolve eq234612 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq234612
  have eq234997 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq234950 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq234950
    | exact resolve eq234950 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234950
  have eq236514 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq234997 (σ X0)
       grind)
    | exact superpose eq234997 eq15
    | exact resolve eq15 eq234997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq236815 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq236514 X0
       have i₂ := eq234997 X0
       grind)
    | exact superpose eq234997 eq236514
    | exact resolve eq236514 eq234997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236514
  have eq239303 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq494 (σ X0)
       have i₂ := eq236815 X0
       grind)
    | exact superpose eq236815 eq494
    | exact resolve eq494 eq236815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq621180 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq5754
       have r₂ := eq236815 x
       grind)
    | exact resolve eq5754 eq236815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5754
  have eq621181 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq621180
       have i₂ := eq236815 y
       grind)
    | exact superpose eq236815 eq621180
    | exact resolve eq621180 eq236815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621180
  have eq621211 : x = y ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq401 y
       have i₂ := eq621181
       grind)
    | exact superpose eq621181 eq401
    | exact resolve eq401 eq621181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401 eq621181
  have eq621590 : (σ x) = (σ (M.op y y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq621211
       have i₂ := eq234997 y
       grind)
    | exact superpose eq234997 eq621211
    | exact resolve eq621211 eq234997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234997 eq621211
  have eq621591 : x = y ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by grind
  clear eq621590
  have eq621639 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq621591
       grind)
    | exact superpose eq621591 eq16
    | exact resolve eq16 eq621591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621591
  have eq621640 : (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq621639
       have r₂ := eq236815 x
       grind)
    | exact resolve eq621639 eq236815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621639
  have eq621644 : y = (τ (σ x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq621640
       grind)
    | exact superpose eq621640 eq10
    | exact resolve eq10 eq621640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621640
  have eq622600 : x = y ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq621644
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq621644
    | exact resolve eq621644 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621644
  have eq623152 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq622600
       grind)
    | exact superpose eq622600 eq16
    | exact resolve eq16 eq622600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622600
  have eq623153 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq623152
       have r₂ := eq236815 x
       grind)
    | exact resolve eq623152 eq236815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236815 eq623152
  have eq623197 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq239303 y
       have i₂ := eq623153
       grind)
    | exact superpose eq623153 eq239303
    | exact resolve eq239303 eq623153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239303
  have eq623216 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq623153
       grind)
    | exact superpose eq623153 eq10
    | exact resolve eq10 eq623153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623153
  have eq624211 : x = (M.op y y) := by
    first
    | (have i₁ := eq623216
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq623216
    | exact resolve eq623216 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623216
  have eq624960 : x = (M.op x y) := by
    first
    | (have i₁ := eq494 y
       have i₂ := eq624211
       grind)
    | exact superpose eq624211 eq494
    | exact resolve eq494 eq624211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494 eq624211
  have eq660139 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq623197
       grind)
    | exact superpose eq623197 eq16
    | exact resolve eq16 eq623197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623197
  have eq660512 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq660139
       have i₂ := eq624960
       grind)
    | exact superpose eq624960 eq660139
    | exact resolve eq660139 eq624960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624960 eq660139
  have eq660513 : False := by grind
  exact eq660513

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyx_pyx_pxx_pyx_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq32 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X2) = (M.op X2 X2) ∨ (M.op X0 X2) = (k X2 X0) := by
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
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq46 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq48 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X2) = (M.op X2 X2) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq32 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq51 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq46 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq46 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq117 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq640 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq48 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq641 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq640 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640
  have eq646 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq641 X0 X1
       have j1 := eq117 X0 X1
       grind)
    | (have r₁ := eq641 X0 X1
       have r₂ := eq117 X0 X1
       grind)
    | (have r₁ := eq641 X0 X0
       have r₂ := eq117 X0 X0
       grind)
    | exact resolve eq641 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq641
  have eq929 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq646 (σ X1) (σ X0)
       grind)
    | exact superpose eq646 eq15
    | exact resolve eq15 eq646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq932 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq929 X0 X1
       have i₂ := eq646 X1 X0
       grind)
    | exact superpose eq646 eq929
    | exact resolve eq929 eq646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646 eq929
  have eq936 : False := by grind
  exact eq936

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyy_pxy_pxx_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq20 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 X3)) (M.op X0 X0)) = X2 ∨ (M.op X0 X0) = X0 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 X1 X3
       have i₂ := eq14 X2 X0
       grind)
    | (have i₁ := eq9 X1 X1 X2
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X2 X0
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X2 X2) ∨ (M.op X2 X2) = X2 ∨ (M.op X0 X0) = (k X1 X2) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X2
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 (M.op X1 X1) X1
       have r₂ := eq14 X0 (M.op X1 X1)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X2 X2) ∨ (M.op X2 X2) = X2 ∨ (M.op X0 X0) = (k X1 X2) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq40 X0 X1 X2
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq40 X0 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq40 (k X1 X2) X1 X2
       have r₂ := eq12 X0 (k X1 X2)
       grind)
    | (have r₁ := eq40 X1 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq40 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 X3)) (M.op X0 X0)) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq38 X0 X1 X2 X3
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq38 X1 X1 X2 X3
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq38 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq86 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq20 X0
       grind)
    | exact superpose eq20 eq9
    | exact resolve eq9 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1685 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq60 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq1686 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1685 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq1685 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq1685 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1685
  have eq2498 : ∀ X0 X3 : G, (M.op X3 X3) = (M.op X0 (M.op (M.op X3 X3) (M.op X3 X3))) ∨ (M.op X0 X3) = (k X0 X3) := by
    intro X0 X3
    first
    | (have i₁ := eq86 (M.op X3 X3) (M.op x (M.op X0 x))
       have i₂ := eq62 X3 x X0 x
       grind)
    | exact superpose eq62 eq86
    | (have j1 := eq62 X3 x X0 X3
       grind)
    | exact resolve eq86 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq2658 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X3 X3) ∨ (M.op X0 X3) = (k X0 X3) := by
    intro X0 X3
    first
    | (have i₁ := eq2498 X0 X3
       have i₂ := eq86 X3 X3
       grind)
    | exact superpose eq86 eq2498
    | (have j0 := eq2498 X0 X3
       grind)
    | exact resolve eq2498 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq2498
  have eq4633 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1686 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1686
  have eq4635 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq4633 X0 X1
       have j1 := eq2658 X0 X1
       grind)
    | (have r₁ := eq4633 x x
       have r₂ := eq2658 x x
       grind)
    | (have r₁ := eq4633 X0 x
       have r₂ := eq2658 X0 x
       grind)
    | exact resolve eq4633 eq2658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2658 eq4633
  have eq4903 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq4635 (σ X0) (σ X1)
       grind)
    | exact superpose eq4635 eq15
    | exact resolve eq15 eq4635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4914 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4903 X0 X1
       have i₂ := eq4635 X0 X1
       grind)
    | exact superpose eq4635 eq4903
    | exact resolve eq4903 eq4635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4635 eq4903
  have eq4923 : False := by grind
  exact eq4923

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pxy_pyy_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq22 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq29 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X1 : G, (M.op X1 (M.op X1 X1)) = X1 := by
    intro X1
    first
    | (have i₁ := eq9 X1 (M.op x (M.op X1 x)) X1
       have i₂ := eq9 X1 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq9
    | exact resolve eq9 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X2 (M.op (M.op X0 X0) X1)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) X2 X1
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq9
    | exact resolve eq9 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq22
    | exact resolve eq22 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq90 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq40 X0 (M.op X0 X0) X1
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq40
    | exact resolve eq40 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq123 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq120 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq120
    | (have j0 := eq120 (σ X0) (σ X1)
       grind)
    | exact resolve eq120 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq120 (τ X0) X1
       grind)
    | exact superpose eq120 eq17
    | (have j1 := eq120 (τ X0) X1
       grind)
    | exact resolve eq17 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq120
  have eq188 : ∀ X0 X1 : G, (σ X1) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq123 X0 X1
       grind)
    | exact superpose eq123 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq123 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq123 X0 X1
       grind)
    | exact resolve eq13 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq188 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq193 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq192 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq192
    | (have j0 := eq192 X0 X1
       grind)
    | exact resolve eq192 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq268 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X1) = (M.op (M.op X4 (M.op X2 (M.op X1 X0))) (M.op (M.op X3 X1) (M.op X3 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq29 (M.op X1 (M.op X0 X2)) X1 X2 (M.op X0 X0)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq29
    | exact resolve eq29 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq271 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29 X1 X1 X2 (M.op X1 X1)
       have i₂ := eq30 X1
       grind)
    | exact superpose eq30 eq29
    | exact resolve eq29 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq281 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X2 X0) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29 X0 X2 (M.op X0 X1) X1
       have i₂ := eq32 (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq32 eq29
    | exact resolve eq29 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq282 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X2 (M.op X0 X1))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq40 X0 (M.op (M.op X2 (M.op X0 X1)) (M.op X2 (M.op X0 X1))) X3
       have i₂ := eq29 X0 X0 X2 X1
       grind)
    | exact superpose eq29 eq40
    | exact resolve eq40 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq304 : ∀ X1 X2 : G, (M.op X1 X1) = (M.op (M.op X1 X2) X1) := by
    intro X1 X2
    first
    | (have i₁ := eq282 X1 X2 (M.op X1 X2) (M.op x (M.op (M.op X1 X2) x))
       have i₂ := eq9 (M.op X1 X2) x x
       grind)
    | exact superpose eq9 eq282
    | exact resolve eq282 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282
  have eq330 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq304 (M.op X1 X0) (M.op X0 X0)
       have i₂ := eq32 X0 X1
       grind)
    | exact superpose eq32 eq304
    | exact resolve eq304 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq492 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq271 X0 X1 X2
       have i₂ := eq330 X0 X1
       grind)
    | exact superpose eq330 eq271
    | exact resolve eq271 eq330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq532 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X2 X1) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq304 (M.op X0 X1) (M.op X1 (M.op X2 X1))
       have i₂ := eq492 X1 X2 X0
       grind)
    | exact superpose eq492 eq304
    | exact resolve eq304 eq492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq534 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X1)) = (M.op (M.op X2 X1) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq532 X0 X1 X2
       have i₂ := eq330 X1 X0
       grind)
    | exact superpose eq330 eq532
    | exact resolve eq532 eq330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532
  have eq612 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq130 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq130
    | exact resolve eq130 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq638 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq612 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq612
    | (have j0 := eq612 X0 X1
       grind)
    | exact resolve eq612 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612
  have eq974 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq281 X0 X1 X2
       have i₂ := eq534 X0 X1 X0
       grind)
    | exact superpose eq534 eq281
    | exact resolve eq281 eq534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq1077 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X1) = (M.op (M.op X4 (M.op X2 (M.op X1 X0))) (M.op X1 (M.op X3 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq268 X0 X1 X2 X3 X4
       have i₂ := eq330 X1 X3
       grind)
    | exact superpose eq330 eq268
    | exact resolve eq268 eq330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq1385 : ∀ X1 X2 X3 : G, (M.op X3 X2) = (M.op (M.op X2 X1) (M.op X2 (M.op X3 X2))) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq1077 X1 X2 X1 X3 (M.op x X1)
       have i₂ := eq492 X1 X2 x
       grind)
    | exact superpose eq492 eq1077
    | exact resolve eq1077 eq492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1077
  have eq1503 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1385 (M.op X0 X0) X0 X1
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq1385
    | exact resolve eq1385 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1533 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op (M.op X2 X3) (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1385 X3 X2 X1
       have i₂ := eq974 X1 X2 X0
       grind)
    | (have i₁ := eq1385 X1 (M.op X2 X0) X0
       have i₂ := eq974 X0 (M.op X2 X0) X2
       grind)
    | exact superpose eq974 eq1385
    | exact resolve eq1385 eq974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1385
  have eq5336 : ∀ X0 X1 : G, (σ (τ (k X1 X0))) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ (k X1 X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq193 (τ X1) (τ X0)
       have i₂ := eq44 X0 X1
       grind)
    | exact superpose eq44 eq193
    | (have j0 := eq193 X0 (τ X0)
       grind)
    | exact resolve eq193 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq193
  have eq5543 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (τ (k X1 X0))) ∨ (σ (τ (k X1 X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5336 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5336
    | (have j0 := eq5336 X0 X1
       grind)
    | exact resolve eq5336 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5336
  have eq5560 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (σ (τ (k X1 X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5543 X0 X1
       have i₂ := eq11 (k X1 X0)
       grind)
    | exact superpose eq11 eq5543
    | (have j0 := eq5543 X0 X1
       grind)
    | exact resolve eq5543 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5543
  have eq5562 : ∀ X0 X1 : G, (σ (τ (k X1 X0))) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5560 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5560
    | (have j0 := eq5560 X0 X1
       grind)
    | exact resolve eq5560 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5560
  have eq5564 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X1 X0))) ∨ (M.op X0 X0) = (k X1 X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5562 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq5562
    | (have j0 := eq5562 X0 X1
       grind)
    | exact resolve eq5562 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5562
  have eq5565 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5564 X0 X1
       have i₂ := eq11 (k X1 X0)
       grind)
    | exact superpose eq11 eq5564
    | (have j0 := eq5564 X0 X1
       grind)
    | exact resolve eq5564 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5564
  have eq5566 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq5565 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5565
    | (have j0 := eq5565 X0 X1
       grind)
    | exact resolve eq5565 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5565
  have eq5567 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq5566 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq5566 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq5566 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5566
  have eq5694 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq5567 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5567
  have eq5798 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k (M.op X1 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5694 (M.op X1 X0) X1
       have i₂ := eq304 X1 X0
       grind)
    | exact superpose eq304 eq5694
    | (have j0 := eq5694 X1 X1
       grind)
    | (have r₁ := eq5694 (M.op X1 x) X1
       have r₂ := eq304 X1 x
       grind)
    | exact resolve eq5694 eq304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5801 : ∀ X0 X1 X2 : G, (M.op X1 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k (M.op X0 (M.op (M.op X1 X1) X2)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5694 (M.op X0 (M.op (M.op X1 X1) X2)) X1
       have i₂ := eq40 X1 X2 X0
       grind)
    | exact superpose eq40 eq5694
    | (have j0 := eq5694 X1 X1
       grind)
    | (have r₁ := eq5694 (M.op X2 (M.op (M.op X0 X0) X1)) X0
       have r₂ := eq40 X0 X1 X2
       grind)
    | exact resolve eq5694 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq5802 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq5694 (M.op X1 X0) X0
       have i₂ := eq90 X0 X1
       grind)
    | exact superpose eq90 eq5694
    | (have j0 := eq5694 X0 X0
       grind)
    | (have r₁ := eq5694 (M.op X1 X0) X0
       have r₂ := eq90 X0 X1
       grind)
    | exact resolve eq5694 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5694
  have eq5819 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have j0 := eq5802 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5802
  have eq5820 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k (M.op X0 (M.op (M.op X1 X1) X2)) X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq5801 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5801
  have eq5823 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op X1 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq5798 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5798
  have eq6317 : ∀ X1 X2 X3 : G, (M.op (M.op X2 X1) (M.op X2 X1)) = (k (M.op X3 X2) (M.op X2 X1)) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq5823 (M.op (M.op x X3) (M.op X3 X2)) (M.op X2 X1)
       have i₂ := eq1533 x X3 X2 X1
       grind)
    | exact superpose eq1533 eq5823
    | exact resolve eq5823 eq1533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1533 eq5823
  have eq6360 : ∀ X1 X2 X3 : G, (M.op X1 (M.op X2 X1)) = (k (M.op X3 X2) (M.op X2 X1)) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq6317 X1 X2 X3
       have i₂ := eq534 X2 X1 X2
       grind)
    | exact superpose eq534 eq6317
    | exact resolve eq6317 eq534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534 eq6317
  have eq8480 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X1 (M.op (M.op X0 (M.op X0 X0)) X2)) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5820 X0 (M.op X1 X1) X2
       have i₂ := eq974 X1 X1 X1
       grind)
    | exact superpose eq974 eq5820
    | exact resolve eq5820 eq974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974 eq5820
  have eq8554 : ∀ X0 X1 X2 : G, (k (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8480 X1 X1 X2
       have i₂ := eq30 X1
       grind)
    | (have i₁ := eq8480 X0 X1 X2
       have i₂ := eq30 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq30 eq8480
    | exact resolve eq8480 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8480
  have eq9726 : ∀ X0 X1 X2 : G, (k (k (M.op X2 X0) (M.op X0 X1)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8554 X0 X1 X1
       have i₂ := eq6360 X1 X0 X2
       grind)
    | exact superpose eq6360 eq8554
    | exact resolve eq8554 eq6360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6360
  have eq11811 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k (k (M.op X2 (M.op X1 X0)) (M.op X1 X1)) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9726 (M.op X1 X0) X1 X2
       have i₂ := eq304 X1 X0
       grind)
    | exact superpose eq304 eq9726
    | exact resolve eq9726 eq304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304 eq9726
  have eq11931 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k (k (M.op X2 (M.op X1 X0)) (M.op X1 X1)) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11811 X0 X1 X2
       have i₂ := eq330 X0 X1
       grind)
    | exact superpose eq330 eq11811
    | exact resolve eq11811 eq330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330 eq11811
  have eq11977 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq11931 X0 X1 x
       have i₂ := eq8554 X1 x X0
       grind)
    | exact superpose eq8554 eq11931
    | exact resolve eq11931 eq8554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8554 eq11931
  have eq12298 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (k X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11977 (M.op X0 X1) X1
       have i₂ := eq492 X1 X0 X0
       grind)
    | exact superpose eq492 eq11977
    | exact resolve eq11977 eq492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492 eq11977
  have eq12413 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12298 (σ X1) (σ X0)
       have i₂ := eq123 X0 X1
       grind)
    | exact superpose eq123 eq12298
    | (have j1 := eq123 X0 X1
       grind)
    | exact resolve eq12298 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq12298
  have eq12452 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12413 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq12413
    | (have j0 := eq12413 X0 X1
       grind)
    | exact resolve eq12413 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12413
  have eq12453 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq12452 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12452
  have eq12509 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12453 x y
       grind)
    | exact superpose eq12453 eq16
    | exact resolve eq16 eq12453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12453
  have eq12667 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq12509
       have i₂ := eq638 x y
       grind)
    | exact superpose eq638 eq12509
    | (have j1 := eq638 x y
       grind)
    | (have r₁ := eq12509
       have r₂ := eq638 x y
       grind)
    | exact resolve eq12509 eq638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq638
  have eq12668 : y = (M.op y x) := by grind
  clear eq12667
  have eq12688 : (M.op y x) = (M.op x x) := by
    first
    | (have i₁ := eq90 x y
       have i₂ := eq12668
       grind)
    | exact superpose eq12668 eq90
    | exact resolve eq90 eq12668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq12778 : y = (M.op x x) := by
    first
    | (have i₁ := eq12688
       have i₂ := eq12668
       grind)
    | exact superpose eq12668 eq12688
    | exact resolve eq12688 eq12668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12688
  have eq12782 : x = (M.op x y) := by
    first
    | (have i₁ := eq30 x
       have i₂ := eq12778
       grind)
    | exact superpose eq12778 eq30
    | exact resolve eq30 eq12778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq12778
  have eq12887 : x = (M.op y (M.op y x)) := by
    first
    | (have i₁ := eq1503 y x
       have i₂ := eq12782
       grind)
    | exact superpose eq12782 eq1503
    | exact resolve eq1503 eq12782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1503
  have eq12949 : x = (M.op y y) := by
    first
    | (have i₁ := eq12887
       have i₂ := eq12668
       grind)
    | exact superpose eq12668 eq12887
    | exact resolve eq12887 eq12668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12668 eq12887
  have eq13113 : x = (k x y) := by
    first
    | (have i₁ := eq5819 y y
       have i₂ := eq12949
       grind)
    | exact superpose eq12949 eq5819
    | exact resolve eq5819 eq12949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5819 eq12949
  have eq13388 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq12509
       have i₂ := eq13113
       grind)
    | exact superpose eq13113 eq12509
    | exact resolve eq12509 eq13113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12509 eq13113
  have eq13401 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq13388
       have i₂ := eq12782
       grind)
    | exact superpose eq12782 eq13388
    | exact resolve eq13388 eq12782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12782 eq13388
  have eq13402 : False := by grind
  exact eq13402

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxy_pxx_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ X0 ≠ X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq9
    | exact resolve eq9 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 (M.op X0 X0)) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq23 X0 X0
       grind)
    | exact superpose eq23 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | exact resolve eq12 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq44 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq57 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq42 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq42
    | exact resolve eq42 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq68 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq102 : ∀ X0 X1 : G, (σ (k (k (τ X0) X1) (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq44 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq44
    | exact resolve eq44 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq237 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (σ X2) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq68 X0 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq68
    | exact resolve eq68 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq5907 : ∀ X0 X1 : G, (M.op (k X0 (σ (τ X1))) (k X0 (σ (τ X1)))) = (σ (k (τ (k X0 X1)) (τ (k X0 X1)))) ∨ (k X0 (σ (τ X1))) = (M.op (k X0 (σ (τ X1))) (k X0 (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq102 X1 (τ X0)
       have i₂ := eq57 X0 X1
       grind)
    | exact superpose eq57 eq102
    | (have j0 := eq102 X0 (τ X1)
       grind)
    | exact resolve eq102 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq102
  have eq5966 : ∀ X0 X1 : G, (M.op (k X0 (σ (τ X1))) (k X0 (σ (τ X1)))) = (k (σ (τ (k X0 X1))) (k X0 X1)) ∨ (k X0 (σ (τ X1))) = (M.op (k X0 (σ (τ X1))) (k X0 (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq5907 X0 X1
       have i₂ := eq19 (k X0 X1) (τ (k X0 X1))
       grind)
    | exact superpose eq19 eq5907
    | (have j0 := eq5907 X0 X1
       grind)
    | exact resolve eq5907 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5907
  have eq5975 : ∀ X0 X1 : G, (k (k X0 X1) (k X0 X1)) = (M.op (k X0 (σ (τ X1))) (k X0 (σ (τ X1)))) ∨ (k X0 (σ (τ X1))) = (M.op (k X0 (σ (τ X1))) (k X0 (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq5966 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq5966
    | (have j0 := eq5966 X0 X1
       grind)
    | exact resolve eq5966 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5966
  have eq5979 : ∀ X0 X1 : G, (k (k X0 X1) (k X0 X1)) = (M.op (k X0 X1) (k X0 X1)) ∨ (k X0 (σ (τ X1))) = (M.op (k X0 (σ (τ X1))) (k X0 (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq5975 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5975
    | (have j0 := eq5975 X0 X1
       grind)
    | exact resolve eq5975 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5975
  have eq5980 : ∀ X0 X1 : G, (k X0 X1) = (M.op (k X0 X1) (k X0 X1)) ∨ (k (k X0 X1) (k X0 X1)) = (M.op (k X0 X1) (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5979 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5979
    | (have j0 := eq5979 X0 X1
       grind)
    | exact resolve eq5979 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5979
  have eq5981 : ∀ X0 X1 : G, (k (k X0 X1) (k X0 X1)) = (M.op (k X0 X1) (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq5980 X0 X1
       have j1 := eq12 (k X0 X1) (k X0 X1)
       grind)
    | (have r₁ := eq5980 X0 X1
       have r₂ := eq12 X0 (k X0 X1)
       grind)
    | exact resolve eq5980 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5980
  have eq5982 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    grind
  have eq6027 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq5982 X0
       have j1 := eq32 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq5982 X0
       have r₂ := eq32 X0 x
       grind)
    | exact resolve eq5982 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq5982
  have eq6038 : ∀ X0 : G, (k (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq6027 X0
       have i₂ := eq23 X0 X0
       grind)
    | exact superpose eq23 eq6027
    | exact resolve eq6027 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq6027
  have eq6068 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq5981 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq6038 X0
       grind)
    | exact superpose eq6038 eq5981
    | exact resolve eq5981 eq6038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5981
  have eq6245 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq6068 (σ X0)
       grind)
    | exact superpose eq6068 eq15
    | exact resolve eq15 eq6068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6272 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq6245 X0
       have i₂ := eq6068 X0
       grind)
    | exact superpose eq6068 eq6245
    | exact resolve eq6245 eq6068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6068 eq6245
  have eq6461 : ∀ X0 X1 X2 : G, (k X0 (σ (k (τ X1) X2))) = (M.op (σ (τ X0)) (k X1 (σ X2))) ∨ (σ (τ X0)) = (k X1 (σ X2)) ∨ (k X1 (σ X2)) = (M.op (k X1 (σ X2)) (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X0 (k (τ X1) X2)
       have i₂ := eq237 X1 X2 (τ X0)
       grind)
    | exact superpose eq237 eq18
    | (have j1 := eq237 X1 X2 (τ X0)
       grind)
    | exact resolve eq18 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237
  have eq6503 : ∀ X0 X1 X2 : G, (k X0 (σ (k (τ X1) X2))) = (M.op X0 (k X1 (σ X2))) ∨ (σ (τ X0)) = (k X1 (σ X2)) ∨ (k X1 (σ X2)) = (M.op (k X1 (σ X2)) (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6461 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6461
    | (have j0 := eq6461 X0 X1 X2
       grind)
    | exact resolve eq6461 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6461
  have eq6519 : ∀ X0 X1 X2 : G, (k X0 (k X1 (σ X2))) = (M.op X0 (k X1 (σ X2))) ∨ (σ (τ X0)) = (k X1 (σ X2)) ∨ (k X1 (σ X2)) = (M.op (k X1 (σ X2)) (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6503 X0 X1 X2
       have i₂ := eq18 X1 X2
       grind)
    | exact superpose eq18 eq6503
    | (have j0 := eq6503 X0 X1 X2
       grind)
    | exact resolve eq6503 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq6503
  have eq6530 : ∀ X0 X1 X2 : G, (k X0 (k X1 (σ X2))) = (M.op X0 (k X1 (σ X2))) ∨ (σ (τ X0)) = (k X1 (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq6519 X0 X1 X2
       have j1 := eq12 X0 (k X1 (σ X2))
       grind)
    | (have r₁ := eq6519 X0 X1 X2
       have r₂ := eq12 X0 (k X1 (σ X2))
       grind)
    | exact resolve eq6519 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6519
  have eq6538 : ∀ X0 X1 X2 : G, (k X0 (k X1 (σ X2))) = (M.op X0 (k X1 (σ X2))) ∨ (k X1 (σ X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6530 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6530
    | (have j0 := eq6530 X0 X1 X2
       grind)
    | exact resolve eq6530 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6530
  have eq12943 : ∀ X0 X1 X2 : G, (k X1 (k X2 X0)) = (M.op X1 (k X2 X0)) ∨ (k X2 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6538 X0 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6538
    | exact resolve eq6538 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6538
  have eq33619 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12943 (M.op X0 X0) X1 (M.op X0 X0)
       have i₂ := eq6038 X0
       grind)
    | exact superpose eq6038 eq12943
    | (have j0 := eq12943 X0 (M.op X1 X0) X1
       grind)
    | exact resolve eq12943 eq6038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6038 eq12943
  have eq33795 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq33619 (τ X1) X0
       grind)
    | exact superpose eq33619 eq19
    | (have j1 := eq33619 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq33619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq33816 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq33619 (σ X1) (σ X0)
       grind)
    | exact superpose eq33619 eq15
    | (have j1 := eq33619 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq33619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33619
  have eq34412 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq33795 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq33795
    | exact resolve eq33795 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33795
  have eq34553 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq34412 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq34412
    | (have j0 := eq34412 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq34412 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34412
  have eq35383 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq33816 x y
       grind)
    | exact superpose eq33816 eq16
    | (have j1 := eq33816 x y
       grind)
    | exact resolve eq16 eq33816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33816
  have eq35553 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq35383
       have i₂ := eq34553 y x
       grind)
    | exact superpose eq34553 eq35383
    | (have j1 := eq34553 (σ x) (σ y)
       grind)
    | (have r₁ := eq35383
       have r₂ := eq34553 y x
       grind)
    | (have r₁ := eq35383
       have r₂ := eq34553 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq35383
       have r₂ := eq34553 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq35383 eq34553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34553 eq35383
  have eq35556 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq35553
  have eq35559 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq35556
       grind)
    | exact superpose eq35556 eq16
    | exact resolve eq16 eq35556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35556
  have eq35560 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq35559
       have r₂ := eq6272 x
       grind)
    | exact resolve eq35559 eq6272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35559
  have eq36601 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq35560
       grind)
    | exact superpose eq35560 eq16
    | exact resolve eq16 eq35560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36602 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq35560
       grind)
    | exact superpose eq35560 eq10
    | exact resolve eq10 eq35560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35560
  have eq36678 : x = y := by
    first
    | (have i₁ := eq36602
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq36602
    | exact resolve eq36602 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36602
  have eq36679 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq36601
       have i₂ := eq6272 x
       grind)
    | exact superpose eq6272 eq36601
    | exact resolve eq36601 eq6272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6272 eq36601
  have eq36688 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq36679
       have i₂ := eq36678
       grind)
    | exact superpose eq36678 eq36679
    | exact resolve eq36679 eq36678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36678 eq36679
  have eq36689 : False := by grind
  exact eq36689

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxx_pyy_pyx_Equation1904 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1904 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ a ∨ k a b = M.op b b :=
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
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  clear eq36
  have eq50 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq97 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq44 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq44
    | (have j0 := eq44 x
       grind)
    | exact resolve eq44 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq114 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq47 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq47
    | (have j0 := eq47 x
       grind)
    | exact resolve eq47 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq133 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq50
    | (have j0 := eq50 (M.op x y)
       grind)
    | exact resolve eq50 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq174 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq16 X0 x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq178 X0
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq178
    | exact resolve eq178 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq183 : ∀ X0 X1 : G, (M.op (M.op X1 (k X0 X0)) (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 X0
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq179 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq179
    | exact resolve eq179 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 (k X0 X0)
       have i₂ := eq179 X0
       grind)
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq188 X0 X1
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq188
    | exact resolve eq188 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq196 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq189 X0 X0
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq189
    | exact resolve eq189 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq202 : y = (M.op (M.op x y) (k y y)) := by
    first
    | (have i₁ := eq189 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq189
    | (have j0 := eq189 y x
       grind)
    | exact resolve eq189 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq203 : (σ y) = (M.op (M.op (σ x) (σ y)) (k (σ y) (σ y))) := by
    first
    | exact superpose eq26 eq189
    | (have j0 := eq189 (σ y) (σ x)
       grind)
    | exact resolve eq189 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq208 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq196 X0
       have i₂ := eq174 (k X0 X0)
       grind)
    | exact superpose eq174 eq196
    | exact resolve eq196 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq210 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 y) (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq202 eq16
    | exact resolve eq16 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq211 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 y) (k (M.op x y) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq210 X0
       have i₂ := eq174 sF0
       grind)
    | exact superpose eq174 eq210
    | exact resolve eq210 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq213 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq203 eq16
    | exact resolve eq16 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq214 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ y)) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq213 X0
       have i₂ := eq174 sF4
       grind)
    | exact superpose eq174 eq213
    | exact resolve eq213 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq329 : (M.op x y) = (M.op (k y y) (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq211 y
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq211
    | exact resolve eq211 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq334 : (M.op (σ x) (σ y)) = (M.op (k (σ y) (σ y)) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq214 sF3
       have i₂ := eq174 sF3
       grind)
    | exact superpose eq174 eq214
    | exact resolve eq214 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq366 : ∀ X0 : G, (k y y) = (M.op (M.op X0 (M.op x y)) (M.op (k y y) (k y y))) := by
    intro X0
    first
    | exact superpose eq329 eq16
    | exact resolve eq16 eq329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329
  have eq367 : ∀ X0 : G, (k y y) = (M.op (M.op X0 (M.op x y)) (k (k y y) (k y y))) := by
    intro X0
    first
    | (have i₁ := eq366 X0
       have i₂ := eq174 (k y y)
       grind)
    | exact superpose eq174 eq366
    | exact resolve eq366 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366
  have eq368 : ∀ X0 : G, (k y y) = (M.op (M.op X0 (M.op x y)) y) := by
    intro X0
    first
    | (have i₁ := eq367 X0
       have i₂ := eq208 y
       grind)
    | exact superpose eq208 eq367
    | exact resolve eq367 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367
  have eq370 : ∀ X0 : G, (k (σ y) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (k (σ y) (σ y)) (k (σ y) (σ y)))) := by
    intro X0
    first
    | exact superpose eq334 eq16
    | exact resolve eq16 eq334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334
  have eq371 : ∀ X0 : G, (k (σ y) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (k (k (σ y) (σ y)) (k (σ y) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq370 X0
       have i₂ := eq174 (k sF3 sF3)
       grind)
    | exact superpose eq174 eq370
    | exact resolve eq370 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370
  have eq372 : ∀ X0 : G, (k (σ y) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq371 X0
       have i₂ := eq208 sF3
       grind)
    | exact superpose eq208 eq371
    | exact resolve eq371 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371
  have eq416 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq418 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq510 : y ≠ (M.op x y) ∨ x = y ∨ (k y x) = (M.op x x) := by
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
  have eq512 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq516 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq512
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq512
    | exact resolve eq512 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512
  have eq518 : y ≠ (M.op x y) ∨ (k x x) = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq510
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq510
    | exact resolve eq510 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510
  have eq593 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq731 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq593 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq593
    | exact resolve eq593 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593
  have eq871 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq179 (τ X0)
       have i₂ := eq731 X0 X0
       grind)
    | exact superpose eq731 eq179
    | exact resolve eq179 eq731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq731
  have eq992 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq416
       grind)
    | exact superpose eq416 eq39
    | exact resolve eq39 eq416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416
  have eq993 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq992
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq992
    | exact resolve eq992 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq992
  have eq995 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20 eq993
    | exact resolve eq993 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq993
  have eq1020 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq183 (k X0 X0) X1
       have i₂ := eq208 X0
       grind)
    | exact superpose eq208 eq183
    | exact resolve eq183 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq1194 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq995 eq418
    | exact resolve eq418 eq995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1201 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq1194
       have r₂ := eq27
       grind)
    | exact resolve eq1194 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1194
  have eq1437 : (σ y) ≠ (σ y) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1201 eq516
    | (have r₁ := eq516
       have r₂ := eq1201
       grind)
    | exact resolve eq516 eq1201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516 eq1201
  have eq1438 : (σ y) ≠ (σ y) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq1437
  have eq1439 : (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq1438
  have eq1440 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq995 eq1439
    | exact resolve eq1439 eq995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq995 eq1439
  have eq1457 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1440 eq208
    | exact resolve eq208 eq1440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1459 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ (M.op x y)))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1440 eq871
    | exact resolve eq871 eq1440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq871 eq1440
  have eq1465 : (τ (σ x)) = (M.op (τ (σ x)) (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq28 eq1459
    | exact resolve eq1459 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1459
  have eq1473 : x = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq1465
    | exact resolve eq1465 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1465
  have eq1488 : (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1457 eq133
    | exact resolve eq133 eq1457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq1457
  have eq1503 : x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq1488
    | exact resolve eq1488 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1488
  have eq1549 : (M.op x y) = (k y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1473 eq368
    | exact resolve eq368 eq1473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368 eq1473
  have eq1561 : (M.op x y) = (k y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1549
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1549
    | exact resolve eq1549 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1549
  have eq1624 : y = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq208 y
       have i₂ := eq1561
       grind)
    | exact superpose eq1561 eq208
    | exact resolve eq208 eq1561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1561
  have eq1628 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1503 eq1624
    | exact resolve eq1624 eq1503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1503 eq1624
  have eq1629 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq1628
  have eq1636 : y = (τ (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq1629 eq31
    | exact resolve eq31 eq1629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1641 : (k y x) = (τ (k (σ x) (σ x))) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq1629 eq114
    | exact resolve eq114 eq1629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq1629
  have eq1662 : (k x x) = (k y x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq97 eq1641
    | exact resolve eq1641 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq1641
  have eq1667 : x = y ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq1636
    | exact resolve eq1636 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1636
  have eq1668 : y = (M.op x y) ∨ x = y := by grind
  clear eq1667
  have eq1670 : (k x x) = (k y x) ∨ x = y := by
    first
    | (have r₁ := eq1662
       have r₂ := eq518
       grind)
    | exact resolve eq1662 eq518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518 eq1662
  have eq1671 : (k x x) = (k (M.op x y) x) ∨ x = y := by
    first
    | exact superpose eq1668 eq1670
    | exact resolve eq1670 eq1668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1670
  have eq1673 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq24
       have i₂ := eq1668
       grind)
    | exact superpose eq1668 eq24
    | exact resolve eq24 eq1668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1668
  have eq1686 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq1673
    | exact resolve eq1673 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1673
  have eq1746 : (σ x) = (M.op (σ x) (σ (k (M.op x y) x))) ∨ x = y := by
    first
    | (have i₁ := eq187 x
       have i₂ := eq1671
       grind)
    | exact superpose eq1671 eq187
    | exact resolve eq187 eq1671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187 eq1671
  have eq1753 : (σ x) = (M.op (σ x) (k (σ (M.op x y)) (σ x))) ∨ x = y := by
    first
    | (have i₁ := eq1746
       have i₂ := eq39 sF0
       grind)
    | exact superpose eq39 eq1746
    | exact resolve eq1746 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1746
  have eq1757 : (σ x) = (M.op (σ x) (k (σ (M.op x y)) (σ x))) ∨ x = y := by
    first
    | exact superpose eq20 eq1753
    | exact resolve eq1753 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1753
  have eq1760 : (σ x) = (M.op (σ x) (k (σ (M.op x y)) (σ x))) ∨ x = y := by
    first
    | (have i₁ := eq1757
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1757
    | exact resolve eq1757 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1757
  have eq1763 : (σ x) = (M.op (σ x) (k (σ y) (σ x))) ∨ x = y := by
    first
    | exact superpose eq1686 eq1760
    | exact resolve eq1760 eq1686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1760
  have eq1780 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq418 eq1763
    | exact resolve eq1763 eq418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418 eq1763
  have eq2471 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1780 eq372
    | exact resolve eq372 eq1780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372
  have eq2474 : (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1780 eq1020
    | exact resolve eq1020 eq1780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1020
  have eq2482 : (σ x) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1780 eq2474
    | exact resolve eq2474 eq1780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1780 eq2474
  have eq2483 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq2471
    | exact resolve eq2471 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2471
  have eq2617 : (σ y) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2483 eq208
    | exact resolve eq208 eq2483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208 eq2483
  have eq2628 : (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2482 eq2617
    | exact resolve eq2617 eq2482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2482 eq2617
  have eq2629 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2628
  have eq2636 : (σ (M.op x y)) ≠ (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2629 eq27
    | exact resolve eq27 eq2629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2629
  have eq2661 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq2636
       have r₂ := eq1686
       grind)
    | exact resolve eq2636 eq1686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1686 eq2636
  have eq2663 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq2661 eq31
    | exact resolve eq31 eq2661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq2661
  have eq2692 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq2663
    | exact resolve eq2663 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2663
  have eq2693 : x = y := by grind
  clear eq2692
  have eq3011 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq2693
       grind)
    | exact superpose eq2693 eq18
    | exact resolve eq18 eq2693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq3012 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq2693
       grind)
    | exact superpose eq2693 eq24
    | exact resolve eq24 eq2693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2693
  have eq3023 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq3012
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3012
    | exact resolve eq3012 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3012
  have eq3024 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq3011
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq3011
    | exact resolve eq3011 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3011
  have eq3025 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq3023 eq26
    | exact resolve eq26 eq3023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq3023
  have eq3054 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq3025
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq3025
    | exact resolve eq3025 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq3025
  have eq3061 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq3024
       grind)
    | exact superpose eq3024 eq39
    | exact resolve eq39 eq3024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq3024
  have eq3074 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq3061
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3061
    | exact resolve eq3061 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq3061
  have eq3079 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3054 eq3074
    | exact resolve eq3074 eq3054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3054 eq3074
  have eq3081 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq3079
    | exact resolve eq3079 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq3079
  have eq3083 : False := by grind
  exact eq3083

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_x_pyx_Equation1904 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1904 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq31 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq25 X0
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ (M.op X0 X0))) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq25 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq25
    | exact resolve eq25 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) X2)) = (M.op X0 (M.op (M.op X1 (M.op (M.op X0 X0) X2)) (M.op X1 (M.op (M.op X0 X0) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 (M.op X0 X0) X0 X1 X2
       have i₂ := eq25 X0
       grind)
    | exact superpose eq25 eq24
    | exact resolve eq24 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X0 X1 X2 (M.op X0 X0)
       have i₂ := eq25 X0
       grind)
    | exact superpose eq25 eq24
    | exact resolve eq24 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq25
  have eq73 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq28
    | (have j0 := eq28 X0 X1
       have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq28 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq470 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq65 X0 X0 X1
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq65
    | exact resolve eq65 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq777 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) = (M.op X0 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X0 (M.op (M.op X0 X0) X1) X1
       have i₂ := eq31 (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq31 eq61
    | exact resolve eq61 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq1224 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq73 x y
       grind)
    | exact superpose eq73 eq16
    | (have j1 := eq73 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq73 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq73 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq73 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq1253 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1224
  have eq1610 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq1253
       grind)
    | exact superpose eq1253 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1253
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1253
       grind)
    | exact resolve eq13 eq1253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1626 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq470 (σ y) (σ x)
       have i₂ := eq1253
       grind)
    | exact superpose eq1253 eq470
    | exact resolve eq470 eq1253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1253
  have eq1627 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1610
  have eq1628 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1627
  have eq1630 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1626
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq1626
    | exact resolve eq1626 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1626
  have eq1635 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1628
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq1628
    | exact resolve eq1628 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1628
  have eq3197 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq1635
       grind)
    | exact superpose eq1635 eq10
    | exact resolve eq10 eq1635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1635
  have eq3232 : y = (k y x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq3197
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq3197
    | exact resolve eq3197 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3197
  have eq3234 : y = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq13 y (k y x)
       grind)
    | (have r₁ := eq3232
       have r₂ := eq13 y x
       grind)
    | exact resolve eq3232 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3232
  have eq5641 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq3234
       grind)
    | exact superpose eq3234 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq3234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3234
  have eq5642 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq5641
  have eq8513 : ∀ X0 : G, x = (M.op (M.op X0 y) (M.op x x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq9 x X0 y
       have i₂ := eq5642
       grind)
    | exact superpose eq5642 eq9
    | exact resolve eq9 eq5642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14883 : x = (M.op y (M.op x x)) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq8513 x
       have i₂ := eq5642
       grind)
    | exact superpose eq5642 eq8513
    | exact resolve eq8513 eq5642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5642 eq8513
  have eq14952 : x = (M.op y (M.op x x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq14883
  have eq26547 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op y y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9 y X0 (M.op x x)
       have i₂ := eq14952
       grind)
    | exact superpose eq14952 eq9
    | exact resolve eq9 eq14952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14952
  have eq58581 : (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq777 x (M.op y y)
       have i₂ := eq26547 x
       grind)
    | exact superpose eq26547 eq777
    | exact resolve eq777 eq26547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777 eq26547
  have eq68097 : ∀ X0 : G, y = (M.op (M.op X0 y) (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq31 y X0
       have i₂ := eq58581
       grind)
    | exact superpose eq58581 eq31
    | exact resolve eq31 eq58581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58581
  have eq168808 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ y)) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq56 (M.op x y) x
       have i₂ := eq68097 x
       grind)
    | exact superpose eq68097 eq56
    | exact resolve eq56 eq68097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68097
  have eq169012 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq168808 x
       have i₂ := eq470 (σ y) x
       grind)
    | exact superpose eq470 eq168808
    | exact resolve eq168808 eq470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168808
  have eq169068 : (σ (M.op x y)) = (σ (M.op y y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq169012
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq169012
    | exact resolve eq169012 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169012
  have eq253807 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq1630
       grind)
    | exact superpose eq1630 eq16
    | exact resolve eq16 eq1630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1630
  have eq254181 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq253807
       have r₂ := eq169068
       grind)
    | exact resolve eq253807 eq169068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169068 eq253807
  have eq257601 : y = (M.op x (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq31 y x
       have i₂ := eq254181
       grind)
    | exact superpose eq254181 eq31
    | exact resolve eq31 eq254181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq257619 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq470 y x
       have i₂ := eq254181
       grind)
    | exact superpose eq254181 eq470
    | exact resolve eq470 eq254181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq268873 : y = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq257601
       have i₂ := eq257619
       grind)
    | exact superpose eq257619 eq257601
    | exact resolve eq257601 eq257619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257601
  have eq269029 : y = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq268873
  have eq350133 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq269029
       have i₂ := eq254181
       grind)
    | exact superpose eq254181 eq269029
    | exact resolve eq269029 eq254181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254181 eq269029
  have eq350346 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq350133
  have eq378314 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq56 x x
       have i₂ := eq350346
       grind)
    | exact superpose eq350346 eq56
    | exact resolve eq56 eq350346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq378315 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq57 x
       have i₂ := eq350346
       grind)
    | exact superpose eq350346 eq57
    | exact resolve eq57 eq350346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq350346
  have eq378707 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq378314 x
       have i₂ := eq470 (σ y) x
       grind)
    | exact superpose eq470 eq378314
    | exact resolve eq378314 eq470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470 eq378314
  have eq378772 : (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq378707
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq378707
    | exact resolve eq378707 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378707
  have eq597924 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq378772
       have i₂ := eq257619
       grind)
    | exact superpose eq257619 eq378772
    | exact resolve eq378772 eq257619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257619 eq378772
  have eq598449 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq597924
  have eq793958 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq378315
       grind)
    | exact superpose eq378315 eq16
    | exact resolve eq16 eq378315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378315
  have eq794472 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq793958
       have r₂ := eq598449
       grind)
    | exact resolve eq793958 eq598449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598449 eq793958
  have eq828742 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq794472
       grind)
    | exact superpose eq794472 eq10
    | exact resolve eq10 eq794472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq794472
  have eq829317 : x = y ∨ x = y := by
    first
    | (have i₁ := eq828742
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq828742
    | exact resolve eq828742 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828742
  have eq829318 : x = y := by grind
  clear eq829317
  have eq858982 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq829318
       grind)
    | exact superpose eq829318 eq16
    | exact resolve eq16 eq829318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829318
  have eq858983 : False := by grind
  exact eq858983
