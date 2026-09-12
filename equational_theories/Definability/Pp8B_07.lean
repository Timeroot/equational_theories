import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1473`: `x = (x ◇ y) ◇ (z ◇ (w ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(Y,Y) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pxx_y_pyy_x_pxy_Equation1473 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1473 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1473.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X3 X0))) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq24 : ∀ X0 X1 X4 X5 : G, (M.op X0 X1) = (M.op X0 (M.op X4 (M.op X5 (M.op X0 X1)))) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq9 (M.op X0 X1) (M.op x (M.op x X0)) X4 X5
       have i₂ := eq9 X0 X1 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op (M.op X1 (M.op X2 X0)) X3) (M.op X4 X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 (M.op X1 (M.op X2 X0)) X3 X4 (M.op X0 x)
       have i₂ := eq9 X0 x X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
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
       have i₂ := eq37 (σ X0)
       grind)
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq39
    | exact resolve eq39 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq39
  have eq67 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
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
  have eq83 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq67 X0 X1
       have i₂ := eq44 X0
       grind)
    | exact superpose eq44 eq67
    | (have j0 := eq67 X0 X1
       grind)
    | exact resolve eq67 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq125 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op X1 (M.op X2 (σ X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) (σ X0) X1 X2
       have i₂ := eq44 X0
       grind)
    | exact superpose eq44 eq9
    | exact resolve eq9 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X0)) = (M.op X1 (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq24 X1 (M.op X2 X0) X3 (M.op X0 x)
       have i₂ := eq9 X0 x X1 X2
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X2) = (M.op X3 (M.op X4 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq24 X3 X2 X4 (M.op (M.op X0 (M.op X1 X2)) x)
       have i₂ := eq25 X2 X0 X1 x X3
       grind)
    | exact superpose eq25 eq24
    | exact resolve eq24 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq313 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (σ X0))) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq138 (σ X0) X1 X2 (σ X0)
       have i₂ := eq44 X0
       grind)
    | exact superpose eq44 eq138
    | exact resolve eq138 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq579 : ∀ X0 X1 X2 X3 : G, (M.op X1 (σ X0)) = (M.op X1 (M.op X2 (σ (M.op X0 (M.op X3 X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq313 (M.op X0 (M.op X3 X0)) X1 X2
       have i₂ := eq9 X0 (M.op X3 X0) X0 X3
       grind)
    | exact superpose eq9 eq313
    | exact resolve eq313 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq869 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq83 X0 X1
       grind)
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq83 X0 X1
       grind)
    | exact superpose eq83 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq83 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq83 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq83 X0 X1
       grind)
    | exact resolve eq12 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq870 : ∀ X0 X1 X2 X3 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (M.op X2 (M.op X3 (M.op (σ X0) (σ X1))))) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq24 (σ X0) (σ X1) x x
       have i₂ := eq83 X0 X1
       grind)
    | (have i₁ := eq24 (σ X1) (σ X0) x x
       have i₂ := eq83 X0 X1
       grind)
    | exact superpose eq83 eq24
    | (have j1 := eq83 X0 X1
       grind)
    | exact resolve eq24 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq83
  have eq905 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq869 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869
  have eq927 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq870 X0 X1 x x
       have i₂ := eq187 x (σ X0) (σ X1) (σ X1) x
       grind)
    | exact superpose eq187 eq870
    | (have j0 := eq870 X0 X1 x x
       grind)
    | exact resolve eq870 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq870
  have eq928 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq905 X0 X1
       have i₂ := eq44 X1
       grind)
    | exact superpose eq44 eq905
    | (have j0 := eq905 X0 X1
       grind)
    | exact resolve eq905 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905
  have eq950 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq927 X0 X1
       have i₂ := eq44 X1
       grind)
    | exact superpose eq44 eq927
    | (have j0 := eq927 X0 X1
       grind)
    | exact resolve eq927 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq927
  have eq951 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq928 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq928
    | (have j0 := eq928 X0 X1
       grind)
    | exact resolve eq928 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq928
  have eq1299 : ∀ X0 X1 X2 X3 : G, (σ (M.op X0 (M.op X1 X0))) = (M.op (σ X0) (M.op X2 (M.op X3 (σ (M.op X0 (M.op X1 X0)))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq125 (M.op X0 (M.op X1 X0)) X2 X3
       have i₂ := eq9 X0 (M.op X1 X0) X0 X1
       grind)
    | exact superpose eq9 eq125
    | exact resolve eq125 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq1376 : ∀ X0 X1 X2 : G, (σ (M.op X0 (M.op X1 X0))) = (M.op (σ X0) (M.op X2 (σ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1299 X0 X1 X2 x
       have i₂ := eq579 X0 X2 x X1
       grind)
    | exact superpose eq579 eq1299
    | exact resolve eq1299 eq579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579 eq1299
  have eq2284 : ∀ X0 X1 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq313 X0 (σ X0) x
       have i₂ := eq1376 X0 X1 x
       grind)
    | exact superpose eq1376 eq313
    | exact resolve eq313 eq1376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313 eq1376
  have eq13128 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq950 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq950
  have eq13135 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq13128 X0 X1
       have j1 := eq951 X0 X1
       grind)
    | (have r₁ := eq13128 X0 X1
       have r₂ := eq951 X0 X1
       grind)
    | (have r₁ := eq13128 X0 X0
       have r₂ := eq951 X0 (k X0 X0)
       grind)
    | exact resolve eq13128 eq951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq951 eq13128
  have eq105100 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 X1) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq13135 X1 X0
       grind)
    | (have i₁ := eq10 X1
       have i₂ := eq13135 X0 X1
       grind)
    | exact superpose eq13135 eq10
    | (have j1 := eq13135 X1 X0
       grind)
    | exact resolve eq10 eq13135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13135
  have eq105676 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq105100 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq105100
    | (have j0 := eq105100 X0 X1
       grind)
    | exact resolve eq105100 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105100
  have eq107704 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq105676 y x
       grind)
    | exact superpose eq105676 eq16
    | (have j1 := eq105676 y x
       grind)
    | exact resolve eq16 eq105676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105676
  have eq108844 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq107704
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq107704
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq107704 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107704
  have eq108863 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq108844
  have eq108864 : (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq108863
  have eq109936 : ∀ X0 X1 X2 : G, (M.op X0 x) = (M.op X0 (M.op X1 (M.op X2 (M.op x y)))) ∨ y = (M.op x x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq187 X2 y x X0 X1
       have i₂ := eq108864
       grind)
    | exact superpose eq108864 eq187
    | exact resolve eq187 eq108864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110055 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq109936 X0 x x
       have i₂ := eq187 x x y X0 x
       grind)
    | exact superpose eq187 eq109936
    | exact resolve eq109936 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187 eq109936
  have eq114042 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op X0 x) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq2284 x x
       have i₂ := eq110055 X0
       grind)
    | exact superpose eq110055 eq2284
    | (have j1 := eq110055 X0
       grind)
    | exact resolve eq2284 eq110055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110055
  have eq114094 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq114042 X0
       grind)
    | (have r₁ := eq114042 X0
       have r₂ := eq16
       grind)
    | exact resolve eq114042 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114042
  have eq114939 : ∀ X0 X1 X2 : G, y = (M.op (M.op y X1) (M.op X2 (M.op X0 x))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 y X1 X2 X0
       have i₂ := eq114094 X0
       grind)
    | exact superpose eq114094 eq9
    | exact resolve eq9 eq114094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114094
  have eq115972 : ∀ X0 X1 : G, y = (M.op (M.op x y) (M.op X0 (M.op X1 x))) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq114939 X1 x X0
       have i₂ := eq108864
       grind)
    | exact superpose eq108864 eq114939
    | exact resolve eq114939 eq108864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108864 eq114939
  have eq116791 : y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq115972 x x
       have i₂ := eq9 x y x x
       grind)
    | exact superpose eq9 eq115972
    | exact resolve eq115972 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115972
  have eq118311 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq2284 x x
       have i₂ := eq116791
       grind)
    | exact superpose eq116791 eq2284
    | exact resolve eq2284 eq116791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2284 eq116791
  have eq118398 : x = y := by
    first
    | (have r₁ := eq118311
       have r₂ := eq16
       grind)
    | exact resolve eq118311 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118311
  have eq119079 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq118398
       grind)
    | exact superpose eq118398 eq16
    | exact resolve eq16 eq118398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118398
  have eq119086 : False := by grind
  exact eq119086

/-- `Equation1473`: `x = (x ◇ y) ◇ (z ◇ (w ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(Y,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyx_y_pyx_pxy_pyx_Equation1473 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1473 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1473.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X3 X0))) = X0 := by
    intro X0 X1 X2 X3
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
  have eq50 : ∀ X0 X1 : G, x = (M.op (M.op x y) (M.op X0 (M.op X1 x))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 x y X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x y X0 X1
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 (σ x)))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y) X0 X1
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X4 X5 : G, (M.op X0 X1) = (M.op X0 (M.op X4 (M.op X5 (M.op X0 X1)))) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq14 (M.op X0 X1) (M.op x (M.op x X0)) X4 X5
       have i₂ := eq14 X0 X1 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, y = (M.op (M.op y X0) (M.op X1 (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 y X0 X1 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y X0 X1 x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ y) X0) (M.op X1 (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) X0 X1 (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 X0) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X1 X0) X2 (M.op X0 x) x
       have i₂ := eq14 X0 x x X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X0)) X2) ≠ X0 ∨ (M.op (M.op X0 (M.op X1 X0)) X2) = (k X2 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op X0 (M.op X1 X0))
       have i₂ := eq14 X0 (M.op X1 X0) X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X2 (M.op X0 (M.op X1 X0))
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq70 (σ X0)
       grind)
    | exact superpose eq70 eq10
    | exact resolve eq10 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq72 X0
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq72
    | exact resolve eq72 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq81 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
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
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq105 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq106 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq109 : (σ (k y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq105
       have i₂ := eq70 sF3
       grind)
    | exact superpose eq70 eq105
    | exact resolve eq105 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq111 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq109
       have i₂ := eq70 y
       grind)
    | exact superpose eq70 eq109
    | exact resolve eq109 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq104
       have i₂ := eq81 y x
       grind)
    | exact superpose eq81 eq104
    | (have j1 := eq81 y x
       grind)
    | exact resolve eq104 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq113
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq113
    | exact resolve eq113 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq120 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq119
    | exact resolve eq119 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq121 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq120
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq120
    | exact resolve eq120 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq127 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq106 eq16
    | exact resolve eq16 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq128 : x ≠ (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (k y x) = (M.op y x) := by
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
  clear eq18
  have eq142 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq121 eq81
    | (have j0 := eq81 (σ y) (σ x)
       grind)
    | exact resolve eq81 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq143 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq142
    | exact resolve eq142 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq146 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq143
       have r₂ := eq27
       grind)
    | exact resolve eq143 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq148 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq146
    | exact resolve eq146 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq160 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq163 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq160
       have i₂ := eq70 sF1
       grind)
    | exact superpose eq70 eq160
    | exact resolve eq160 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160
  have eq165 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq163
       have i₂ := eq70 sF0
       grind)
    | exact superpose eq70 eq163
    | exact resolve eq163 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq167 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq148 eq27
    | exact resolve eq27 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq81 (σ X0) sF2
       grind)
    | exact superpose eq81 eq39
    | (have j1 := eq81 (σ X0) (σ x)
       grind)
    | exact resolve eq39 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq81
  have eq201 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq165 eq16
    | exact resolve eq16 eq165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165
  have eq258 : ∀ X2 X3 : G, (M.op x y) = (M.op x (M.op X2 (M.op X3 (M.op x y)))) := by
    intro X2 X3
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq263 : ∀ X0 X1 : G, (σ x) = (M.op (σ x) (M.op X0 (M.op X1 (σ x)))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq148 eq51
    | exact resolve eq51 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq275 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) X0) y) := by
    intro X0
    first
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq310 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ y) X0) (M.op X1 (σ x))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq148 eq54
    | exact resolve eq54 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq322 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq310 eq51
    | exact resolve eq51 eq310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq323 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq310 eq14
    | exact resolve eq14 eq310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq335 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ y) (M.op (σ x) (σ y))) = (k (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq322 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq322
       grind)
    | exact resolve eq12 eq322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322
  have eq339 : (M.op (σ y) (M.op (σ x) (σ y))) = (k (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq335
       have r₂ := eq148
       grind)
    | exact resolve eq335 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335
  have eq364 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (τ X0)
       have i₂ := eq70 (τ X0)
       grind)
    | exact superpose eq70 eq34
    | exact resolve eq34 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq375 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq364 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq364
    | exact resolve eq364 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364
  have eq377 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq375 X0
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq375
    | exact resolve eq375 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375
  have eq509 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq148 eq339
    | exact resolve eq339 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339
  have eq512 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq509
  have eq515 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq512 eq121
    | exact resolve eq121 eq512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512
  have eq518 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by grind
  clear eq515
  have eq524 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq518 eq67
    | exact resolve eq67 eq518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq518
  have eq555 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq524
       have r₂ := eq148
       grind)
    | exact resolve eq524 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148 eq524
  have eq631 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq555 eq121
    | exact resolve eq121 eq555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555
  have eq634 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by grind
  clear eq631
  have eq638 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq634
       have r₂ := eq27
       grind)
    | exact resolve eq634 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634
  have eq643 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op X0 (σ (M.op x y)))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq638 eq263
    | exact resolve eq263 eq638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263
  have eq649 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq638 eq310
    | exact resolve eq310 eq638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq654 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq649 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649
  have eq660 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op X0 (σ (M.op x y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq643 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643
  have eq690 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op X1 y)) := by
    intro X0 X1
    first
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq691 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op X1 (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq54 eq52
    | exact resolve eq52 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq692 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op X1 (σ y))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq310 eq52
    | exact resolve eq52 eq310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq310
  have eq769 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq638 eq654
    | exact resolve eq654 eq638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654
  have eq786 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq769
  have eq787 : (τ (σ y)) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq786 eq201
    | exact resolve eq201 eq786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201 eq786
  have eq800 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq787
    | exact resolve eq787 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787
  have eq1302 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (M.op (σ x) (M.op X0 (σ x)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq323 eq69
    | (have r₁ := eq69 (σ x) x (σ y)
       have r₂ := eq323 (M.op x (σ x))
       grind)
    | exact resolve eq69 eq323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323
  have eq1312 : ∀ X0 : G, (σ x) = (k (σ y) (M.op (σ x) (M.op X0 (σ x)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1302 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1302
  have eq1329 : (σ x) = (k (σ y) (M.op (σ x) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq638 eq1312
    | exact resolve eq1312 eq638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1312
  have eq1338 : (σ x) = (k (σ y) (M.op (σ x) (σ (M.op x y)))) ∨ x = (M.op x y) := by grind
  clear eq1329
  have eq1461 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq800 eq275
    | exact resolve eq275 eq800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq800
  have eq1481 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq111
       have i₂ := eq1461
       grind)
    | exact superpose eq1461 eq111
    | exact resolve eq111 eq1461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1461
  have eq1501 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq1481
    | exact resolve eq1481 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1481
  have eq1518 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1501 eq692
    | exact resolve eq692 eq1501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692 eq1501
  have eq1531 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1518 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1518
  have eq1754 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1531 eq638
    | exact resolve eq638 eq1531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq638 eq1531
  have eq1765 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq1754
  have eq1799 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1765 eq660
    | exact resolve eq660 eq1765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660 eq1765
  have eq1812 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq1799
  have eq1841 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1812 eq1338
    | exact resolve eq1338 eq1812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1338 eq1812
  have eq1862 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq1841
  have eq2052 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1862 eq121
    | exact resolve eq121 eq1862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq1862
  have eq2056 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq2052
  have eq2065 : x = (M.op x y) := by
    first
    | (have r₁ := eq2056
       have r₂ := eq167
       grind)
    | exact resolve eq2056 eq167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167 eq2056
  have eq2068 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq2065 eq20
    | exact resolve eq20 eq2065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq2073 : x ≠ x ∨ x = (M.op x x) ∨ (k y x) = (M.op y x) := by
    first
    | exact superpose eq2065 eq128
    | (have r₁ := eq128
       have r₂ := eq2065
       grind)
    | exact resolve eq128 eq2065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq2077 : ∀ X0 : G, x = (M.op (M.op x X0) y) := by
    intro X0
    first
    | exact superpose eq2065 eq275
    | exact resolve eq275 eq2065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq2078 : x = (M.op x x) ∨ (k y x) = (M.op y x) := by grind
  clear eq2073
  have eq2084 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2068
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2068
    | exact resolve eq2068 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2068
  have eq2088 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq2084 eq26
    | exact resolve eq26 eq2084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq2161 : ∀ X2 X3 : G, x = (M.op x (M.op X2 (M.op X3 x))) := by
    intro X2 X3
    first
    | exact superpose eq2065 eq258
    | exact resolve eq258 eq2065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258
  have eq2170 : ∀ X0 : G, x ≠ x ∨ x = (k y (M.op x (M.op X0 x))) := by
    intro X0
    first
    | (have i₁ := eq69 x x y
       have i₂ := eq2077 (M.op x x)
       grind)
    | exact superpose eq2077 eq69
    | (have r₁ := eq69 x x y
       have r₂ := eq2077 (M.op x x)
       grind)
    | exact resolve eq69 eq2077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2077
  have eq2182 : ∀ X0 : G, x = (k y (M.op x (M.op X0 x))) := by
    intro X0
    first
    | (have j0 := eq2170 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2170
  have eq2238 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op X1 y)) := by
    intro X0 X1
    first
    | exact superpose eq2065 eq690
    | exact resolve eq690 eq2065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690
  have eq2250 : ∀ X0 X1 : G, y = (M.op (M.op y X1) (M.op X0 x)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 y X1 X0 x
       have i₂ := eq2238 X0 x
       grind)
    | exact superpose eq2238 eq14
    | exact resolve eq14 eq2238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2334 : ∀ X0 X1 : G, y ≠ y ∨ y = (k (M.op X1 x) (M.op y (M.op X0 y))) := by
    intro X0 X1
    first
    | (have i₁ := eq69 y X1 (M.op X0 x)
       have i₂ := eq2250 X0 (M.op X1 y)
       grind)
    | exact superpose eq2250 eq69
    | (have r₁ := eq69 y X1 (M.op X0 x)
       have r₂ := eq2250 X0 (M.op X1 y)
       grind)
    | exact resolve eq69 eq2250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq2250
  have eq2353 : ∀ X0 X1 : G, y = (k (M.op X1 x) (M.op y (M.op X0 y))) := by
    intro X0 X1
    first
    | (have j0 := eq2334 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2334
  have eq2358 : ∀ X1 : G, y = (k (M.op X1 x) (M.op y x)) := by
    intro X1
    first
    | (have i₁ := eq2353 x X1
       have i₂ := eq2238 y x
       grind)
    | exact superpose eq2238 eq2353
    | exact resolve eq2353 eq2238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2353
  have eq2424 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (σ (M.op (M.op y y) (M.op y y))) := by
    first
    | (have i₁ := eq77 (M.op y y)
       have i₂ := eq111
       grind)
    | exact superpose eq111 eq77
    | exact resolve eq77 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq111
  have eq2464 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (σ (M.op (M.op y y) x)) := by
    first
    | (have i₁ := eq2424
       have i₂ := eq2238 (M.op y y) y
       grind)
    | exact superpose eq2238 eq2424
    | exact resolve eq2424 eq2238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2424
  have eq2469 : (σ (M.op (M.op y y) x)) = (M.op (M.op (σ y) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq691 eq2464
    | exact resolve eq2464 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691 eq2464
  have eq3194 : (M.op (M.op y y) x) = (τ (M.op (M.op (σ y) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq16 (M.op (M.op y y) x)
       have i₂ := eq2469
       grind)
    | exact superpose eq2469 eq16
    | exact resolve eq16 eq2469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2469
  have eq4709 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq2084 eq179
    | (have j0 := eq179 X0
       grind)
    | exact resolve eq179 eq2084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq4710 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq2084 eq4709
    | (have j0 := eq4709 X0
       grind)
    | exact resolve eq4709 eq2084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4709
  have eq4740 : (σ (k y x)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq4710 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4710
    | (have j0 := eq4710 y
       grind)
    | exact resolve eq4710 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4710
  have eq4767 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq2088 eq4740
    | exact resolve eq4740 eq2088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4740
  have eq4784 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq4767
       have i₂ := eq104
       grind)
    | exact superpose eq104 eq4767
    | exact resolve eq4767 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq4767
  have eq4797 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq2084 eq4784
    | exact resolve eq4784 eq2084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4784
  have eq4808 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq2088 eq4797
    | exact resolve eq4797 eq2088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2088 eq4797
  have eq4813 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq4808
       have r₂ := eq27
       grind)
    | exact resolve eq4808 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4808
  have eq4825 : (k y (M.op x y)) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq4813 eq127
    | exact resolve eq127 eq4813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq4813
  have eq4827 : (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2065 eq4825
    | exact resolve eq4825 eq2065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2065 eq4825
  have eq5419 : (M.op y x) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2078
       have i₂ := eq4827
       grind)
    | exact superpose eq4827 eq2078
    | exact resolve eq2078 eq4827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2078
  have eq5572 : y = (k (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2358 y
       have i₂ := eq5419
       grind)
    | exact superpose eq5419 eq2358
    | exact resolve eq2358 eq5419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2358 eq5419
  have eq5594 : y = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq5572
       have i₂ := eq70 (τ sF4)
       grind)
    | exact superpose eq70 eq5572
    | exact resolve eq5572 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq5572
  have eq5599 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq5594 eq377
    | exact resolve eq377 eq5594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377 eq5594
  have eq5621 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq5599
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq5599
    | exact resolve eq5599 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq5599
  have eq5643 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (M.op (σ x) (σ y))) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq5621 eq56
    | exact resolve eq56 eq5621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq5621
  have eq5895 : (τ (σ y)) = (M.op (M.op y y) x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq5643 eq3194
    | exact resolve eq3194 eq5643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3194 eq5643
  have eq5932 : y = (M.op (M.op y y) x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq5895
    | exact resolve eq5895 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq5895
  have eq6969 : ∀ X0 : G, x = (M.op x (M.op X0 y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq2161 X0 (M.op y y)
       have i₂ := eq5932
       grind)
    | exact superpose eq5932 eq2161
    | exact resolve eq2161 eq5932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2161 eq5932
  have eq7002 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq6969 x
       have i₂ := eq2238 x x
       grind)
    | exact superpose eq2238 eq6969
    | exact resolve eq6969 eq2238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2238 eq6969
  have eq7003 : x = (M.op x x) := by grind
  clear eq7002
  have eq7024 : x = (k y (M.op x x)) := by
    first
    | (have i₁ := eq2182 x
       have i₂ := eq7003
       grind)
    | exact superpose eq7003 eq2182
    | exact resolve eq2182 eq7003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2182
  have eq7055 : x = (k y x) := by
    first
    | (have i₁ := eq7024
       have i₂ := eq7003
       grind)
    | exact superpose eq7003 eq7024
    | exact resolve eq7024 eq7003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7003 eq7024
  have eq7064 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq7055
       have i₂ := eq4827
       grind)
    | exact superpose eq4827 eq7055
    | exact resolve eq7055 eq4827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4827 eq7055
  have eq7077 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7064 eq15
    | exact resolve eq15 eq7064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7064
  have eq7094 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7077
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq7077
    | exact resolve eq7077 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq7077
  have eq7098 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2084 eq7094
    | exact resolve eq7094 eq2084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2084 eq7094
  have eq7099 : False := by grind
  exact eq7099

/-- `Equation1473`: `x = (x ◇ y) ◇ (z ◇ (w ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(Y,Y) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyy_x_pyx_pxx_pyx_Equation1473 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1473 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1473.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X3 X0))) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
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
    | (have r₁ := eq11 (M.op X1 (M.op X1 X1)) X1
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | exact resolve eq11 eq13
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
  clear eq36
  have eq51 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
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
  clear eq45
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
  have eq175 : ∀ X0 X1 : G, x = (M.op (M.op x y) (M.op X0 (M.op X1 x))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 x y X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x y X0 X1
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 (σ x)))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0 X1
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X4 X5 : G, (M.op X0 X1) = (M.op X0 (M.op X4 (M.op X5 (M.op X0 X1)))) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq16 (M.op X0 X1) (M.op x (M.op x X0)) X4 X5
       have i₂ := eq16 X0 X1 x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 : G, y = (M.op (M.op y X0) (M.op X1 (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 y X0 X1 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 y X0 X1 x
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ y) X0) (M.op X1 (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) X0 X1 (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : ∀ X2 X3 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X2 (M.op X3 (M.op (σ x) (σ y))))) := by
    intro X2 X3
    first
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq610 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) (M.op X3 (k X0 X1))) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 X2 X3 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq611 : ∀ X0 X1 X2 X3 : G, (M.op (k X0 X1) (M.op X2 (M.op X3 X1))) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X1 X0 X2 X3
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq630 : (M.op x y) = (k y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq28 y x
       grind)
    | exact superpose eq28 eq18
    | (have j1 := eq28 y x
       grind)
    | exact resolve eq18 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq635 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq28 sF3 sF2
       grind)
    | exact superpose eq28 eq26
    | (have j1 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq640 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq642 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq630
       grind)
    | exact superpose eq630 eq40
    | exact resolve eq40 eq630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq630
  have eq643 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq642
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq642
    | exact resolve eq642 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642
  have eq645 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq643
    | exact resolve eq643 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643
  have eq676 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op X1 y)) := by
    intro X0 X1
    first
    | exact superpose eq178 eq177
    | exact resolve eq177 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq677 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op X1 (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq179 eq177
    | exact resolve eq177 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq740 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq645 eq635
    | exact resolve eq635 eq645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645
  have eq747 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq740
       have r₂ := eq27
       grind)
    | exact resolve eq740 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq740
  have eq755 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq747 eq28
    | (have j0 := eq28 y x
       grind)
    | exact resolve eq28 eq747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq757 : (σ x) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq747 eq13
    | exact resolve eq13 eq747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747
  have eq761 : (σ y) = (k (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq755
       have r₂ := eq757
       grind)
    | exact resolve eq755 eq757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755 eq757
  have eq764 : (τ (σ y)) = (k x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq761 eq98
    | exact resolve eq98 eq761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq761
  have eq770 : y = (k x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq32 eq764
    | exact resolve eq764 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq764
  have eq788 : x ≠ y ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq640 x
       have i₂ := eq770
       grind)
    | exact superpose eq770 eq640
    | (have j0 := eq640 x
       grind)
    | exact resolve eq640 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1100 : ∀ X0 X1 : G, x = (M.op (M.op x X0) (M.op X1 y)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq610 x x X0 X1
       have i₂ := eq770
       grind)
    | exact superpose eq770 eq610
    | (have j0 := eq610 x x x x
       grind)
    | exact resolve eq610 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1110 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X3 X0)) = (M.op X1 (k X0 X2)) ∨ (M.op X2 X2) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq177 X1 (k X0 X2) X3 (M.op X0 x)
       have i₂ := eq610 X0 X2 x X1
       grind)
    | exact superpose eq610 eq177
    | (have j1 := eq610 X0 X2 X2 X3
       grind)
    | exact resolve eq177 eq610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq610
  have eq1124 : ∀ X0 : G, x = (M.op (M.op x X0) (M.op x y)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq1100 X0 x
       have i₂ := eq676 (M.op x X0) x
       grind)
    | (have i₁ := eq1100 X0 x
       have i₂ := eq676 (M.op x X0) x
       grind)
    | exact superpose eq676 eq1100
    | (have j0 := eq1100 X0 x
       grind)
    | exact resolve eq1100 eq676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1100
  have eq1130 : ∀ X0 : G, x = (M.op (M.op x X0) (M.op x y)) ∨ x = (M.op x x) ∨ y = (k x x) := by
    intro X0
    first
    | exact superpose eq28 eq1124
    | (have j0 := eq1124 X0
       have j1 := eq28 x x
       grind)
    | exact resolve eq1124 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1124
  have eq1131 : ∀ X0 : G, x = (M.op (M.op x X0) (M.op x y)) ∨ x = y ∨ y = (k x x) := by
    intro X0
    first
    | exact superpose eq770 eq1130
    | (have j0 := eq1130 X0
       grind)
    | exact resolve eq1130 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1130
  have eq1136 : ∀ X0 X1 : G, x = (M.op y (M.op X0 (M.op X1 x))) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq611 x x X0 X1
       have i₂ := eq770
       grind)
    | exact superpose eq770 eq611
    | (have j0 := eq611 x x x x
       grind)
    | exact resolve eq611 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1222 : ∀ X0 X1 : G, x = (M.op y (M.op X0 (M.op X1 x))) ∨ x = (M.op x x) ∨ y = (k x x) := by
    intro X0 X1
    first
    | exact superpose eq28 eq1136
    | (have j0 := eq1136 X0 X1
       have j1 := eq28 x x
       grind)
    | exact resolve eq1136 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1136
  have eq1225 : ∀ X0 : G, x = (M.op y (M.op X0 (k x x))) ∨ x = (M.op x x) ∨ y = (k x x) := by
    intro X0
    first
    | exact superpose eq1110 eq1222
    | (have j1 := eq1110 x x x x
       grind)
    | exact resolve eq1222 eq1110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1222
  have eq1226 : ∀ X0 : G, x = (M.op y (M.op X0 (k x x))) ∨ x = y ∨ y = (k x x) := by
    intro X0
    first
    | exact superpose eq770 eq1225
    | (have j0 := eq1225 X0
       grind)
    | exact resolve eq1225 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1225
  have eq1588 : ∀ X1 : G, y = (M.op x (M.op X1 (M.op x y))) ∨ x = y ∨ y = (k x x) := by
    intro X1
    first
    | (have i₁ := eq178 (M.op x (k x x)) X1
       have i₂ := eq1226 x
       grind)
    | exact superpose eq1226 eq178
    | exact resolve eq178 eq1226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1226
  have eq1607 : x = (M.op y (M.op x y)) ∨ x = y ∨ y = (k x x) ∨ x = y ∨ y = (k x x) := by
    first
    | exact superpose eq1588 eq1131
    | exact resolve eq1131 eq1588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1612 : ∀ X0 : G, y ≠ (M.op X0 (M.op x y)) ∨ y = (k (M.op X0 (M.op x y)) x) ∨ x = y ∨ y = (k x x) := by
    intro X0
    first
    | exact superpose eq1588 eq13
    | exact resolve eq13 eq1588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1615 : ∀ X0 : G, y = (k (M.op X0 (M.op x y)) x) ∨ (M.op X0 (M.op x y)) = (M.op x x) ∨ x = y ∨ y = (k x x) := by
    intro X0
    first
    | exact superpose eq1588 eq28
    | (have j0 := eq28 (M.op X0 (M.op x y)) x
       grind)
    | exact resolve eq28 eq1588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1588
  have eq1620 : y = (k x x) ∨ x = y ∨ x = (M.op y (M.op x y)) := by grind
  clear eq1607
  have eq1624 : ∀ X0 : G, y = (k (M.op X0 (M.op x y)) x) ∨ y = (M.op X0 (M.op x y)) ∨ x = y ∨ y = (k x x) := by
    intro X0
    first
    | exact superpose eq770 eq1615
    | (have j0 := eq1615 X0
       grind)
    | exact resolve eq1615 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770 eq1615
  have eq1626 : ∀ X0 : G, y = (k (M.op X0 (M.op x y)) x) ∨ x = y ∨ y = (k x x) := by
    intro X0
    first
    | (have j0 := eq1624 X0
       have j1 := eq1612 X0
       grind)
    | (have r₁ := eq1624 X0
       have r₂ := eq1612 X0
       grind)
    | exact resolve eq1624 eq1612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1612 eq1624
  have eq1631 : ∀ X0 X1 : G, x = (M.op y (M.op X0 (M.op X1 x))) ∨ x = (M.op x x) ∨ x = y ∨ x = (M.op y (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq611 x x X0 X1
       have i₂ := eq1620
       grind)
    | exact superpose eq1620 eq611
    | (have j0 := eq611 x x x x
       grind)
    | exact resolve eq611 eq1620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1634 : ∀ X0 : G, x = (M.op y (M.op X0 (k x x))) ∨ x = (M.op x x) ∨ x = y ∨ x = (M.op y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1110 eq1631
    | (have j1 := eq1110 x x x x
       grind)
    | exact resolve eq1631 eq1110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1631
  have eq1637 : ∀ X0 : G, x = (M.op y (M.op X0 y)) ∨ x = (M.op x x) ∨ x = y ∨ x = (M.op y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1620 eq1634
    | exact resolve eq1634 eq1620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1620 eq1634
  have eq1640 : x = (M.op y (M.op x y)) ∨ x = (M.op x x) ∨ x = y ∨ x = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq1637 x
       have i₂ := eq676 y x
       grind)
    | (have i₁ := eq1637 x
       have i₂ := eq676 y x
       grind)
    | exact superpose eq676 eq1637
    | (have j0 := eq1637 x
       grind)
    | exact resolve eq1637 eq676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1637
  have eq1641 : x = (M.op y (M.op x y)) ∨ x = (M.op x x) ∨ x = y := by grind
  clear eq1640
  have eq1661 : ∀ X0 : G, y = (M.op x (M.op X0 (M.op x y))) ∨ x = (M.op x x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1641 eq178
    | exact resolve eq178 eq1641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq1679 : y = (k x x) ∨ x = y ∨ y = (k x x) ∨ x = y ∨ y = (k x x) := by
    first
    | exact superpose eq1131 eq1626
    | exact resolve eq1626 eq1131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1131 eq1626
  have eq1686 : y = (k x x) ∨ x = y := by grind
  clear eq1679
  have eq1689 : (σ y) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1686
       grind)
    | exact superpose eq1686 eq40
    | exact resolve eq40 eq1686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1695 : (σ y) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq1689
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1689
    | exact resolve eq1689 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1689
  have eq1697 : (σ y) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq1695
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1695
    | exact resolve eq1695 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1695
  have eq1705 : ∀ X0 X1 : G, (σ x) = (M.op (σ y) (M.op X0 (M.op X1 (σ x)))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq1697 eq611
    | (have j0 := eq611 (σ x) (σ x) x x
       grind)
    | exact resolve eq611 eq1697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1708 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op X0 (k (σ x) (σ x)))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1110 eq1705
    | (have j1 := eq1110 (σ x) x (σ x) x
       grind)
    | exact resolve eq1705 eq1110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1705
  have eq1712 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op X0 (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1697 eq1708
    | exact resolve eq1708 eq1697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1697 eq1708
  have eq1715 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq677 eq1712
    | (have j0 := eq1712 (σ x)
       grind)
    | exact resolve eq1712 eq677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq677 eq1712
  have eq2032 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X0 (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1715 eq192
    | exact resolve eq192 eq1715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192 eq1715
  have eq2057 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = y ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq1641 eq1661
    | exact resolve eq1661 eq1641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1641 eq1661
  have eq2078 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = y := by grind
  clear eq2057
  have eq2086 : y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq2078
       have r₂ := eq788
       grind)
    | exact resolve eq2078 eq788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq788 eq2078
  have eq2095 : ∀ X0 : G, x = (M.op (M.op x y) (M.op X0 y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq175 X0 x
       have i₂ := eq2086
       grind)
    | exact superpose eq2086 eq175
    | exact resolve eq175 eq2086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq2108 : x ≠ y ∨ x = (M.op x x) := by grind
  clear eq2086
  have eq2115 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2095 x
       have i₂ := eq676 sF0 x
       grind)
    | (have i₁ := eq2095 x
       have i₂ := eq676 sF0 x
       grind)
    | exact superpose eq676 eq2095
    | (have j0 := eq2095 x
       grind)
    | exact resolve eq2095 eq676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq676 eq2095
  have eq2267 : x ≠ (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq2115 eq13
    | (have r₁ := eq13 x x
       have r₂ := eq2115
       grind)
    | exact resolve eq13 eq2115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2270 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq2115 eq28
    | (have j0 := eq28 x x
       grind)
    | exact resolve eq28 eq2115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2115
  have eq2282 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq2267
       have r₂ := eq2270
       grind)
    | exact resolve eq2267 eq2270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2267 eq2270
  have eq2301 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq2282 eq42
    | exact resolve eq42 eq2282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq2305 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq2301
    | exact resolve eq2301 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2301
  have eq2307 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2305
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2305
    | exact resolve eq2305 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2305
  have eq2312 : (σ (M.op x y)) ≠ (σ x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq2307 eq640
    | (have j0 := eq640 (σ (M.op x y))
       grind)
    | exact resolve eq640 eq2307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640
  have eq2313 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (M.op X1 (σ (M.op x y))))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq2307 eq611
    | (have j0 := eq611 (σ (M.op x y)) (σ (M.op x y)) x x
       grind)
    | exact resolve eq611 eq2307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611
  have eq2315 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (k (σ (M.op x y)) (σ (M.op x y))))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq1110 eq2313
    | (have j1 := eq1110 (σ (M.op x y)) x (σ (M.op x y)) x
       grind)
    | exact resolve eq2313 eq1110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1110 eq2313
  have eq2319 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (σ x))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq2307 eq2315
    | exact resolve eq2315 eq2307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2315
  have eq8349 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq2319 eq2032
    | exact resolve eq2032 eq2319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2032
  have eq8393 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq8349
       have r₂ := eq2108
       grind)
    | exact resolve eq8349 eq2108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8349
  have eq8402 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq8393
       have r₂ := eq27
       grind)
    | exact resolve eq8393 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8393
  have eq8456 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq8402 eq2319
    | exact resolve eq2319 eq8402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2319
  have eq8481 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by grind
  clear eq8456
  have eq8488 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq8402 eq8481
    | exact resolve eq8481 eq8402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8402 eq8481
  have eq8492 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq8488
       have r₂ := eq2312
       grind)
    | exact resolve eq8488 eq2312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2312 eq8488
  have eq8506 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq8492 eq13
    | (have r₁ := eq13 (σ (M.op x y)) (σ (M.op x y))
       have r₂ := eq8492
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq8492
       grind)
    | exact resolve eq13 eq8492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8492
  have eq8522 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by grind
  clear eq8506
  have eq8528 : x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq2307 eq8522
    | exact resolve eq8522 eq2307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2307 eq8522
  have eq8544 : x ≠ x ∨ x = (k x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq8528
       grind)
    | exact superpose eq8528 eq13
    | (have r₁ := eq13 x x
       have r₂ := eq8528
       grind)
    | exact resolve eq13 eq8528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8528
  have eq8560 : x = (k x x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq8544
  have eq8580 : x = y ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1686
       have i₂ := eq8560
       grind)
    | exact superpose eq8560 eq1686
    | exact resolve eq1686 eq8560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8560
  have eq8593 : (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq8580
  have eq8612 : (k (M.op x y) (M.op x y)) = (τ (k (σ x) (σ x))) ∨ x = y := by
    first
    | exact superpose eq8593 eq134
    | exact resolve eq134 eq8593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134 eq8593
  have eq8647 : (k x x) = (k (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq98 eq8612
    | exact resolve eq8612 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq8612
  have eq8656 : y = (k (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq1686 eq8647
    | exact resolve eq8647 eq1686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8647
  have eq9059 : x = y ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq8656 eq2282
    | exact resolve eq2282 eq8656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2282 eq8656
  have eq9070 : x = y ∨ x = (M.op x x) := by grind
  clear eq9059
  have eq9080 : x = (M.op x x) := by
    first
    | (have r₁ := eq9070
       have r₂ := eq2108
       grind)
    | exact resolve eq9070 eq2108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2108 eq9070
  have eq9102 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq9080
       grind)
    | exact superpose eq9080 eq13
    | (have r₁ := eq13 x x
       have r₂ := eq9080
       grind)
    | exact resolve eq13 eq9080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9118 : x = (k x x) := by grind
  clear eq9102
  have eq9145 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1686
       have i₂ := eq9118
       grind)
    | exact superpose eq9118 eq1686
    | exact resolve eq1686 eq9118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1686
  have eq9151 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq9118
       grind)
    | exact superpose eq9118 eq40
    | exact resolve eq40 eq9118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq9118
  have eq9158 : x = y := by grind
  clear eq9145
  have eq9167 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq9151
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq9151
    | exact resolve eq9151 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9151
  have eq9169 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq9158
       grind)
    | exact superpose eq9158 eq18
    | exact resolve eq18 eq9158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq9170 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq9158
       grind)
    | exact superpose eq9158 eq24
    | exact resolve eq24 eq9158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq9158
  have eq9215 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq9170
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq9170
    | exact resolve eq9170 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9170
  have eq9216 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq9215 eq26
    | exact resolve eq26 eq9215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq9230 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq9215 eq635
    | exact resolve eq635 eq9215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635 eq9215
  have eq9299 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq9167 eq9230
    | exact resolve eq9230 eq9167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9167 eq9230
  have eq9315 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9216 eq9299
    | exact resolve eq9299 eq9216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9216 eq9299
  have eq9316 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq9315
  have eq9317 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq9316 eq27
    | exact resolve eq27 eq9316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq9316
  have eq9539 : x = (M.op x y) := by
    first
    | (have i₁ := eq9080
       have i₂ := eq9169
       grind)
    | exact superpose eq9169 eq9080
    | exact resolve eq9080 eq9169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9080 eq9169
  have eq9594 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq9539
       grind)
    | exact superpose eq9539 eq22
    | exact resolve eq22 eq9539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq9539
  have eq9761 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq9594 eq20
    | exact resolve eq20 eq9594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq9594
  have eq9779 : False := by grind
  exact eq9779

/-- `Equation1473`: `x = (x ◇ y) ◇ (z ◇ (w ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,Y) else if m(X,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pyy_pyy_pxx_pyx_Equation1473 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1473 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1473.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X3 X0))) = X0 := by
    intro X0 X1 X2 X3
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
  have eq50 : ∀ X0 X1 : G, x = (M.op (M.op x y) (M.op X0 (M.op X1 x))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 x y X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x y X0 X1
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 (σ x)))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y) X0 X1
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X4 X5 : G, (M.op X0 X1) = (M.op X0 (M.op X4 (M.op X5 (M.op X0 X1)))) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq14 (M.op X0 X1) (M.op x (M.op x X0)) X4 X5
       have i₂ := eq14 X0 X1 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, y = (M.op (M.op y X0) (M.op X1 (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 y X0 X1 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y X0 X1 x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ y) X0) (M.op X1 (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) X0 X1 (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op (M.op X1 (M.op X2 X0)) X3) (M.op X4 X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 (M.op X1 (M.op X2 X0)) X3 X4 (M.op X0 x)
       have i₂ := eq14 X0 x X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 X0) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X1 X0) X2 (M.op X0 x) x
       have i₂ := eq14 X0 x x X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : x ≠ (M.op x y) ∨ (k y x) = (M.op x x) := by
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
  have eq67 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq76 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  clear eq36
  have eq86 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op X2 (M.op X3 X1))) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X1 X1 X2 X3
       have i₂ := eq11 X0 X1
       grind)
    | (have i₁ := eq14 X0 X0 X2 X3
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq14
    | (have j1 := eq11 X0 X1
       grind)
    | exact resolve eq14 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) (M.op X3 (M.op X0 X0))) = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X1 X2 X3 X1
       have i₂ := eq11 X1 X0
       grind)
    | (have i₁ := eq14 X1 X1 X2 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq14
    | (have j1 := eq11 X1 X0
       grind)
    | exact resolve eq14 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq16
    | exact resolve eq16 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq16
    | exact resolve eq16 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq110 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X2 X2) ∨ (M.op X1 X2) = X1 ∨ (M.op X2 X2) = (k X2 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 X1
       have i₂ := eq11 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq12
    | (have j0 := eq12 X2 X1
       have j1 := eq11 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq12 X1 X0
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq11 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact resolve eq12 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 X1 X2 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X2) = X1 ∨ (M.op X0 X0) = (k X2 X1) ∨ (M.op X0 X2) = X0 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X1
       have i₂ := eq11 X0 X1
       grind)
    | (have i₁ := eq12 X0 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq11 X2 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq12 X1 X0
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq11 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact resolve eq12 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq115 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq115 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq115 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq118 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq116 (σ X0)
       grind)
    | exact superpose eq116 eq10
    | exact resolve eq10 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq116 x
       grind)
    | exact superpose eq116 eq43
    | exact resolve eq43 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq121 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq116 sF2
       grind)
    | exact superpose eq116 eq49
    | exact resolve eq49 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq122 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq121
       have i₂ := eq116 x
       grind)
    | exact superpose eq116 eq121
    | exact resolve eq121 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq124 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq119
       have i₂ := eq116 sF2
       grind)
    | exact superpose eq116 eq119
    | exact resolve eq119 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq125 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq118 X0
       have i₂ := eq116 X0
       grind)
    | exact superpose eq116 eq118
    | exact resolve eq118 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq128 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq103
       have i₂ := eq116 sF3
       grind)
    | exact superpose eq116 eq103
    | exact resolve eq103 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq129 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq128
       have i₂ := eq116 y
       grind)
    | exact superpose eq116 eq128
    | exact resolve eq128 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq138 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
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
  have eq139 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq140 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq139
       have i₂ := eq116 sF1
       grind)
    | exact superpose eq116 eq139
    | exact resolve eq139 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq143 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq140
       have i₂ := eq116 sF0
       grind)
    | exact superpose eq116 eq140
    | exact resolve eq140 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq140
  have eq157 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq138 eq16
    | exact resolve eq16 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq165 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq143 eq16
    | exact resolve eq16 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq268 : ∀ X2 X3 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X2 (M.op X3 (M.op (σ x) (σ y))))) := by
    intro X2 X3
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq351 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq582 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq56 (σ X0) (σ X0) x
       have i₂ := eq125 X0
       grind)
    | exact superpose eq125 eq56
    | exact resolve eq56 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq622 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq351 X0 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq351
    | (have j0 := eq351 X0 x
       grind)
    | exact resolve eq351 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351
  have eq653 : (k (M.op y y) x) = (τ (k (M.op (σ y) (σ y)) (σ x))) := by
    first
    | exact superpose eq129 eq622
    | exact resolve eq622 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622
  have eq714 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X0)) = (M.op X1 (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 X1 (M.op X2 X0) X3 (M.op X0 x)
       have i₂ := eq14 X0 x X1 X2
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq715 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op X1 y)) := by
    intro X0 X1
    first
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq716 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op X1 (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq54 eq52
    | exact resolve eq52 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq772 : ∀ X0 X1 X2 : G, (M.op X1 (σ y)) = (M.op X1 (M.op X2 (M.op X0 (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq716 eq52
    | exact resolve eq52 eq716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq887 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X2) = (M.op X3 (M.op X4 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 X3 X2 X4 (M.op (M.op X0 (M.op X1 X2)) x)
       have i₂ := eq55 X2 X0 X1 x X3
       grind)
    | exact superpose eq55 eq52
    | exact resolve eq52 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq1246 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq56 X1 X1 (M.op x (M.op x X0))
       have i₂ := eq86 X1 X0 x x
       grind)
    | exact superpose eq86 eq56
    | (have j1 := eq86 X1 X0 x x
       grind)
    | exact resolve eq56 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq86
  have eq1519 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X1 X1 (M.op X0 x) x
       have i₂ := eq90 X1 X0 x x
       grind)
    | exact superpose eq90 eq52
    | (have j1 := eq90 X1 X0 x x
       grind)
    | exact resolve eq52 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq2831 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq110 X1 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq2832 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2831 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2831
  have eq2944 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq112 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq2945 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2944 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2944
  have eq2946 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2945 X0 X1
       have j1 := eq13 X1 X0
       grind)
    | (have r₁ := eq2945 X1 X0
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq2945 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2945
  have eq5058 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) ∨ (σ (k X0 y)) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq40 eq2946
    | exact resolve eq2946 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq5234 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq2946 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9949 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq1246 x y
       grind)
    | exact superpose eq1246 eq75
    | (have j1 := eq1246 x y
       grind)
    | exact resolve eq75 eq1246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10135 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq9949
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9949
    | exact resolve eq9949 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9949
  have eq10198 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq20 eq10135
    | exact resolve eq10135 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10135
  have eq10232 : x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq10198
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq10198
    | exact resolve eq10198 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10198
  have eq10250 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq10232
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq10232
    | exact resolve eq10232 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10232
  have eq10615 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq75
       have i₂ := eq1519 y x
       grind)
    | exact superpose eq1519 eq75
    | (have j1 := eq1519 y x
       grind)
    | exact resolve eq75 eq1519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1519
  have eq10791 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq10615
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq10615
    | exact resolve eq10615 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10615
  have eq10866 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq10791
    | exact resolve eq10791 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10791
  have eq10896 : x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq10866
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq10866
    | exact resolve eq10866 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10866
  have eq10907 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq10896
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq10896
    | exact resolve eq10896 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10896
  have eq12323 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq2832 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2832
  have eq12338 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq12323 X0 X1
       have j1 := eq1246 X1 X0
       grind)
    | (have r₁ := eq12323 X1 (M.op X1 X1)
       have r₂ := eq1246 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq12323 X1 X0
       have r₂ := eq1246 X0 X1
       grind)
    | (have r₁ := eq12323 X0 X0
       have r₂ := eq1246 X0 X0
       grind)
    | exact resolve eq12323 eq1246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1246 eq12323
  have eq295622 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq10250 eq12338
    | (have j0 := eq12338 (σ y) (σ x)
       grind)
    | exact resolve eq12338 eq10250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10250
  have eq295627 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq295622
    | exact resolve eq295622 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295622
  have eq295651 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq295627
       have r₂ := eq27
       grind)
    | exact resolve eq295627 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295627
  have eq295668 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq295651
    | exact resolve eq295651 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295651
  have eq296952 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq10907 eq2946
    | exact resolve eq2946 eq10907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2946 eq10907
  have eq296961 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq296952
    | exact resolve eq296952 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296952
  have eq296983 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq296961
       have r₂ := eq27
       grind)
    | exact resolve eq296961 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296961
  have eq298827 : (τ (σ (M.op x y))) = (M.op x x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq296983 eq122
    | exact resolve eq122 eq296983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296983
  have eq299284 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq30 eq298827
    | exact resolve eq298827 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298827
  have eq299285 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq299284
  have eq299291 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq124
       have i₂ := eq299285
       grind)
    | exact superpose eq299285 eq124
    | exact resolve eq124 eq299285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq299563 : ∀ X0 X1 : G, x = (M.op (M.op x X0) (M.op X1 (M.op x y))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq14 x X0 X1 x
       have i₂ := eq299285
       grind)
    | exact superpose eq299285 eq14
    | exact resolve eq14 eq299285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299285
  have eq299742 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq299291
    | exact resolve eq299291 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299291
  have eq300124 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (σ (M.op x y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq299742 eq51
    | exact resolve eq51 eq299742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq300376 : ∀ X0 X1 : G, (σ x) = (M.op (σ (M.op x y)) (M.op X0 (M.op X1 (σ x)))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq299742 eq14
    | exact resolve eq14 eq299742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq300378 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (M.op X1 (σ (M.op x y))))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq299742 eq52
    | exact resolve eq52 eq299742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq300395 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ x))) = (M.op X0 (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq299742 eq714
    | exact resolve eq714 eq299742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714
  have eq311370 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) (σ (M.op x (M.op x y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq299563 eq582
    | exact resolve eq582 eq299563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299563
  have eq311413 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq582 y x
       have i₂ := eq295668
       grind)
    | exact superpose eq295668 eq582
    | exact resolve eq582 eq295668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582 eq295668
  have eq311922 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq311413 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq311413
    | (have j0 := eq311413 X0
       grind)
    | exact resolve eq311413 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq311413
  have eq311938 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) (σ (M.op x (M.op x y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq311370 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq311370
    | (have j0 := eq311370 X0
       grind)
    | exact resolve eq311370 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311370
  have eq311957 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq20 eq311922
    | (have j0 := eq311922 X0
       grind)
    | exact resolve eq311922 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311922
  have eq313085 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq300376 eq311957
    | exact resolve eq311957 eq300376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300376 eq311957
  have eq313491 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq313085
  have eq313502 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq313491
    | exact resolve eq313491 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313491
  have eq313504 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq313502
       have r₂ := eq27
       grind)
    | exact resolve eq313502 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313502
  have eq313507 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq313504 eq27
    | exact resolve eq27 eq313504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq313509 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ y) X0) (M.op X1 (σ x))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq313504 eq54
    | exact resolve eq54 eq313504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq313510 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq313504 eq67
    | (have r₁ := eq67
       have r₂ := eq313504
       grind)
    | exact resolve eq67 eq313504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq313576 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op X0 (σ (M.op x y)))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq313504 eq300124
    | exact resolve eq300124 eq313504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300124
  have eq313577 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op X0 (σ (M.op x y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq313576 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313576
  have eq313626 : (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq313510
  have eq314798 : (k y x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq313626 eq98
    | exact resolve eq98 eq313626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq313626
  have eq314892 : (k y x) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq122 eq314798
    | exact resolve eq314798 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq314798
  have eq314907 : (k y x) = (M.op x x) := by
    first
    | (have r₁ := eq314892
       have r₂ := eq66
       grind)
    | exact resolve eq314892 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq314892
  have eq314929 : (k (σ y) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq75
       have i₂ := eq314907
       grind)
    | exact superpose eq314907 eq75
    | exact resolve eq75 eq314907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq314907
  have eq314994 : (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq314929
       have i₂ := eq124
       grind)
    | exact superpose eq124 eq314929
    | exact resolve eq314929 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq314929
  have eq315096 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq314994 eq12338
    | (have j0 := eq12338 (σ y) (σ x)
       grind)
    | exact resolve eq12338 eq314994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314994
  have eq315099 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq315096
    | exact resolve eq315096 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315096
  have eq315119 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq315099
    | exact resolve eq315099 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq315099
  have eq315476 : ∀ X0 X1 X2 : G, (M.op X0 (σ x)) = (M.op X0 (M.op X1 (M.op X2 (M.op (σ x) (σ y))))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq315119 eq887
    | exact resolve eq887 eq315119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq315602 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq772 eq315476
    | exact resolve eq315476 eq772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315476
  have eq318060 : (M.op y y) = (τ (M.op (σ y) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq315602 eq129
    | exact resolve eq129 eq315602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq315602
  have eq322995 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq313509 eq300395
    | exact resolve eq300395 eq313509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300395 eq313509
  have eq323503 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq322995 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322995
  have eq323802 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq323503 eq300378
    | exact resolve eq300378 eq323503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300378 eq323503
  have eq323945 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq323802 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323802
  have eq324049 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq716 eq323945
    | (have j0 := eq323945 (σ x)
       grind)
    | exact resolve eq323945 eq716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323945
  have eq330507 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ x) X0) ∨ (σ (M.op x y)) = (k X0 (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq299742 eq5234
    | exact resolve eq5234 eq299742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5234
  have eq343371 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ (M.op x (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq268 eq311938
    | (have j0 := eq311938 (σ y)
       grind)
    | exact resolve eq311938 eq268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268 eq311938
  have eq345002 : (σ x) = (M.op (σ x) (σ (M.op x (M.op x y)))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq313504 eq343371
    | exact resolve eq343371 eq313504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313504 eq343371
  have eq345162 : (σ x) = (M.op (σ x) (σ (M.op x (M.op x y)))) ∨ x = (M.op x y) := by grind
  clear eq345002
  have eq345611 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (k (M.op X0 (σ y)) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq716 eq330507
    | (have j0 := eq330507 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq330507 eq716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716 eq330507
  have eq345708 : ∀ X0 : G, (σ (M.op x y)) = (k (M.op X0 (σ y)) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq345611 X0
       grind)
    | (have r₁ := eq345611 X0
       have r₂ := eq324049
       grind)
    | exact resolve eq345611 eq324049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324049 eq345611
  have eq345821 : (τ (σ (M.op x y))) = (k (M.op y y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq345708 eq653
    | exact resolve eq653 eq345708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653 eq345708
  have eq345880 : (M.op x y) = (k (M.op y y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq345821
    | exact resolve eq345821 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq345821
  have eq345956 : (M.op x y) = (M.op x (M.op y y)) ∨ x = (M.op x (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12338 (M.op y y) x
       have i₂ := eq345880
       grind)
    | exact superpose eq345880 eq12338
    | (have j0 := eq12338 (M.op y y) x
       grind)
    | exact resolve eq12338 eq345880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345880
  have eq345980 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq345956
       have i₂ := eq715 x y
       grind)
    | exact superpose eq715 eq345956
    | exact resolve eq345956 eq715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345956
  have eq346000 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq345980
       have i₂ := eq715 x y
       grind)
    | exact superpose eq715 eq345980
    | exact resolve eq345980 eq715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345980
  have eq347672 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq346000 eq345162
    | exact resolve eq345162 eq346000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346000
  have eq347865 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x (M.op x y)) := by grind
  clear eq347672
  have eq347905 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x (M.op x y)) := by
    first
    | exact superpose eq20 eq347865
    | exact resolve eq347865 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347865
  have eq348605 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x (M.op x y)) := by
    first
    | exact superpose eq347905 eq313577
    | exact resolve eq313577 eq347905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313577 eq347905
  have eq348761 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x (M.op x y)) := by grind
  clear eq348605
  have eq349824 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x (M.op x y)) := by
    first
    | exact superpose eq348761 eq299742
    | exact resolve eq299742 eq348761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348761
  have eq350288 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x (M.op x y)) := by grind
  clear eq349824
  have eq350343 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq350288
       have r₂ := eq313507
       grind)
    | exact resolve eq350288 eq313507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350288
  have eq350379 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq350343 eq345162
    | exact resolve eq345162 eq350343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345162 eq350343
  have eq350581 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq350379
  have eq350606 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq350581
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq350581
    | exact resolve eq350581 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350581
  have eq350881 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq350606 eq299742
    | exact resolve eq299742 eq350606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299742 eq350606
  have eq351345 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq350881
  have eq351400 : x = (M.op x y) := by
    first
    | (have r₁ := eq351345
       have r₂ := eq313507
       grind)
    | exact resolve eq351345 eq313507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313507 eq351345
  have eq351430 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq351400 eq20
    | exact resolve eq20 eq351400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq351621 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq351430
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq351430
    | exact resolve eq351430 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351430
  have eq351977 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq351621 eq315119
    | exact resolve eq315119 eq351621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315119
  have eq351988 : (M.op y y) = (τ (M.op (σ y) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq351621 eq318060
    | exact resolve eq318060 eq351621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318060
  have eq352009 : (M.op y y) = (τ (M.op (σ y) (σ (M.op x y)))) := by
    first
    | (have r₁ := eq351988
       have r₂ := eq27
       grind)
    | exact resolve eq351988 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351988
  have eq352019 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq351977
       have r₂ := eq27
       grind)
    | exact resolve eq351977 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351977
  have eq352435 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq352019 eq165
    | exact resolve eq165 eq352019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165
  have eq352741 : ∀ X0 X1 X2 : G, (M.op X0 (σ (M.op x y))) = (M.op X0 (M.op X1 (M.op X2 (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq352019 eq887
    | exact resolve eq887 eq352019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352019
  have eq352848 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq772 eq352741
    | exact resolve eq352741 eq772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772 eq352741
  have eq352864 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq351400 eq352435
    | exact resolve eq352435 eq351400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352435
  have eq364164 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) ∨ (σ (k X0 y)) = (M.op (σ y) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq352848 eq5058
    | (have j0 := eq5058 X0
       grind)
    | exact resolve eq5058 eq352848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5058 eq352848
  have eq364335 : (σ (k (M.op x y) y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (k (M.op x y) y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq364164
    | (have j0 := eq364164 (M.op x y)
       grind)
    | exact resolve eq364164 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq364164
  have eq364495 : (σ (k (M.op x y) y)) = (M.op (σ y) (σ (M.op x y))) := by grind
  clear eq364335
  have eq364523 : (k (σ (M.op x y)) (σ y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq138 eq364495
    | exact resolve eq364495 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138 eq364495
  have eq365336 : (k (M.op x y) y) = (τ (M.op (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq364523 eq157
    | exact resolve eq157 eq364523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157 eq364523
  have eq365348 : (M.op y y) = (k (M.op x y) y) := by
    first
    | exact superpose eq352009 eq365336
    | exact resolve eq365336 eq352009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352009 eq365336
  have eq365353 : (k x y) = (M.op y y) := by
    first
    | exact superpose eq351400 eq365348
    | exact resolve eq365348 eq351400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365348
  have eq365365 : (M.op y y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq365353
       have i₂ := eq12338 x y
       grind)
    | exact superpose eq12338 eq365353
    | (have j1 := eq12338 x y
       grind)
    | exact resolve eq365353 eq12338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12338 eq365353
  have eq382287 : ∀ X0 X1 X2 : G, (M.op X0 y) = (M.op X0 (M.op X1 (M.op X2 (M.op y x)))) ∨ y = (M.op y x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq887 X2 y y X0 X1
       have i₂ := eq365365
       grind)
    | exact superpose eq365365 eq887
    | exact resolve eq887 eq365365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365365
  have eq382415 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq382287 X0 x x
       have i₂ := eq887 x y x X0 x
       grind)
    | exact superpose eq887 eq382287
    | exact resolve eq382287 eq887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq887 eq382287
  have eq383102 : (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq382415 x
       grind)
    | exact superpose eq382415 eq18
    | (have j1 := eq382415 x
       grind)
    | exact resolve eq18 eq382415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq382415
  have eq383260 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq383102
       have i₂ := eq352864
       grind)
    | exact superpose eq352864 eq383102
    | exact resolve eq383102 eq352864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383102
  have eq383328 : y = (M.op y x) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq351400 eq383260
    | exact resolve eq383260 eq351400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383260
  have eq384733 : ∀ X0 : G, x = (M.op (M.op x y) (M.op X0 y)) ∨ x = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq50 X0 y
       have i₂ := eq383328
       grind)
    | exact superpose eq383328 eq50
    | exact resolve eq50 eq383328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq383328
  have eq384949 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq384733 x
       have i₂ := eq715 sF0 x
       grind)
    | (have i₁ := eq384733 x
       have i₂ := eq715 sF0 x
       grind)
    | exact superpose eq715 eq384733
    | (have j0 := eq384733 x
       grind)
    | exact resolve eq384733 eq715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715 eq384733
  have eq384991 : x = (M.op x x) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq351400 eq384949
    | exact resolve eq384949 eq351400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351400 eq384949
  have eq385021 : x = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq384991
       have i₂ := eq352864
       grind)
    | exact superpose eq352864 eq384991
    | exact resolve eq384991 eq352864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352864 eq384991
  have eq385022 : x = (τ (M.op (σ x) (σ y))) := by grind
  clear eq385021
  have eq385113 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq385022 eq15
    | exact resolve eq15 eq385022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385022
  have eq385241 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq385113
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq385113
    | exact resolve eq385113 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq385113
  have eq385299 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq351621 eq385241
    | exact resolve eq385241 eq351621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351621 eq385241
  have eq385352 : False := by grind
  exact eq385352

/-- `Equation1473`: `x = (x ◇ y) ◇ (z ◇ (w ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = m(X,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pxy_pyx_pyy_pyx_Equation1473 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1473 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1473.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
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
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X3 X0))) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq30 : ∀ X0 X1 X4 X5 : G, (M.op X0 X1) = (M.op X0 (M.op X4 (M.op X5 (M.op X0 X1)))) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq9 (M.op X0 X1) (M.op x (M.op x X0)) X4 X5
       have i₂ := eq9 X0 X1 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 X2 X4 : G, (M.op X2 (M.op X1 X0)) = (M.op X2 (M.op X4 X0)) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq30 X2 (M.op X1 X0) X4 (M.op X0 x)
       have i₂ := eq9 X0 x X2 X1
       grind)
    | exact superpose eq9 eq30
    | exact resolve eq30 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq77 : ∀ X0 X1 X2 X4 X5 : G, (M.op X4 X0) = (M.op X4 (M.op X5 (M.op X2 (M.op X1 X0)))) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq68 (M.op X2 (M.op X1 X0)) (M.op X0 x) X4 X5
       have i₂ := eq9 X0 x X2 X1
       grind)
    | exact superpose eq9 eq68
    | exact resolve eq68 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq199 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq203 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq234 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq203 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq235 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq234 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234
  have eq236 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq199 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq278 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X0) = (M.op X2 (M.op X3 (M.op X4 (M.op X0 X1)))) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq77 X0 X0 X4 X2 X3
       have i₂ := eq236 X0 X1
       grind)
    | (have i₁ := eq77 X1 X0 X2 X4 x
       have i₂ := eq236 X0 X1
       grind)
    | exact superpose eq236 eq77
    | (have j1 := eq236 X0 X1
       grind)
    | exact resolve eq77 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236
  have eq291 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq278 X0 X1 X2 x x
       have i₂ := eq77 X1 X0 x X2 x
       grind)
    | exact superpose eq77 eq278
    | (have j0 := eq278 X0 X1 X2 x x
       grind)
    | exact resolve eq278 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq278
  have eq646 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq235 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235
  have eq650 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq646 X0 X1
       have j1 := eq291 X0 X1 x
       grind)
    | (have r₁ := eq646 X0 X1
       have r₂ := eq291 X0 X1 X1
       grind)
    | (have r₁ := eq646 X1 X0
       have r₂ := eq291 X0 X1 X0
       grind)
    | exact resolve eq646 eq291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291 eq646
  have eq699 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  clear eq650
  have eq704 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq699 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699
  have eq718 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq704 (σ X0) (σ X1)
       grind)
    | exact superpose eq704 eq15
    | exact resolve eq15 eq704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq729 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq718 X0 X1
       have i₂ := eq704 X0 X1
       grind)
    | exact superpose eq704 eq718
    | exact resolve eq718 eq704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704 eq718
  have eq792 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq729 y x
       grind)
    | exact superpose eq729 eq16
    | (have r₁ := eq16
       have r₂ := eq729 y x
       grind)
    | exact resolve eq16 eq729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729
  have eq803 : False := by grind
  exact eq803

/-- `Equation1473`: `x = (x ◇ y) ◇ (z ◇ (w ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(X,Y) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_y_pxx_pyx_Equation1473 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1473 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1473.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X3 X0))) = X0 := by
    intro X0 X1 X2 X3
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
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
    | (have i₁ := eq23 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq23
    | exact resolve eq23 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    grind
  have eq43 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq37
    | exact resolve eq37 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq44 : ∀ X0 X1 X4 X5 : G, (M.op X0 X1) = (M.op X0 (M.op X4 (M.op X5 (M.op X0 X1)))) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq9 (M.op X0 X1) (M.op x (M.op x X0)) X4 X5
       have i₂ := eq9 X0 X1 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (k X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    grind
  have eq50 : ∀ X0 X1 X2 : G, (k (k X0 (τ X1)) (τ X2)) = (τ (k (k (σ X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30 (k X0 (τ X1)) X2
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq30
    | exact resolve eq30 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X3 X0)) (M.op X0 X1)) ≠ X0 ∨ (M.op X0 X1) = (M.op (M.op X2 (M.op X3 X0)) (M.op X2 (M.op X3 X0))) ∨ (k (M.op X0 X1) (M.op X2 (M.op X3 X0))) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 (M.op X0 X1) (M.op X2 (M.op X3 X0))
       have i₂ := eq9 X0 X1 X2 X3
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 (M.op X0 X1) (M.op X2 (M.op X3 X0))
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq107 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq107
    | (have j0 := eq107 (σ X0)
       grind)
    | exact resolve eq107 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq123 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X0)) = (M.op X1 (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq44 X1 (M.op X2 X0) X3 (M.op X0 x)
       have i₂ := eq9 X0 x X1 X2
       grind)
    | exact superpose eq9 eq44
    | exact resolve eq44 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132 : ∀ X0 X1 X3 X4 X5 : G, (M.op X1 X0) = (M.op X1 (M.op X5 (M.op X3 (M.op X4 X0)))) := by
    intro X0 X1 X3 X4 X5
    first
    | (have i₁ := eq123 (M.op X3 (M.op X4 X0)) X1 (M.op X0 x) X5
       have i₂ := eq9 X0 x X3 X4
       grind)
    | exact superpose eq9 eq123
    | exact resolve eq123 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X0)) X0) = (k (M.op X1 (M.op X2 X0)) (M.op (M.op X1 (M.op X2 X0)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq47 (M.op X2 (M.op x X0)) (M.op X0 X1)
       have i₂ := eq9 X0 X1 X2 x
       grind)
    | exact superpose eq9 eq47
    | exact resolve eq47 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq255 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq674 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq255 X1 X0
       grind)
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq255 X0 X1
       grind)
    | exact superpose eq255 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq255 X1 X0
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq255 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq255 X0 X1
       grind)
    | exact resolve eq13 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq676 : ∀ X0 X1 X2 X3 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (M.op X2 (M.op X3 (M.op (σ X0) (σ X1))))) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq44 (σ X1) (σ X0) x x
       have i₂ := eq255 X0 X1
       grind)
    | (have i₁ := eq44 (σ X0) (σ X1) x x
       have i₂ := eq255 X0 X1
       grind)
    | exact superpose eq255 eq44
    | (have j1 := eq255 X1 X0
       grind)
    | exact resolve eq44 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq686 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq674 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674
  have eq687 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq686 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686
  have eq692 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq676 X0 X1 x x
       have i₂ := eq132 (σ X1) (σ X1) x (σ X0) x
       grind)
    | exact superpose eq132 eq676
    | (have j0 := eq676 X0 X1 x x
       grind)
    | exact resolve eq676 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq676
  have eq694 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq687 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq687
    | (have j0 := eq687 X0 X1
       grind)
    | exact resolve eq687 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687
  have eq1041 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) ≠ (M.op (M.op X1 (M.op X2 (M.op X0 X3))) X0) ∨ (M.op (M.op X1 (M.op X2 (M.op X0 X3))) (M.op X1 (M.op X2 (M.op X0 X3)))) = X0 ∨ (M.op X0 X0) = (k X0 (M.op X1 (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq103 (M.op X0 X1) (M.op X2 (M.op X3 X0)) X2 X3
       have i₂ := eq9 X0 X1 X2 X3
       grind)
    | exact superpose eq9 eq103
    | (have r₁ := eq103 X0 (M.op X3 X0) X0 X3
       have r₂ := eq9 X0 (M.op X3 X0) X0 X3
       grind)
    | exact resolve eq103 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq1065 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) ≠ (M.op (M.op X1 (M.op X2 (M.op X0 X3))) X0) ∨ (M.op (M.op X1 (M.op X2 (M.op X0 X3))) X3) = X0 ∨ (M.op X0 X0) = (k X0 (M.op X1 (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1041 X0 X1 X2 X3
       have i₂ := eq132 X3 (M.op X1 (M.op X2 (M.op X0 X3))) X2 X0 X1
       grind)
    | exact superpose eq132 eq1041
    | (have j0 := eq1041 X0 X1 X2 X3
       grind)
    | exact resolve eq1041 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1041
  have eq1234 : ∀ X0 : G, (k (τ (σ (k X0 X0))) X0) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq43 X0
       have i₂ := eq108 X0
       grind)
    | exact superpose eq108 eq43
    | (have j1 := eq108 X0
       grind)
    | exact resolve eq43 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1238 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ (k X0 X0)) (M.op X1 (M.op X2 (σ X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) (σ X0) X1 X2
       have i₂ := eq108 X0
       grind)
    | exact superpose eq108 eq9
    | (have j1 := eq108 X0
       grind)
    | exact resolve eq9 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1258 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq108 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq1264 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1234 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq1234
    | (have j0 := eq1234 X0
       grind)
    | exact resolve eq1234 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1234
  have eq1313 : ∀ X0 : G, (k (τ (σ X0)) X0) = X0 ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq43 X0
       have i₂ := eq1264 X0
       grind)
    | exact superpose eq1264 eq43
    | (have j1 := eq1264 X0
       grind)
    | exact resolve eq43 eq1264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1316 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ X0)) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    grind
  clear eq1264
  have eq1335 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1316 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq1316
    | (have j0 := eq1316 X0
       grind)
    | exact resolve eq1316 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1316
  have eq1338 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1313 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1313
    | (have j0 := eq1313 X0
       grind)
    | exact resolve eq1313 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1313
  have eq1417 : ∀ X0 : G, (τ (σ X0)) = (k (k X0 (τ (σ X0))) (τ (σ X0))) ∨ (σ (σ X0)) = (σ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq50 X0 (σ X0) (σ X0)
       have i₂ := eq1335 (σ X0)
       grind)
    | exact superpose eq1335 eq50
    | (have j1 := eq1335 (σ X0)
       grind)
    | exact resolve eq50 eq1335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq1335
  have eq1439 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (σ (σ X0)) = (σ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq1417 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1417
    | (have j0 := eq1417 X0
       grind)
    | exact resolve eq1417 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1417
  have eq1455 : ∀ X0 : G, (σ (σ X0)) = (σ (σ (k X0 X0))) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1439 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq1439
    | (have j0 := eq1439 X0
       grind)
    | exact resolve eq1439 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1439
  have eq2336 : ∀ X0 X1 : G, (τ (k (σ (σ X0)) X1)) = (k (σ (k X0 X0)) (τ X1)) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq30 (σ (k X0 X0)) X1
       have i₂ := eq1455 X0
       grind)
    | exact superpose eq1455 eq30
    | (have j1 := eq1455 X0
       grind)
    | exact resolve eq30 eq1455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1455
  have eq2354 : ∀ X0 X1 : G, (k (σ X0) (τ X1)) = (k (σ (k X0 X0)) (τ X1)) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2336 X0 X1
       have i₂ := eq30 (σ X0) X1
       grind)
    | exact superpose eq30 eq2336
    | (have j0 := eq2336 X0 X1
       grind)
    | exact resolve eq2336 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2336
  have eq5433 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq692 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692
  have eq5439 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq5433 X0 X1
       have j1 := eq694 X0 X1
       grind)
    | (have r₁ := eq5433 X0 X1
       have r₂ := eq694 X0 X1
       grind)
    | (have r₁ := eq5433 X0 X0
       have r₂ := eq694 X0 (k X0 X0)
       grind)
    | (have r₁ := eq5433 X0 X0
       have r₂ := eq694 X0 X0
       grind)
    | exact resolve eq5433 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694 eq5433
  have eq5459 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5439 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5439
    | exact resolve eq5439 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5506 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5439 x y
       grind)
    | exact superpose eq5439 eq16
    | (have j1 := eq5439 x y
       grind)
    | exact resolve eq16 eq5439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5533 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (σ X0))) = (M.op X2 (σ (k X0 X1))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq123 (σ X0) X2 X3 (σ X1)
       have i₂ := eq5439 X1 X0
       grind)
    | exact superpose eq5439 eq123
    | (have j1 := eq5439 X1 X0
       grind)
    | exact resolve eq123 eq5439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5560 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5459 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq5459
    | (have j0 := eq5459 X0 X1
       grind)
    | exact resolve eq5459 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq5459
  have eq5573 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5560 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5560
    | exact resolve eq5560 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5602 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X1 X0
       have i₂ := eq5560 X0 X1
       grind)
    | exact superpose eq5560 eq30
    | (have j1 := eq5560 X0 X1
       grind)
    | exact resolve eq30 eq5560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5560
  have eq5784 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq5573 (τ X1) X0
       grind)
    | exact superpose eq5573 eq18
    | (have j1 := eq5573 (τ X1) X0
       grind)
    | exact resolve eq18 eq5573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq5850 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5602 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5602
    | exact resolve eq5602 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5602
  have eq5921 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5850 X0 X1
       have i₂ := eq34 X1 X0
       grind)
    | exact superpose eq34 eq5850
    | (have j0 := eq5850 X0 X1
       grind)
    | exact resolve eq5850 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5850
  have eq5993 : ∀ X0 X1 X2 : G, (τ (k X2 (k X1 X0))) = (k (τ X2) (τ (M.op X0 X1))) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34 (k X1 X0) X2
       have i₂ := eq5921 X1 X0
       grind)
    | exact superpose eq5921 eq34
    | (have j1 := eq5921 X1 X0
       grind)
    | exact resolve eq34 eq5921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5921
  have eq6011 : ∀ X0 X1 X2 : G, (τ (k X2 (k X1 X0))) = (τ (k X2 (M.op X0 X1))) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5993 X0 X1 X2
       have i₂ := eq34 (M.op X0 X1) X2
       grind)
    | exact superpose eq34 eq5993
    | (have j0 := eq5993 X0 X1 X2
       grind)
    | exact resolve eq5993 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5993
  have eq6024 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5784 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5784
    | exact resolve eq5784 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5784
  have eq6096 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6024 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq6024
    | (have j0 := eq6024 X0 X1
       grind)
    | exact resolve eq6024 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6024
  have eq6210 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq5506
       have i₂ := eq5573 y x
       grind)
    | exact superpose eq5573 eq5506
    | (have j1 := eq5573 (σ y) (σ x)
       grind)
    | exact resolve eq5506 eq5573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5506
  have eq6215 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq6210
  have eq6216 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (σ (k x x)) := by
    first
    | (have i₁ := eq6215
       have i₂ := eq5439 x x
       grind)
    | exact superpose eq5439 eq6215
    | (have j1 := eq5439 x x
       grind)
    | exact resolve eq6215 eq5439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5439
  have eq6226 : x = (k (τ (σ y)) x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq43 x
       have i₂ := eq6215
       grind)
    | exact superpose eq6215 eq43
    | exact resolve eq43 eq6215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq6246 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op X1 (σ x))) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq123 (σ x) X0 X1 (σ x)
       have i₂ := eq6215
       grind)
    | exact superpose eq6215 eq123
    | exact resolve eq123 eq6215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6215
  have eq6264 : y = (M.op x x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq6226
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq6226
    | exact resolve eq6226 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6226
  have eq6267 : x = (k y x) ∨ x = (k y x) := by grind
  clear eq6264
  have eq6295 : x = (k y x) := by grind
  clear eq6267
  have eq6299 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq6096 y x
       have i₂ := eq6295
       grind)
    | exact superpose eq6295 eq6096
    | (have j0 := eq6096 y x
       grind)
    | exact resolve eq6096 eq6295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6096
  have eq6334 : ∀ X0 : G, (k (τ X0) (M.op x y)) = (τ (k X0 (σ x))) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq23 X0 (M.op x y)
       have i₂ := eq6299
       grind)
    | exact superpose eq6299 eq23
    | exact resolve eq23 eq6299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6335 : ∀ X0 : G, (k (M.op x y) (τ X0)) = (τ (k (σ x) X0)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq30 (M.op x y) X0
       have i₂ := eq6299
       grind)
    | exact superpose eq6299 eq30
    | exact resolve eq30 eq6299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6364 : ∀ X0 : G, (k (M.op x y) (τ X0)) = (k x (τ X0)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq6335 X0
       have i₂ := eq30 x X0
       grind)
    | exact superpose eq30 eq6335
    | exact resolve eq6335 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq6335
  have eq6365 : ∀ X0 : G, (k (τ X0) (M.op x y)) = (k (τ X0) x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq6334 X0
       have i₂ := eq23 X0 x
       grind)
    | exact superpose eq23 eq6334
    | exact resolve eq6334 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6334
  have eq7126 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op X1 X2)) ≠ (M.op (M.op X4 (M.op X5 (M.op X0 (M.op X1 X2)))) X0) ∨ (M.op (M.op X4 (M.op X5 (M.op X0 (M.op X1 X2)))) (M.op X3 X2)) = X0 ∨ (M.op X0 X0) = (k X0 (M.op X4 (M.op X5 (M.op X0 (M.op X1 X2))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq1065 X1 X1 X2 (M.op X2 X0)
       have i₂ := eq123 X0 X1 X2 X3
       grind)
    | (have i₁ := eq1065 X1 X1 X2 (M.op X3 X0)
       have i₂ := eq123 X0 X1 X2 X3
       grind)
    | exact superpose eq123 eq1065
    | (have j0 := eq1065 X0 X4 X5 (M.op X1 X2)
       grind)
    | exact resolve eq1065 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1065
  have eq7221 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op X1 X2)) ≠ (M.op (M.op X4 X2) X0) ∨ (M.op (M.op X4 (M.op X5 (M.op X0 (M.op X1 X2)))) (M.op X3 X2)) = X0 ∨ (M.op X0 X0) = (k X0 (M.op X4 (M.op X5 (M.op X0 (M.op X1 X2))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq7126 X0 X1 X2 X3 X4 X5
       have i₂ := eq132 X2 X4 X0 X1 X5
       grind)
    | exact superpose eq132 eq7126
    | (have j0 := eq7126 X0 X1 X2 X3 X4 X5
       grind)
    | exact resolve eq7126 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7126
  have eq7230 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X2) (M.op X3 X2)) = X0 ∨ (M.op X0 (M.op X1 X2)) ≠ (M.op (M.op X4 X2) X0) ∨ (M.op X0 X0) = (k X0 (M.op X4 (M.op X5 (M.op X0 (M.op X1 X2))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq7221 X0 X1 X2 X3 X4 X5
       have i₂ := eq132 X2 X4 X0 X1 X5
       grind)
    | exact superpose eq132 eq7221
    | (have j0 := eq7221 X0 X1 X2 X3 X4 X5
       grind)
    | exact resolve eq7221 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7221
  have eq7239 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X2)) ≠ (M.op (M.op X4 X2) X0) ∨ (M.op (M.op X4 X2) (M.op X3 X2)) = X0 ∨ (M.op X0 X0) = (k X0 (M.op X4 X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq7230 X0 X1 X2 X3 X4 x
       have i₂ := eq132 X2 X4 X0 X1 x
       grind)
    | exact superpose eq132 eq7230
    | (have j0 := eq7230 X0 X1 X2 X3 X4 x
       grind)
    | exact resolve eq7230 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7230
  have eq7350 : ∀ X0 : G, (k x X0) = (k (M.op x y) X0) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq6364 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6364
    | exact resolve eq6364 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6364
  have eq7471 : ∀ X0 : G, (k X0 (M.op x y)) = (k X0 x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq6365 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6365
    | exact resolve eq6365 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6365
  have eq7585 : (k x (M.op x y)) = (k (M.op x y) x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq7350 (M.op x y)
       have i₂ := eq7471 (M.op x y)
       grind)
    | exact superpose eq7471 eq7350
    | exact resolve eq7350 eq7471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7350
  have eq7634 : (k x (M.op x y)) = (k (M.op x y) x) ∨ y = (M.op x x) := by grind
  clear eq7585
  have eq20335 : ∀ X0 X1 X2 : G, (k X0 (k X2 X1)) = (σ (τ (k X0 (M.op X1 X2)))) ∨ (M.op X1 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 (k X0 (k X2 X1))
       have i₂ := eq6011 X1 X2 X0
       grind)
    | exact superpose eq6011 eq11
    | (have j1 := eq6011 X1 X2 X2
       grind)
    | exact resolve eq11 eq6011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6011
  have eq20374 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 X2)) = (k X0 (k X2 X1)) ∨ (M.op X1 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20335 X0 X1 X2
       have i₂ := eq11 (k X0 (M.op X1 X2))
       grind)
    | exact superpose eq11 eq20335
    | (have j0 := eq20335 X0 X1 X2
       grind)
    | exact resolve eq20335 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20335
  have eq91237 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (k (M.op X0 X1) (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq7239 (M.op X0 X1) X1 X1 X2 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7239
  have eq116066 : ∀ X0 X1 : G, (k (σ X1) X0) = (k (σ (k X1 X1)) X0) ∨ (k (k X1 X1) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2354 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2354
    | (have j0 := eq2354 X1 X1
       grind)
    | exact resolve eq2354 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2354
  have eq116737 : ∀ X0 X1 : G, (τ (k (σ X0) (σ X1))) = (k (τ (σ (k X0 X0))) X1) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq23 (σ (k X0 X0)) X1
       have i₂ := eq116066 (σ X1) X0
       grind)
    | exact superpose eq116066 eq23
    | (have j1 := eq116066 X0 X0
       grind)
    | exact resolve eq23 eq116066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116066
  have eq116847 : ∀ X0 X1 : G, (τ (k (σ X0) (σ X1))) = (k (k X0 X0) X1) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq116737 X0 X1
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq116737
    | (have j0 := eq116737 X0 X1
       grind)
    | exact resolve eq116737 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116737
  have eq117115 : ∀ X0 X1 : G, (k (τ (σ X0)) X1) = (k (k X0 X0) X1) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq116847 X0 X1
       have i₂ := eq23 (σ X0) X1
       grind)
    | exact superpose eq23 eq116847
    | (have j0 := eq116847 X0 X1
       grind)
    | exact resolve eq116847 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq116847
  have eq117289 : ∀ X0 X1 : G, (k X0 X1) = (k (k X0 X0) X1) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq117115 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq117115
    | (have j0 := eq117115 X0 X1
       grind)
    | exact resolve eq117115 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117115
  have eq118038 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq117289 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117289
  have eq118044 : ∀ X0 : G, (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq118038 X0
       have j1 := eq1338 X0
       grind)
    | (have r₁ := eq118038 X0
       have r₂ := eq1338 X0
       grind)
    | exact resolve eq118038 eq1338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1338 eq118038
  have eq118252 : (M.op x y) = (k (k (M.op x y) x) (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq118044 (M.op x y)
       have i₂ := eq7471 (M.op x y)
       grind)
    | exact superpose eq7471 eq118044
    | exact resolve eq118044 eq7471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118323 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq118044 X0
       have i₂ := eq5573 (k X0 X0) X0
       grind)
    | exact superpose eq5573 eq118044
    | (have j1 := eq5573 X0 X0
       grind)
    | exact resolve eq118044 eq5573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5573
  have eq118383 : ∀ X0 X1 : G, (k X1 X0) = (k X1 (M.op X0 (k X0 X0))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq20374 X1 X0 (k X0 X0)
       have i₂ := eq118044 X0
       grind)
    | exact superpose eq118044 eq20374
    | (have j0 := eq20374 X0 X0 (k X0 X0)
       grind)
    | exact resolve eq20374 eq118044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118044
  have eq118854 : ∀ X0 X1 X2 : G, (k X0 X0) = (M.op (M.op (k X0 X0) X1) (M.op X2 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (k X0 X0) X1 X2 X0
       have i₂ := eq118323 X0
       grind)
    | exact superpose eq118323 eq9
    | (have j1 := eq118323 X0
       grind)
    | exact resolve eq9 eq118323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118866 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 (M.op X2 (k X0 X0))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq123 (k X0 X0) X1 X2 X0
       have i₂ := eq118323 X0
       grind)
    | exact superpose eq118323 eq123
    | (have j1 := eq118323 X0
       grind)
    | exact resolve eq123 eq118323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118868 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op X3 X0))) = (M.op X1 (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq132 (k X0 X0) X1 X3 X0 X2
       have i₂ := eq118323 X0
       grind)
    | exact superpose eq118323 eq132
    | (have j1 := eq118323 X0
       grind)
    | exact resolve eq132 eq118323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq122717 : (M.op x y) = (k (k (M.op x y) x) x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq7471 (k (M.op x y) x)
       have i₂ := eq118252
       grind)
    | exact superpose eq118252 eq7471
    | exact resolve eq7471 eq118252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7471 eq118252
  have eq122732 : (M.op x y) = (k (k (M.op x y) x) x) ∨ y = (M.op x x) := by grind
  clear eq122717
  have eq122740 : (M.op x y) = (k (k x (M.op x y)) x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq122732
       have i₂ := eq7634
       grind)
    | exact superpose eq7634 eq122732
    | exact resolve eq122732 eq7634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7634 eq122732
  have eq122765 : (M.op x y) = (k (k x (M.op x y)) x) ∨ y = (M.op x x) := by grind
  clear eq122740
  have eq129160 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (σ (k x x)) := by grind
  clear eq6216
  have eq129247 : (σ y) = (σ (k x x)) ∨ y = (M.op x x) ∨ (σ x) = (σ (k x x)) := by
    first
    | (have i₁ := eq129160
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq129160
    | exact resolve eq129160 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129160
  have eq186354 : (k x x) = (τ (σ y)) ∨ y = (M.op x x) ∨ (σ x) = (σ (k x x)) := by
    first
    | (have i₁ := eq10 (k x x)
       have i₂ := eq129247
       grind)
    | exact superpose eq129247 eq10
    | exact resolve eq10 eq129247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129247
  have eq186491 : (σ x) = (σ (k x x)) ∨ y = (M.op x x) ∨ y = (k x x) := by
    first
    | (have i₁ := eq186354
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq186354
    | exact resolve eq186354 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186354
  have eq186944 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (k x x) := by
    first
    | (have i₁ := eq1258 x
       have i₂ := eq186491
       grind)
    | exact superpose eq186491 eq1258
    | (have j0 := eq1258 x
       grind)
    | (have r₁ := eq1258 x
       have r₂ := eq186491
       grind)
    | exact resolve eq1258 eq186491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1258 eq186491
  have eq187062 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (k x x) := by grind
  clear eq186944
  have eq187131 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x x) ∨ y = (k x x) := by
    intro X0
    first
    | (have i₁ := eq6246 X0 (σ x)
       have i₂ := eq187062
       grind)
    | exact superpose eq187062 eq6246
    | exact resolve eq6246 eq187062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6246
  have eq187230 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ y = (M.op x x) ∨ y = (k x x) := by
    intro X0
    first
    | (have j0 := eq187131 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187131
  have eq187996 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (k x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq187230 (σ x)
       grind)
    | exact superpose eq187230 eq16
    | exact resolve eq16 eq187230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187230
  have eq497101 : ∀ X0 X1 X2 X3 : G, (k X3 X0) = (k X3 (M.op X0 (M.op X1 (M.op X2 X0)))) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq118383 X0 X3
       have i₂ := eq118868 X0 X0 X1 X2
       grind)
    | exact superpose eq118868 eq118383
    | (have j0 := eq118383 X0 X1
       have j1 := eq118868 X0 X1 X2 X3
       grind)
    | exact resolve eq118383 eq118868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118383 eq118868
  have eq497450 : ∀ X0 X1 X2 X3 : G, (k X3 X0) = (k X3 (M.op X0 (M.op X1 (M.op X2 X0)))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq497101 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497101
  have eq515709 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x x) ∨ y = (k x x) ∨ y = (M.op x x) ∨ y = (k x x) := by
    first
    | (have i₁ := eq187996
       have i₂ := eq187062
       grind)
    | exact superpose eq187062 eq187996
    | exact resolve eq187996 eq187062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187062 eq187996
  have eq515721 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x x) ∨ y = (k x x) := by grind
  clear eq515709
  have eq515726 : y = (k x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq515721
       have r₂ := eq6299
       grind)
    | exact resolve eq515721 eq6299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6299 eq515721
  have eq516100 : ∀ X0 X1 : G, y = (M.op (M.op y X0) (M.op X1 x)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq118854 x X1 x
       have i₂ := eq515726
       grind)
    | exact superpose eq515726 eq118854
    | exact resolve eq118854 eq515726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118854
  have eq516102 : ∀ X0 X1 : G, (M.op X0 (M.op X1 y)) = (M.op X0 x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq118866 x X1 x
       have i₂ := eq515726
       grind)
    | exact superpose eq515726 eq118866
    | exact resolve eq118866 eq515726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118866
  have eq516164 : ∀ X0 X1 : G, (M.op X0 (M.op X1 y)) = (M.op X0 x) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have j0 := eq516102 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516102
  have eq516166 : ∀ X0 X1 : G, y = (M.op (M.op y X0) (M.op X1 x)) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have j0 := eq516100 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516100
  have eq686433 : ∀ X0 X1 X2 X3 : G, (M.op X2 (σ (τ (k X0 X1)))) = (M.op X2 (M.op X3 (σ (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq5533 (τ X0) (τ X1) X2 X3
       have i₂ := eq34 X1 X0
       grind)
    | exact superpose eq34 eq5533
    | (have j0 := eq5533 (τ X0) (τ X1) X2 X3
       grind)
    | exact resolve eq5533 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq5533
  have eq688259 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op X2 (σ (τ (k X0 X1)))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq686433 X0 X1 X2 X3
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq686433
    | (have j0 := eq686433 X0 X1 X2 X3
       grind)
    | exact resolve eq686433 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686433
  have eq688533 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op X2 (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq688259 X0 X1 X2 X3
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq688259
    | (have j0 := eq688259 X0 X1 X2 X3
       grind)
    | exact resolve eq688259 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688259
  have eq688693 : ∀ X0 X1 X2 X3 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (M.op X2 (M.op X3 X0)) = (M.op X2 (k X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq688533 X0 X0 X2 X3
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq688533
    | (have j0 := eq688533 X0 X1 X2 X3
       grind)
    | exact resolve eq688533 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688533
  have eq688740 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op X2 (k X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq688693 X0 X1 X2 X3
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq688693
    | (have j0 := eq688693 X0 X1 X2 X3
       grind)
    | exact resolve eq688693 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688693
  have eq690901 : ∀ X0 X1 X2 : G, (k X0 X1) = (k (M.op (k X0 X1) (M.op X2 X0)) (k X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    grind
  clear eq688740
  have eq991341 : ∀ X0 X1 X2 : G, (k X0 X1) = (k (M.op (k X0 X1) (M.op X2 X0)) (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20374 (M.op (k X0 X1) (M.op X2 X0)) X1 X0
       have i₂ := eq690901 X0 X1 X2
       grind)
    | exact superpose eq690901 eq20374
    | (have j0 := eq20374 X0 X1 X0
       have j1 := eq690901 X0 X1 X2
       grind)
    | exact resolve eq20374 eq690901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20374 eq690901
  have eq991489 : ∀ X0 X1 X2 : G, (k X0 X1) = (k (M.op (k X0 X1) (M.op X2 X0)) (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq991341 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq991341
  have eq1060507 : ∀ X0 : G, x = (k (M.op x (M.op X0 y)) (M.op x y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq991489 y x x
       have i₂ := eq6295
       grind)
    | exact superpose eq6295 eq991489
    | (have j0 := eq991489 y x x
       grind)
    | exact resolve eq991489 eq6295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6295 eq991489
  have eq1268401 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 (M.op X1 (k X0 X0))) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq91237 X0 (k X0 X0) x
       have i₂ := eq118323 X0
       grind)
    | exact superpose eq118323 eq91237
    | (have j1 := eq118323 X0
       grind)
    | exact resolve eq91237 eq118323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91237
  have eq1269296 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (k X0 X0))) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1268401 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1268401
  have eq1269720 : ∀ X0 : G, x = (M.op x (M.op X0 y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq1269296 x x
       have i₂ := eq515726
       grind)
    | exact superpose eq515726 eq1269296
    | exact resolve eq1269296 eq515726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1269840 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op X1 (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq44 X1 (k X0 X0) X2 X0
       have i₂ := eq1269296 X0 X1
       grind)
    | exact superpose eq1269296 eq44
    | (have j1 := eq1269296 X0 X1
       grind)
    | exact resolve eq44 eq1269296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1269296
  have eq1270422 : ∀ X0 : G, x = (M.op x (M.op X0 y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq1269720 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1269720
  have eq1284126 : x = (k x (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1060507 x
       have i₂ := eq1270422 x
       grind)
    | exact superpose eq1270422 eq1060507
    | exact resolve eq1060507 eq1270422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1060507
  have eq1284185 : ∀ X0 : G, y = (M.op (M.op y X0) x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq9 y X0 x x
       have i₂ := eq1270422 x
       grind)
    | exact superpose eq1270422 eq9
    | exact resolve eq9 eq1270422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1270422
  have eq1284568 : x = (k x (M.op x y)) ∨ y = (M.op x x) := by grind
  clear eq1284126
  have eq1298374 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq516166 X0 (M.op y x)
       have i₂ := eq1284185 x
       grind)
    | exact superpose eq1284185 eq516166
    | exact resolve eq516166 eq1284185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516166 eq1284185
  have eq1298676 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq1298374 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1298374
  have eq1300982 : (M.op x y) = (k x x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq122765
       have i₂ := eq1284568
       grind)
    | exact superpose eq1284568 eq122765
    | exact resolve eq122765 eq1284568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122765 eq1284568
  have eq1301140 : (M.op x y) = (k x x) ∨ y = (M.op x x) := by grind
  clear eq1300982
  have eq1313553 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq516164 X0 (M.op y x)
       have i₂ := eq1298676 x
       grind)
    | exact superpose eq1298676 eq516164
    | exact resolve eq516164 eq1298676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516164 eq1298676
  have eq1313887 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq1313553 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1313553
  have eq1314227 : y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq515726
       have i₂ := eq1301140
       grind)
    | exact superpose eq1301140 eq515726
    | exact resolve eq515726 eq1301140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515726 eq1301140
  have eq1314751 : y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq1314227
  have eq1324788 : y = (M.op x x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1314751
       have i₂ := eq1313887 x
       grind)
    | exact superpose eq1313887 eq1314751
    | exact resolve eq1314751 eq1313887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1313887 eq1314751
  have eq1324858 : y = (M.op x x) := by grind
  clear eq1324788
  have eq1325548 : ∀ X0 X1 : G, x = (M.op (M.op x X0) (M.op X1 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 x X0 X1 x
       have i₂ := eq1324858
       grind)
    | exact superpose eq1324858 eq9
    | exact resolve eq9 eq1324858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1325551 : ∀ X0 X1 : G, y = (M.op x (M.op X0 (M.op X1 y))) := by
    intro X0 X1
    first
    | (have i₁ := eq44 x x x x
       have i₂ := eq1324858
       grind)
    | exact superpose eq1324858 eq44
    | exact resolve eq44 eq1324858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq1325562 : ∀ X0 X1 : G, (M.op X0 (M.op X1 x)) = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq123 x X0 X1 x
       have i₂ := eq1324858
       grind)
    | exact superpose eq1324858 eq123
    | exact resolve eq123 eq1324858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2432278 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq118323 X0
       have i₂ := eq1269840 X0 X0 X1
       grind)
    | exact superpose eq1269840 eq118323
    | (have j0 := eq118323 X0
       have j1 := eq1269840 X0 X1 x
       grind)
    | exact resolve eq118323 eq1269840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118323 eq1269840
  have eq2433150 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2432278 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2432278
  have eq2435919 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq180 X0 X0 x
       have i₂ := eq2433150 X0 x
       grind)
    | exact superpose eq2433150 eq180
    | (have j1 := eq2433150 X0 x
       grind)
    | exact resolve eq180 eq2433150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq2436027 : ∀ X0 X1 : G, (k X1 X0) = (k X1 (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq497450 X0 X0 x X1
       have i₂ := eq2433150 X0 x
       grind)
    | exact superpose eq2433150 eq497450
    | (have j0 := eq497450 X0 X1 x x
       have j1 := eq2433150 X0 X1
       grind)
    | exact resolve eq497450 eq2433150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497450 eq2433150
  have eq2436882 : ∀ X0 X1 : G, (k X1 X0) = (k X1 (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2436027 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2436027
  have eq2475601 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq2435919 X0
       have i₂ := eq2436882 X0 X0
       grind)
    | exact superpose eq2436882 eq2435919
    | (have j0 := eq2435919 X0
       have j1 := eq2436882 X0 x
       grind)
    | exact resolve eq2435919 eq2436882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2435919 eq2436882
  have eq2476913 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq2475601 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2475601
  have eq2479305 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq2476913 (σ X0)
       grind)
    | exact superpose eq2476913 eq15
    | exact resolve eq15 eq2476913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2481016 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2479305 X0
       have i₂ := eq2476913 X0
       grind)
    | exact superpose eq2476913 eq2479305
    | exact resolve eq2479305 eq2476913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2479305
  have eq2485753 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (σ X0))) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq123 (σ X0) X1 X2 (σ X0)
       have i₂ := eq2481016 X0
       grind)
    | exact superpose eq2481016 eq123
    | exact resolve eq123 eq2481016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq2502230 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op X1 (σ (M.op x y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq2485753 (M.op x y) X0 X1
       have i₂ := eq1325548 y x
       grind)
    | exact superpose eq1325548 eq2485753
    | exact resolve eq2485753 eq1325548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2502345 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op X1 (σ x))) := by
    intro X0 X1
    first
    | (have i₁ := eq2485753 x X0 X1
       have i₂ := eq1324858
       grind)
    | exact superpose eq1324858 eq2485753
    | exact resolve eq2485753 eq1324858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1324858 eq2485753
  have eq2527369 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (k (M.op x y) (M.op x y))) (M.op X0 (σ x))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq1238 (M.op x y) X0 x
       have i₂ := eq2502230 X0 x
       grind)
    | exact superpose eq2502230 eq1238
    | (have j0 := eq1238 (M.op x y) x x
       grind)
    | exact resolve eq1238 eq2502230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1238 eq2502230
  have eq2528652 : (σ (M.op x y)) = (M.op (σ (k (M.op x y) (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq2527369 x
       have i₂ := eq2502345 (σ (k (M.op x y) (M.op x y))) x
       grind)
    | exact superpose eq2502345 eq2527369
    | exact resolve eq2527369 eq2502345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2502345 eq2527369
  have eq2529046 : (σ (M.op x y)) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq2528652
       have i₂ := eq2476913 (M.op x y)
       grind)
    | exact superpose eq2476913 eq2528652
    | exact resolve eq2528652 eq2476913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2476913 eq2528652
  have eq2529334 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq2529046
       have i₂ := eq1325548 y x
       grind)
    | exact superpose eq1325548 eq2529046
    | exact resolve eq2529046 eq1325548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2529046
  have eq2529559 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq2529334
       have r₂ := eq16
       grind)
    | exact resolve eq2529334 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2529334
  have eq2529739 : (σ (M.op x y)) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq2529559
       have i₂ := eq2481016 (M.op x y)
       grind)
    | exact superpose eq2481016 eq2529559
    | exact resolve eq2529559 eq2481016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2529559
  have eq2529870 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2529739
       have i₂ := eq1325548 y x
       grind)
    | exact superpose eq1325548 eq2529739
    | exact resolve eq2529739 eq1325548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1325548 eq2529739
  have eq2530045 : (M.op x y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq2529870
       grind)
    | exact superpose eq2529870 eq10
    | exact resolve eq10 eq2529870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2529870
  have eq2531347 : x = (M.op x y) := by
    first
    | (have i₁ := eq2530045
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2530045
    | exact resolve eq2530045 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2530045
  have eq2532240 : ∀ X0 : G, y = (M.op x (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq1325551 X0 x
       have i₂ := eq2531347
       grind)
    | exact superpose eq2531347 eq1325551
    | exact resolve eq1325551 eq2531347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1325551
  have eq2532616 : y = (M.op x y) := by
    first
    | (have i₁ := eq2532240 x
       have i₂ := eq1325562 x x
       grind)
    | exact superpose eq1325562 eq2532240
    | exact resolve eq2532240 eq1325562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1325562 eq2532240
  have eq2532763 : x = y := by
    first
    | (have i₁ := eq2532616
       have i₂ := eq2531347
       grind)
    | exact superpose eq2531347 eq2532616
    | exact resolve eq2532616 eq2531347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2531347 eq2532616
  have eq2532929 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2532763
       grind)
    | exact superpose eq2532763 eq16
    | exact resolve eq16 eq2532763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2532763
  have eq2534955 : False := by grind
  exact eq2534955

/-- `Equation1473`: `x = (x ◇ y) ◇ (z ◇ (w ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if X = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pyy_pyy_pyx_Equation1473 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1473 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1473.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X3 X0))) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq65 : ∀ X0 X1 X4 X5 : G, (M.op X0 X1) = (M.op X0 (M.op X4 (M.op X5 (M.op X0 X1)))) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq9 (M.op X0 X1) (M.op x (M.op x X0)) X4 X5
       have i₂ := eq9 X0 X1 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq130 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X0)) = (M.op X1 (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq65 X1 (M.op X2 X0) X3 (M.op X0 x)
       have i₂ := eq9 X0 x X1 X2
       grind)
    | exact superpose eq9 eq65
    | exact resolve eq65 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X2) = (M.op X3 (M.op X4 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq65 X3 X2 X4 X0
       have i₂ := eq130 X2 X0 X3 X1
       grind)
    | (have i₁ := eq65 X3 X2 X4 X0
       have i₂ := eq130 X2 X0 X1 X3
       grind)
    | exact superpose eq130 eq65
    | exact resolve eq65 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq246 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq248 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq1318 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq1336 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq85 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq1338 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1318 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq1318
    | (have j0 := eq1318 X0
       grind)
    | exact resolve eq1318 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1318
  have eq1344 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq1338 X0
       have j1 := eq1336 X0
       grind)
    | (have r₁ := eq1338 X0
       have r₂ := eq1336 X0
       grind)
    | exact resolve eq1338 eq1336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1336 eq1338
  have eq1346 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1344 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1344
    | exact resolve eq1344 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1354 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ (k X0 X0)) (M.op X1 (M.op X2 (σ X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) (σ X0) X1 X2
       have i₂ := eq1344 X0
       grind)
    | exact superpose eq1344 eq9
    | exact resolve eq9 eq1344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1362 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (σ X0))) = (M.op X1 (σ (k X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq130 (σ X0) X1 (σ X0) X2
       have i₂ := eq1344 X0
       grind)
    | exact superpose eq1344 eq130
    | exact resolve eq130 eq1344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq1378 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq1346 X0
       have i₂ := eq20 X0 (τ X0)
       grind)
    | exact superpose eq20 eq1346
    | exact resolve eq1346 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1346
  have eq1379 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq1378 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1378
    | exact resolve eq1378 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1378
  have eq1960 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (σ X0))) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1362 X0 X1 X2
       have i₂ := eq1379 X0
       grind)
    | exact superpose eq1379 eq1362
    | exact resolve eq1362 eq1379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1362
  have eq2124 : ∀ X0 X1 X2 X3 : G, (M.op X1 (σ X0)) = (M.op X1 (M.op X2 (σ (M.op X0 (M.op X3 X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1960 (M.op X0 (M.op X3 X0)) X1 X2
       have i₂ := eq9 X0 (M.op X3 X0) X0 X3
       grind)
    | exact superpose eq9 eq1960
    | exact resolve eq1960 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2145 : ∀ X0 X1 X2 X3 : G, (M.op X2 (σ X1)) = (M.op X2 (M.op X3 (M.op X0 (σ (M.op X1 X1))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq176 X0 x (σ X1) X2 X3
       have i₂ := eq1960 X1 X0 x
       grind)
    | exact superpose eq1960 eq176
    | exact resolve eq176 eq1960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq2460 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op X1 (M.op X2 (σ X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1354 X0 X1 X2
       have i₂ := eq1379 X0
       grind)
    | exact superpose eq1379 eq1354
    | exact resolve eq1354 eq1379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1354
  have eq2777 : ∀ X0 X1 X2 X3 : G, (σ (M.op X0 (M.op X1 X0))) = (M.op (σ X0) (M.op X2 (M.op X3 (σ (M.op X0 (M.op X1 X0)))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2460 (M.op X0 (M.op X1 X0)) X2 X3
       have i₂ := eq9 X0 (M.op X1 X0) X0 X1
       grind)
    | exact superpose eq9 eq2460
    | exact resolve eq2460 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2825 : ∀ X0 X3 X4 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (M.op X3 (M.op X4 (σ (M.op X0 X0))))) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq9 (σ (M.op X0 X0)) (M.op x (M.op x (σ X0))) X3 X4
       have i₂ := eq2460 X0 x x
       grind)
    | exact superpose eq2460 eq9
    | exact resolve eq9 eq2460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2460
  have eq2847 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2825 X0 x x
       have i₂ := eq2145 x X0 (σ X0) x
       grind)
    | exact superpose eq2145 eq2825
    | exact resolve eq2825 eq2145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2145 eq2825
  have eq2862 : ∀ X0 X1 X2 : G, (σ (M.op X0 (M.op X1 X0))) = (M.op (σ X0) (M.op X2 (σ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2777 X0 X1 X2 x
       have i₂ := eq2124 X0 X2 x X1
       grind)
    | exact superpose eq2124 eq2777
    | exact resolve eq2777 eq2124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2124 eq2777
  have eq3696 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X1 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1960 X0 (σ X0) x
       have i₂ := eq2862 X0 X1 x
       grind)
    | exact superpose eq2862 eq1960
    | exact resolve eq1960 eq2862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1960 eq2862
  have eq4434 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq246 x y
       grind)
    | exact superpose eq246 eq16
    | (have j1 := eq246 x y
       grind)
    | exact resolve eq16 eq246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246
  have eq4513 : (σ y) = (σ (k x x)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4434
       have i₂ := eq1344 x
       grind)
    | exact superpose eq1344 eq4434
    | exact resolve eq4434 eq1344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1344 eq4434
  have eq4562 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4513
       have i₂ := eq1379 x
       grind)
    | exact superpose eq1379 eq4513
    | exact resolve eq4513 eq1379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1379 eq4513
  have eq97597 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq248 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq248
    | exact resolve eq248 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248
  have eq97791 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq97597 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq97597
    | (have j0 := eq97597 X0 X1
       grind)
    | exact resolve eq97597 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97597
  have eq352566 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq4562
       have i₂ := eq97791 y x
       grind)
    | exact superpose eq97791 eq4562
    | (have j1 := eq97791 (σ y) (σ (M.op x x))
       grind)
    | (have r₁ := eq4562
       have r₂ := eq97791 y x
       grind)
    | (have r₁ := eq4562
       have r₂ := eq97791 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq4562
       have r₂ := eq97791 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq4562 eq97791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4562 eq97791
  have eq352567 : x = y ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq352566
  have eq1092813 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq352567
       grind)
    | exact superpose eq352567 eq16
    | exact resolve eq16 eq352567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352567
  have eq1092814 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq1092813
       have r₂ := eq2847 x
       grind)
    | exact resolve eq1092813 eq2847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1092813
  have eq1092816 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1092814
       grind)
    | exact superpose eq1092814 eq10
    | exact resolve eq10 eq1092814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1092814
  have eq1093148 : x = y ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1092816
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1092816
    | exact resolve eq1092816 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1092816
  have eq1093202 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1093148
       grind)
    | exact superpose eq1093148 eq16
    | exact resolve eq16 eq1093148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1093148
  have eq1093203 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq1093202
       have r₂ := eq2847 x
       grind)
    | exact resolve eq1093202 eq2847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2847 eq1093202
  have eq1093304 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq1093203
       grind)
    | exact superpose eq1093203 eq10
    | exact resolve eq10 eq1093203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1093203
  have eq1093700 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1093304
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1093304
    | exact resolve eq1093304 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1093304
  have eq1093701 : y = (M.op x x) := by grind
  clear eq1093700
  have eq1094062 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3696 x x
       have i₂ := eq1093701
       grind)
    | exact superpose eq1093701 eq3696
    | exact resolve eq3696 eq1093701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3696 eq1093701
  have eq1094429 : False := by grind
  exact eq1094429

/-- `Equation1473`: `x = (x ◇ y) ◇ (z ◇ (w ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pyx_pxy_pyx_Equation1473 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1473 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1473.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
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
  have eq57 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq57 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq57 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq57 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq60 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq58 (σ X0)
       grind)
    | exact superpose eq58 eq15
    | exact resolve eq15 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq60 X0
       have i₂ := eq58 X0
       grind)
    | exact superpose eq58 eq60
    | exact resolve eq60 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq60
  have eq84 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq96 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq90 X0 X1
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq90
    | (have j0 := eq90 X0 X1
       grind)
    | exact resolve eq90 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq90
  have eq515 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq96 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq96 X0 X1
       grind)
    | exact superpose eq96 eq13
    | (have j0 := eq13 X0 (σ X0)
       have j1 := eq96 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq96 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq96 X0 X1
       grind)
    | exact resolve eq13 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq543 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq515 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515
  have eq551 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq543 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq543 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq543 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543
  have eq563 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq551 X0 X1
       have j1 := eq84 X0 (σ X1)
       grind)
    | (have r₁ := eq551 X0 X1
       have r₂ := eq84 X0 X1
       grind)
    | exact resolve eq551 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq551
  have eq570 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq563 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq563
    | (have j0 := eq563 X0 X1
       grind)
    | exact resolve eq563 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563
  have eq571 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq570 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570
  have eq576 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq571 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq571
    | exact resolve eq571 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq588 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq571 x y
       grind)
    | exact superpose eq571 eq16
    | exact resolve eq16 eq571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq571
  have eq693 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq576 X0 (τ X1)
       grind)
    | exact superpose eq576 eq17
    | exact resolve eq17 eq576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq576
  have eq709 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq693 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq693
    | exact resolve eq693 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693
  have eq717 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq709 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq709
    | exact resolve eq709 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709
  have eq729 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq588
       have i₂ := eq717 x y
       grind)
    | exact superpose eq717 eq588
    | exact resolve eq588 eq717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588 eq717
  have eq730 : False := by grind
  exact eq730
