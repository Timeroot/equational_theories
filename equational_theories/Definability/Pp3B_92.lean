import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation964`: `x = y ◇ ((z ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,X) else if m(X,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pyy_pxx_pyy_pyx_Equation964 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law964 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law964.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq25 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X1) (M.op X1 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X3 X1) (M.op X1 X0)) X1 X2
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 : G, (k (k (M.op X0 X0) X0) (M.op X0 X0)) = (M.op (k (M.op X0 X0) X0) (k (M.op X0 X0) X0)) := by
    intro X0
    grind
  have eq35 : ∀ X0 : G, (M.op X0 (k (M.op X0 X0) X0)) = X0 := by
    intro X0
    grind
  have eq36 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X0 X0)) (k (M.op X0 X0) X0))) := by
    intro X0 X1
    grind
  have eq37 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op (k (M.op X0 X0) X0) (M.op (M.op X0 X0) X1))) = X1 := by
    intro X0 X1
    grind
  have eq39 : ∀ X0 X1 : G, (k (M.op X0 X0) X0) = (M.op X0 (M.op (M.op X1 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (M.op X0 X0) X0) X0 X1
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq9
    | exact resolve eq9 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X2 X2) ∨ (M.op X0 X0) = X2 ∨ (M.op X0 X0) = (k X2 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X2 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 (M.op X0 X0) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X0)) (k (M.op X0 X0) X0)) = (M.op (M.op X0 X0) (M.op (M.op X2 (M.op X0 X0)) (M.op X0 X0))) := by
    intro X0 X1 X2
    grind
  have eq148 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X0) = (M.op (M.op X1 X2) (M.op X2 (M.op (M.op X3 (M.op X4 X2)) (M.op (M.op X4 X2) X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq25 (M.op (M.op X3 (M.op X4 X2)) (M.op (M.op X4 X2) X0)) X2 X4 X1
       have i₂ := eq9 X0 (M.op X4 X2) X3
       grind)
    | exact superpose eq9 eq25
    | exact resolve eq25 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq155 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X0 x
       have i₂ := eq25 X2 X0 X1 x
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq165 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X1 (M.op X1 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1 x
       have i₂ := eq25 (M.op X1 X2) X1 x X0
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 : G, (k (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (k (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq130 X0 X1 x
       have i₂ := eq39 (M.op X0 X0) x
       grind)
    | exact superpose eq39 eq130
    | exact resolve eq130 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq184 : ∀ X0 X1 : G, (k (k (M.op X0 X0) X0) (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (k (M.op X0 X0) X0)) := by
    intro X0 X1
    grind
  clear eq180
  have eq196 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X1)) (M.op (M.op X2 X1) X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq155 X1 X2 (M.op (M.op X3 (M.op X2 X1)) (M.op (M.op X2 X1) X0))
       have i₂ := eq9 X0 (M.op X2 X1) X3
       grind)
    | exact superpose eq9 eq155
    | exact resolve eq155 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq198 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 X0)) = (M.op (M.op X2 X1) (M.op (M.op X3 (M.op X2 X1)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq155 X1 X2 (M.op (M.op X2 X1) (M.op (M.op X3 (M.op X2 X1)) X0))
       have i₂ := eq155 (M.op X2 X1) X3 X0
       grind)
    | exact superpose eq155 eq155
    | exact resolve eq155 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq199 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) = (M.op X1 (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq155 X1 X0 (k (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1))
       have i₂ := eq35 (M.op X0 X1)
       grind)
    | exact superpose eq35 eq155
    | exact resolve eq155 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq204 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X2) X0) = (M.op X2 (M.op (M.op X4 X2) (M.op X2 (M.op (M.op X3 X2) X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq25 (M.op X2 (M.op (M.op X3 X2) X0)) X2 X4 X1
       have i₂ := eq155 X2 X3 X0
       grind)
    | exact superpose eq155 eq25
    | exact resolve eq25 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq209 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X0) = (M.op (M.op X3 X2) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq204 X0 X1 X2 X3 x
       have i₂ := eq9 (M.op (M.op X3 X2) X0) X2 x
       grind)
    | exact superpose eq9 eq204
    | exact resolve eq204 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq223 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (M.op (k (M.op X1 X1) X1) (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq155 X1 X1 (M.op (k (M.op X1 X1) X1) (M.op (M.op X1 X1) X0))
       have i₂ := eq37 X1 X0
       grind)
    | exact superpose eq37 eq155
    | exact resolve eq155 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq226 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (k (M.op X2 X2) X2) (M.op (M.op X2 X2) X0))) (M.op (M.op (k (M.op X2 X2) X2) (M.op (M.op X2 X2) X0)) X3)) = (M.op (M.op (k (M.op X2 X2) X2) (M.op (M.op X2 X2) X0)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq25 X3 (M.op (k (M.op X2 X2) X2) (M.op (M.op X2 X2) X0)) (M.op X2 X2) X1
       have i₂ := eq37 X2 X0
       grind)
    | exact superpose eq37 eq25
    | exact resolve eq25 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq227 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op (M.op X3 (M.op X2 X2)) (M.op (k (M.op X2 X2) X2) (M.op (M.op X2 X2) X0)))) = (M.op (M.op X1 (M.op X2 X2)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq25 (M.op (k (M.op X2 X2) X2) (M.op (M.op X2 X2) X0)) (M.op X2 X2) X3 X1
       have i₂ := eq37 X2 X0
       grind)
    | exact superpose eq37 eq25
    | exact resolve eq25 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq228 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (k (M.op X1 X1) X1) (M.op (M.op X1 X1) X0)) (M.op (M.op X3 (M.op (k (M.op X1 X1) X1) (M.op (M.op X1 X1) X0))) X2)) = (M.op X0 (M.op (M.op (k (M.op X1 X1) X1) (M.op (M.op X1 X1) X0)) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq25 X2 (M.op (k (M.op X1 X1) X1) (M.op (M.op X1 X1) X0)) X3 (M.op X1 X1)
       have i₂ := eq37 X1 X0
       grind)
    | exact superpose eq37 eq25
    | exact resolve eq25 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq231 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (k (M.op X1 X1) X1) (M.op (M.op X1 X1) X0)) X2)) = (M.op (M.op (M.op X1 X1) X0) (M.op (M.op (M.op X1 X1) X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq228 X0 X1 X2 x
       have i₂ := eq198 X2 (M.op (M.op X1 X1) X0) (k (M.op X1 X1) X1) x
       grind)
    | exact superpose eq198 eq228
    | exact resolve eq228 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq232 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X2)) X0) = (M.op X2 (M.op X2 (M.op (k (M.op X2 X2) X2) (M.op (M.op X2 X2) X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq227 X0 X1 X2 x
       have i₂ := eq198 (M.op (k (M.op X2 X2) X2) (M.op (M.op X2 X2) X0)) X2 X2 x
       grind)
    | exact superpose eq198 eq227
    | exact resolve eq227 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227
  have eq233 : ∀ X0 X2 X3 : G, (M.op (M.op (k (M.op X2 X2) X2) (M.op (M.op X2 X2) X0)) (M.op X0 X3)) = (M.op (M.op (M.op X2 X2) X0) (M.op (M.op (M.op X2 X2) X0) X3)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq226 X0 x X2 X3
       have i₂ := eq196 X3 (M.op (M.op X2 X2) X0) (k (M.op X2 X2) X2) x
       grind)
    | exact superpose eq196 eq226
    | exact resolve eq226 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196 eq226
  have eq241 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op (M.op (M.op X1 X1) X0) X2)) = (M.op X0 (M.op (M.op X1 (M.op X1 X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq231 X0 X1 X2
       have i₂ := eq223 X0 X1
       grind)
    | exact superpose eq223 eq231
    | exact resolve eq231 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231
  have eq242 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X2)) X0) = (M.op X2 (M.op X2 (M.op X2 (M.op X2 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq232 X0 X1 X2
       have i₂ := eq223 X0 X2
       grind)
    | exact superpose eq223 eq232
    | exact resolve eq232 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq243 : ∀ X0 X2 X3 : G, (M.op (M.op (M.op X2 X2) X0) (M.op (M.op (M.op X2 X2) X0) X3)) = (M.op (M.op X2 (M.op X2 X0)) (M.op X0 X3)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq233 X0 X2 X3
       have i₂ := eq223 X0 X2
       grind)
    | exact superpose eq223 eq233
    | exact resolve eq233 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223 eq233
  have eq245 : ∀ X0 X2 X3 : G, (M.op (M.op X2 (M.op X2 X0)) (M.op X0 X3)) = (M.op X0 (M.op (M.op X2 (M.op X2 X0)) X3)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq243 X0 X2 X3
       have i₂ := eq241 X0 X2 X3
       grind)
    | exact superpose eq241 eq243
    | exact resolve eq243 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241 eq243
  have eq263 : ∀ X0 X1 : G, (k (M.op X0 X0) X0) = (M.op (M.op X1 X0) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq165 X1 X0 (k (M.op X0 X0) X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq165
    | exact resolve eq165 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq275 : ∀ X0 X2 X3 X4 : G, (M.op X0 (M.op (M.op X2 (M.op X2 X0)) X3)) = (M.op (M.op X2 (M.op X2 X0)) (M.op (M.op X4 (M.op X2 (M.op X2 X0))) X3)) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq25 X3 (M.op X2 (M.op X2 X0)) X4 (M.op x X2)
       have i₂ := eq165 x X2 X0
       grind)
    | exact superpose eq165 eq25
    | exact resolve eq25 eq165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq278 : ∀ X0 X2 X3 : G, (M.op X0 (M.op (M.op X2 (M.op X2 X0)) X3)) = (M.op (M.op X2 X0) (M.op (M.op X2 X0) X3)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq275 X0 X2 X3 x
       have i₂ := eq198 X3 (M.op X2 X0) X2 x
       grind)
    | exact superpose eq198 eq275
    | exact resolve eq275 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq323 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X4) = (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X3 X0))) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq209 X4 X1 (M.op (M.op X2 X3) (M.op X3 X0)) X3
       have i₂ := eq9 X0 X3 X2
       grind)
    | exact superpose eq9 eq209
    | exact resolve eq209 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq326 : ∀ X0 X1 X2 : G, (M.op (k (M.op X0 X0) X0) X2) = (M.op (M.op X1 (M.op X0 X0)) X2) := by
    intro X0 X1 X2
    grind
  have eq328 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op X1 (M.op X2 (M.op X2 X0))) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq209 X3 X1 (M.op X2 (M.op X2 X0)) (M.op x X2)
       have i₂ := eq165 x X2 X0
       grind)
    | exact superpose eq165 eq209
    | exact resolve eq209 eq165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq462 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op (M.op X3 (M.op X0 X0)) (M.op (M.op X2 (M.op X0 X0)) (k (M.op X0 X0) X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq25 (M.op (M.op X2 (M.op X0 X0)) (k (M.op X0 X0) X0)) (M.op X0 X0) X3 X1
       have i₂ := eq36 X0 X2
       grind)
    | exact superpose eq36 eq25
    | exact resolve eq25 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq466 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (M.op X2 (M.op X0 X0)) (k (M.op X0 X0) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq165 X1 (M.op X0 X0) (M.op (M.op X2 (M.op X0 X0)) (k (M.op X0 X0) X0))
       have i₂ := eq36 X0 X2
       grind)
    | exact superpose eq36 eq165
    | exact resolve eq165 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq471 : ∀ X0 X1 : G, (k (k (M.op X0 X0) X0) (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq466 X0 X1 x
       have i₂ := eq184 X0 x
       grind)
    | exact superpose eq184 eq466
    | exact resolve eq466 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466
  have eq475 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0)) = (M.op X0 (M.op X0 (M.op (M.op X2 (M.op X0 X0)) (k (M.op X0 X0) X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq462 X0 X1 X2 x
       have i₂ := eq198 (M.op (M.op X2 (M.op X0 X0)) (k (M.op X0 X0) X0)) X0 X0 x
       grind)
    | exact superpose eq198 eq462
    | exact resolve eq462 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198 eq462
  have eq498 : ∀ X0 : G, (k (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)) = (k (k (M.op X0 X0) X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq471 X0 x
       have i₂ := eq263 (M.op X0 X0) x
       grind)
    | exact superpose eq263 eq471
    | exact resolve eq471 eq263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq471
  have eq502 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0)) = (M.op X0 (M.op X0 (k (k (M.op X0 X0) X0) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq475 X0 X1 x
       have i₂ := eq184 X0 x
       grind)
    | exact superpose eq184 eq475
    | exact resolve eq475 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184 eq475
  have eq510 : ∀ X0 : G, (k (k (M.op X0 X0) X0) (M.op X0 X0)) = (M.op X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq498 X0
       have i₂ := eq199 X0 X0
       grind)
    | exact superpose eq199 eq498
    | exact resolve eq498 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498
  have eq532 : ∀ X0 : G, (k (M.op (k (M.op X0 X0) X0) (k (M.op X0 X0) X0)) (k (M.op X0 X0) X0)) = (M.op (k (M.op X0 X0) X0) (M.op X0 (k (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq39 (k (M.op X0 X0) X0) X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq39
    | exact resolve eq39 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq567 : ∀ X0 : G, (k (M.op (k (M.op X0 X0) X0) (k (M.op X0 X0) X0)) (k (M.op X0 X0) X0)) = (M.op (k (M.op X0 X0) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq532 X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq532
    | exact resolve eq532 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532
  have eq580 : ∀ X0 : G, (M.op (k (M.op X0 X0) X0) X0) = (k (k (k (M.op X0 X0) X0) (M.op X0 X0)) (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq567 X0
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq567
    | exact resolve eq567 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567
  have eq586 : ∀ X0 : G, (M.op (k (M.op X0 X0) X0) X0) = (k (M.op X0 (M.op X0 (M.op X0 X0))) (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq580 X0
       have i₂ := eq510 X0
       grind)
    | exact superpose eq510 eq580
    | exact resolve eq580 eq510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580
  have eq770 : ∀ X0 : G, (k (M.op (k (M.op X0 X0) X0) (k (M.op X0 X0) X0)) (k (M.op X0 X0) X0)) = (M.op X0 (M.op (k (M.op X0 X0) X0) (k (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq263 (k (M.op X0 X0) X0) X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq263
    | exact resolve eq263 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq830 : ∀ X0 : G, (M.op X0 (k (k (M.op X0 X0) X0) (M.op X0 X0))) = (k (k (k (M.op X0 X0) X0) (M.op X0 X0)) (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq770 X0
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq770
    | exact resolve eq770 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770
  have eq845 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 (M.op X0 X0)))) = (k (M.op X0 (M.op X0 (M.op X0 X0))) (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq830 X0
       have i₂ := eq510 X0
       grind)
    | exact superpose eq510 eq830
    | exact resolve eq830 eq510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830
  have eq851 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 (M.op X0 X0)))) = (M.op (k (M.op X0 X0) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq845 X0
       have i₂ := eq586 X0
       grind)
    | exact superpose eq586 eq845
    | exact resolve eq845 eq586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq845
  have eq10394 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2))) X3) = (M.op (M.op X4 X2) (M.op (M.op X1 X2) (M.op (M.op X1 X2) (M.op (M.op X1 X2) X3)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq209 (M.op (M.op X1 X2) (M.op (M.op X1 X2) (M.op (M.op X1 X2) X3))) X4 X2 X1
       have i₂ := eq242 X3 X0 (M.op X1 X2)
       grind)
    | exact superpose eq242 eq209
    | exact resolve eq209 eq242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242
  have eq10413 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2))) X3) = (M.op (M.op X4 X2) (M.op X2 (M.op (M.op X1 (M.op X1 X2)) (M.op (M.op X1 X2) X3)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq10394 X0 X1 X2 X3 X4
       have i₂ := eq278 X2 X1 (M.op (M.op X1 X2) X3)
       grind)
    | exact superpose eq278 eq10394
    | exact resolve eq10394 eq278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278 eq10394
  have eq10743 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2))) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq10413 X0 X1 X2 X3 x
       have i₂ := eq148 X3 x X2 X1 X1
       grind)
    | exact superpose eq148 eq10413
    | exact resolve eq10413 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148 eq10413
  have eq11213 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq60 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq11214 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11213 X0 X1
       have j1 := eq79 X1 X0
       grind)
    | (have r₁ := eq11213 X1 X1
       have r₂ := eq79 X0 X1
       grind)
    | (have r₁ := eq11213 X1 X1
       have r₂ := eq79 X0 X1
       grind)
    | (have r₁ := eq11213 (M.op (M.op X1 X1) (M.op X1 X1)) X1
       have r₂ := eq79 X0 (M.op X1 X1)
       grind)
    | exact resolve eq11213 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq11213
  have eq11244 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op (M.op X3 (M.op (M.op X0 X0) (M.op X0 X0))) X2) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq10743 X0 X1 X1 X3
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq10743 X0 X0 X0 X3
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq10743
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq10743 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11437 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (k (M.op (M.op X2 X0) (M.op X2 X0)) (M.op X2 X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq326 (M.op X2 X0) x X1
       have i₂ := eq10743 x X2 X0 X1
       grind)
    | exact superpose eq10743 eq326
    | exact resolve eq326 eq10743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326
  have eq11656 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 (M.op X0 (M.op X2 X0))) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11437 X0 X1 X2
       have i₂ := eq199 X2 X0
       grind)
    | exact superpose eq199 eq11437
    | exact resolve eq11437 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11437
  have eq11757 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X1 X2) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11244 X0 X1 X2 x
       have i₂ := eq323 X0 x X0 X0 X2
       grind)
    | exact superpose eq323 eq11244
    | (have j0 := eq11244 X0 X1 X2 x
       grind)
    | exact resolve eq11244 eq323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323 eq11244
  have eq12213 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X2 (M.op X0 (M.op X3 X0))) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq209 X1 X2 (M.op X0 (M.op X3 X0)) X0
       have i₂ := eq11656 X0 X1 X3
       grind)
    | exact superpose eq11656 eq209
    | exact resolve eq209 eq11656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11656
  have eq12859 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X1 X0)) X2) = (M.op (M.op X3 (M.op (M.op X1 (M.op X1 X0)) X0)) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12213 (M.op X1 (M.op X1 X0)) X2 X3 (M.op x X1)
       have i₂ := eq165 x X1 X0
       grind)
    | exact superpose eq165 eq12213
    | exact resolve eq12213 eq165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165 eq12213
  have eq16940 : ∀ X0 X1 X2 X3 : G, (M.op X1 X3) = (M.op (M.op (M.op X0 X1) (M.op (M.op X2 (M.op X2 (M.op X0 X1))) (M.op X0 X1))) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq10743 (M.op X2 (M.op X2 (M.op X0 X1))) X0 X1 X3
       have i₂ := eq245 (M.op X0 X1) X2 (M.op X0 X1)
       grind)
    | exact superpose eq245 eq10743
    | exact resolve eq10743 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245 eq10743
  have eq17144 : ∀ X0 X1 X2 X3 : G, (M.op X1 X3) = (M.op (M.op X2 (M.op X2 (M.op X0 X1))) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16940 X0 X1 X2 X3
       have i₂ := eq12859 (M.op X0 X1) X2 X3 (M.op X0 X1)
       grind)
    | exact superpose eq12859 eq16940
    | exact resolve eq16940 eq12859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12859 eq16940
  have eq17718 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 (M.op X3 (M.op X4 X0))) (M.op (M.op X3 (M.op X4 X0)) X1)) = (M.op (M.op X3 (M.op X4 X0)) (M.op X0 X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq25 X1 (M.op X3 (M.op X4 X0)) X3 X2
       have i₂ := eq17144 X4 X0 X3 X1
       grind)
    | exact superpose eq17144 eq25
    | exact resolve eq25 eq17144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq17725 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X1) = (M.op (M.op X2 (M.op X3 (M.op X4 X0))) X1) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq209 X1 X2 (M.op X3 (M.op X4 X0)) X3
       have i₂ := eq17144 X4 X0 X3 X1
       grind)
    | exact superpose eq17144 eq209
    | exact resolve eq209 eq17144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209 eq17144
  have eq17984 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X3 (M.op X4 X0)) (M.op X0 X1)) = (M.op X0 (M.op (M.op X3 (M.op X4 X0)) X1)) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq17718 X0 X1 x X3 X4
       have i₂ := eq17725 X0 (M.op (M.op X3 (M.op X4 X0)) X1) x X3 X4
       grind)
    | exact superpose eq17725 eq17718
    | exact resolve eq17718 eq17725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17718
  have eq20396 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq263 X1 X1
       have i₂ := eq11214 X0 X1
       grind)
    | (have i₁ := eq263 X0 X1
       have i₂ := eq11214 (M.op X1 X0) X1
       grind)
    | exact superpose eq11214 eq263
    | (have j1 := eq11214 X0 X1
       grind)
    | exact resolve eq263 eq11214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263
  have eq20470 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11214 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11214
  have eq20473 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq20396 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20396
  have eq20485 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq20470 X0 X1
       have j1 := eq11757 X1 X0 x
       grind)
    | (have r₁ := eq20470 X1 X0
       have r₂ := eq11757 X0 X1 X1
       grind)
    | (have r₁ := eq20470 X0 X1
       have r₂ := eq11757 X0 X1 X0
       grind)
    | (have r₁ := eq20470 X0 X0
       have r₂ := eq11757 X0 (M.op X0 X0) x
       grind)
    | exact resolve eq20470 eq11757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11757 eq20470
  have eq21526 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq20473 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20473
  have eq22179 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq21526 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21526
  have eq23338 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq22179 (σ X0)
       grind)
    | exact superpose eq22179 eq15
    | exact resolve eq15 eq22179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23353 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq23338 X0
       have i₂ := eq22179 X0
       grind)
    | exact superpose eq22179 eq23338
    | exact resolve eq23338 eq22179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22179 eq23338
  have eq25350 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (k (σ (M.op X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq35 (σ X0)
       have i₂ := eq23353 X0
       grind)
    | exact superpose eq23353 eq35
    | exact resolve eq35 eq23353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq25415 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20485 X1 (σ X0)
       have i₂ := eq23353 X0
       grind)
    | exact superpose eq23353 eq20485
    | (have j0 := eq20485 X1 (σ X0)
       grind)
    | exact resolve eq20485 eq23353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25438 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ X0) (M.op (σ (M.op X0 X0)) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq155 (σ X0) (σ X0) X1
       have i₂ := eq23353 X0
       grind)
    | exact superpose eq23353 eq155
    | exact resolve eq155 eq23353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq25463 : ∀ X0 X1 X2 X3 : G, (M.op (σ X0) X1) = (M.op (M.op X2 (M.op X3 (σ (M.op X0 X0)))) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq17725 (σ X0) X1 X2 X3 (σ X0)
       have i₂ := eq23353 X0
       grind)
    | exact superpose eq23353 eq17725
    | exact resolve eq17725 eq23353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17725
  have eq25492 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq25350 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq25350
    | exact resolve eq25350 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25350
  have eq27843 : ∀ X0 : G, (k (M.op (σ (k (M.op X0 X0) X0)) (σ (k (M.op X0 X0) X0))) (σ (k (M.op X0 X0) X0))) = (M.op (σ (k (M.op X0 X0) X0)) (M.op (σ X0) (σ (k (M.op X0 X0) X0)))) := by
    intro X0
    first
    | (have i₁ := eq39 (σ (k (M.op X0 X0) X0)) (σ X0)
       have i₂ := eq25492 X0
       grind)
    | exact superpose eq25492 eq39
    | exact resolve eq39 eq25492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq27900 : ∀ X0 : G, (k (M.op (σ (k (M.op X0 X0) X0)) (σ (k (M.op X0 X0) X0))) (σ (k (M.op X0 X0) X0))) = (M.op (σ (k (M.op X0 X0) X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq27843 X0
       have i₂ := eq25492 X0
       grind)
    | exact superpose eq25492 eq27843
    | exact resolve eq27843 eq25492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25492 eq27843
  have eq27940 : ∀ X0 : G, (M.op (σ (k (M.op X0 X0) X0)) (σ X0)) = (k (σ (M.op (k (M.op X0 X0) X0) (k (M.op X0 X0) X0))) (σ (k (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq27900 X0
       have i₂ := eq23353 (k (M.op X0 X0) X0)
       grind)
    | exact superpose eq23353 eq27900
    | exact resolve eq27900 eq23353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27900
  have eq27956 : ∀ X0 : G, (σ (k (M.op (k (M.op X0 X0) X0) (k (M.op X0 X0) X0)) (k (M.op X0 X0) X0))) = (M.op (σ (k (M.op X0 X0) X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq27940 X0
       have i₂ := eq15 (M.op (k (M.op X0 X0) X0) (k (M.op X0 X0) X0)) (k (M.op X0 X0) X0)
       grind)
    | exact superpose eq15 eq27940
    | exact resolve eq27940 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27940
  have eq27965 : ∀ X0 : G, (σ (k (k (k (M.op X0 X0) X0) (M.op X0 X0)) (k (M.op X0 X0) X0))) = (M.op (σ (k (M.op X0 X0) X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq27956 X0
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq27956
    | exact resolve eq27956 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq27956
  have eq27968 : ∀ X0 : G, (M.op (σ (k (M.op X0 X0) X0)) (σ X0)) = (σ (k (M.op X0 (M.op X0 (M.op X0 X0))) (k (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq27965 X0
       have i₂ := eq510 X0
       grind)
    | exact superpose eq510 eq27965
    | exact resolve eq27965 eq510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27965
  have eq27970 : ∀ X0 : G, (M.op (σ (k (M.op X0 X0) X0)) (σ X0)) = (σ (M.op (k (M.op X0 X0) X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq27968 X0
       have i₂ := eq586 X0
       grind)
    | exact superpose eq586 eq27968
    | exact resolve eq27968 eq586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586 eq27968
  have eq59191 : ∀ X0 X1 : G, (M.op (σ (M.op X1 X1)) (k (k (M.op (σ (M.op X1 X1)) (σ (M.op X1 X1))) (σ (M.op X1 X1))) (M.op (σ (M.op X1 X1)) (σ (M.op X1 X1))))) = (M.op (σ X1) (M.op (σ X1) (M.op (M.op X0 (M.op (σ (M.op X1 X1)) (σ (M.op X1 X1)))) (M.op (σ (M.op X1 X1)) (σ (M.op X1 X1)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq25438 X1 (M.op (σ (M.op X1 X1)) (k (k (M.op (σ (M.op X1 X1)) (σ (M.op X1 X1))) (σ (M.op X1 X1))) (M.op (σ (M.op X1 X1)) (σ (M.op X1 X1)))))
       have i₂ := eq502 (σ (M.op X1 X1)) X0
       grind)
    | exact superpose eq502 eq25438
    | exact resolve eq25438 eq502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502
  have eq59224 : ∀ X0 X1 : G, (M.op (σ (M.op X1 X1)) (k (k (M.op (σ (M.op X1 X1)) (σ (M.op X1 X1))) (σ (M.op X1 X1))) (M.op (σ (M.op X1 X1)) (σ (M.op X1 X1))))) = (M.op (σ X1) (M.op (σ X1) (M.op (σ (M.op X1 X1)) (M.op (M.op X0 (M.op (σ (M.op X1 X1)) (σ (M.op X1 X1)))) (σ (M.op X1 X1)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq59191 X0 X1
       have i₂ := eq17984 (σ (M.op X1 X1)) (σ (M.op X1 X1)) X0 (σ (M.op X1 X1))
       grind)
    | exact superpose eq17984 eq59191
    | exact resolve eq59191 eq17984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17984 eq59191
  have eq59579 : ∀ X0 X1 : G, (M.op (σ (M.op X1 X1)) (k (k (M.op (σ (M.op X1 X1)) (σ (M.op X1 X1))) (σ (M.op X1 X1))) (M.op (σ (M.op X1 X1)) (σ (M.op X1 X1))))) = (M.op (M.op X0 (M.op (σ (M.op X1 X1)) (σ (M.op X1 X1)))) (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq59224 X0 X1
       have i₂ := eq25438 X1 (M.op (M.op X0 (M.op (σ (M.op X1 X1)) (σ (M.op X1 X1)))) (σ (M.op X1 X1)))
       grind)
    | exact superpose eq25438 eq59224
    | exact resolve eq59224 eq25438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25438 eq59224
  have eq59900 : ∀ X1 : G, (M.op (σ X1) (σ (M.op X1 X1))) = (M.op (σ (M.op X1 X1)) (k (k (M.op (σ (M.op X1 X1)) (σ (M.op X1 X1))) (σ (M.op X1 X1))) (M.op (σ (M.op X1 X1)) (σ (M.op X1 X1))))) := by
    intro X1
    first
    | (have i₁ := eq59579 x X1
       have i₂ := eq25463 X1 (σ (M.op X1 X1)) x (σ (M.op X1 X1))
       grind)
    | exact superpose eq25463 eq59579
    | exact resolve eq59579 eq25463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25463 eq59579
  have eq60156 : ∀ X1 : G, (M.op (σ X1) (σ (M.op X1 X1))) = (M.op (σ (M.op X1 X1)) (M.op (σ (M.op X1 X1)) (M.op (σ (M.op X1 X1)) (M.op (σ (M.op X1 X1)) (σ (M.op X1 X1)))))) := by
    intro X1
    first
    | (have i₁ := eq59900 X1
       have i₂ := eq510 (σ (M.op X1 X1))
       grind)
    | exact superpose eq510 eq59900
    | exact resolve eq59900 eq510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510 eq59900
  have eq60376 : ∀ X1 : G, (M.op (σ X1) (σ (M.op X1 X1))) = (M.op (k (M.op (σ (M.op X1 X1)) (σ (M.op X1 X1))) (σ (M.op X1 X1))) (σ (M.op X1 X1))) := by
    intro X1
    first
    | (have i₁ := eq60156 X1
       have i₂ := eq851 (σ (M.op X1 X1))
       grind)
    | exact superpose eq851 eq60156
    | exact resolve eq60156 eq851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851 eq60156
  have eq60528 : ∀ X1 : G, (M.op (σ X1) (σ (M.op X1 X1))) = (M.op (k (σ (M.op (M.op X1 X1) (M.op X1 X1))) (σ (M.op X1 X1))) (σ (M.op X1 X1))) := by
    intro X1
    first
    | (have i₁ := eq60376 X1
       have i₂ := eq23353 (M.op X1 X1)
       grind)
    | exact superpose eq23353 eq60376
    | exact resolve eq60376 eq23353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23353 eq60376
  have eq60639 : ∀ X1 : G, (M.op (σ X1) (σ (M.op X1 X1))) = (M.op (σ (k (M.op (M.op X1 X1) (M.op X1 X1)) (M.op X1 X1))) (σ (M.op X1 X1))) := by
    intro X1
    first
    | (have i₁ := eq60528 X1
       have i₂ := eq15 (M.op (M.op X1 X1) (M.op X1 X1)) (M.op X1 X1)
       grind)
    | exact superpose eq15 eq60528
    | exact resolve eq60528 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60528
  have eq60715 : ∀ X1 : G, (M.op (σ X1) (σ (M.op X1 X1))) = (σ (M.op (k (M.op (M.op X1 X1) (M.op X1 X1)) (M.op X1 X1)) (M.op X1 X1))) := by
    intro X1
    first
    | (have i₁ := eq60639 X1
       have i₂ := eq27970 (M.op X1 X1)
       grind)
    | exact superpose eq27970 eq60639
    | exact resolve eq60639 eq27970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27970 eq60639
  have eq60767 : ∀ X1 : G, (M.op (σ X1) (σ (M.op X1 X1))) = (σ (M.op (M.op X1 (M.op X1 (M.op X1 X1))) (M.op X1 X1))) := by
    intro X1
    first
    | (have i₁ := eq60715 X1
       have i₂ := eq199 X1 X1
       grind)
    | exact superpose eq199 eq60715
    | exact resolve eq60715 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199 eq60715
  have eq60798 : ∀ X1 : G, (M.op (σ X1) (σ (M.op X1 X1))) = (σ (M.op X1 (M.op X1 X1))) := by
    intro X1
    first
    | (have i₁ := eq60767 X1
       have i₂ := eq328 X1 X1 X1 (M.op X1 X1)
       grind)
    | exact superpose eq328 eq60767
    | exact resolve eq60767 eq328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328 eq60767
  have eq106150 : ∀ X0 X1 : G, (τ X0) = (M.op X1 X1) ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq25415 X1 X0
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq25415 X0 (σ X0)
       grind)
    | exact superpose eq25415 eq10
    | (have j1 := eq25415 X1 X0
       grind)
    | exact resolve eq10 eq25415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25415
  have eq191769 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq106150 (σ X1) X0
       grind)
    | exact superpose eq106150 eq15
    | (have j1 := eq106150 (σ X1) X0
       grind)
    | exact resolve eq15 eq106150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106150
  have eq191788 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq191769 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq191769
    | (have j0 := eq191769 X0 X1
       grind)
    | exact resolve eq191769 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191769
  have eq213713 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq191788 x y
       grind)
    | exact superpose eq191788 eq16
    | (have j1 := eq191788 x y
       grind)
    | exact resolve eq16 eq191788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191788
  have eq216672 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq213713
       have i₂ := eq20485 y x
       grind)
    | exact superpose eq20485 eq213713
    | (have j1 := eq20485 y x
       grind)
    | exact resolve eq213713 eq20485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20485 eq213713
  have eq216675 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by grind
  clear eq216672
  have eq216676 : y = (M.op x x) := by grind
  clear eq216675
  have eq218846 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq60798 x
       have i₂ := eq216676
       grind)
    | exact superpose eq216676 eq60798
    | exact resolve eq60798 eq216676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60798 eq216676
  have eq219039 : False := by grind
  exact eq219039

/-- `Equation964`: `x = y ◇ ((z ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_pyx_pxx_pyx_Equation964 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law964 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law964.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) (M.op X2 X1)) = (M.op X2 (M.op (M.op X3 X2) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X0 X2) (M.op X2 X1)) X2 X3
       have i₂ := eq9 X1 X2 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X2 X3 : G, (M.op X0 (M.op X0 (M.op (M.op X3 X0) X2))) = X2 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq9 X2 X0 x
       have i₂ := eq56 x X2 X0 X3
       grind)
    | exact superpose eq56 eq9
    | exact resolve eq9 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X0 x
       have i₂ := eq56 X1 (M.op X0 X2) X0 x
       grind)
    | exact superpose eq56 eq9
    | exact resolve eq9 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) (M.op (M.op X3 (M.op X1 X2)) X0)) = (M.op X2 (M.op X2 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq74 X2 (M.op (M.op X1 X2) (M.op (M.op X3 (M.op X1 X2)) X0)) X1
       have i₂ := eq74 (M.op X1 X2) X0 X3
       grind)
    | exact superpose eq74 eq74
    | exact resolve eq74 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op (M.op X4 X1) (M.op X1 (M.op (M.op X2 X1) X0)))) = (M.op (M.op X3 X1) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq56 X3 (M.op X1 (M.op (M.op X2 X1) X0)) X1 X4
       have i₂ := eq74 X1 X0 X2
       grind)
    | exact superpose eq74 eq56
    | exact resolve eq56 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) X0) = (M.op (M.op X3 X1) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq92 X0 X1 X2 X3 x
       have i₂ := eq9 (M.op (M.op X2 X1) X0) X1 x
       grind)
    | exact superpose eq9 eq92
    | exact resolve eq92 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq115 : ∀ X0 X1 X3 X4 : G, (M.op X0 (M.op (M.op X1 (M.op X1 X0)) X3)) = (M.op (M.op X1 (M.op X1 X0)) (M.op (M.op X4 (M.op X1 (M.op X1 X0))) X3)) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq56 (M.op x X1) X3 (M.op X1 (M.op X1 X0)) X4
       have i₂ := eq78 X1 x X0
       grind)
    | exact superpose eq78 eq56
    | exact resolve eq56 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : ∀ X0 X1 X3 : G, (M.op X0 (M.op (M.op X1 (M.op X1 X0)) X3)) = (M.op (M.op X1 X0) (M.op (M.op X1 X0) X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq115 X0 X1 X3 x
       have i₂ := eq89 X3 X1 (M.op X1 X0) x
       grind)
    | exact superpose eq89 eq115
    | exact resolve eq115 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq141 : ∀ X0 X1 X3 X4 : G, (M.op X0 X4) = (M.op (M.op X3 (M.op X1 (M.op X1 X0))) X4) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq97 X4 (M.op X1 (M.op X1 X0)) X3 (M.op x X1)
       have i₂ := eq78 X1 x X0
       grind)
    | exact superpose eq78 eq97
    | exact resolve eq97 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq291 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq321 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq291 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291
  have eq349 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq367 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq349 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349
  have eq368 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq367 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367
  have eq372 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq368 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq368
    | exact resolve eq368 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq375 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq372 X0
       have i₂ := eq368 X0
       grind)
    | exact superpose eq368 eq372
    | exact resolve eq372 eq368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368 eq372
  have eq406 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq375 X0
       grind)
    | exact superpose eq375 eq9
    | exact resolve eq9 eq375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq407 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) (σ X0) X1
       have i₂ := eq375 X0
       grind)
    | exact superpose eq375 eq9
    | exact resolve eq9 eq375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq412 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (M.op (σ X0) (M.op (σ X0) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq78 (σ X0) (σ X0) X1
       have i₂ := eq375 X0
       grind)
    | exact superpose eq375 eq78
    | exact resolve eq78 eq375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq417 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq321 (σ X0) X1
       have i₂ := eq375 X0
       grind)
    | exact superpose eq375 eq321
    | (have j0 := eq321 (σ X0) X1
       grind)
    | exact resolve eq321 eq375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq420 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq421 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq420 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq420
    | exact resolve eq420 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420
  have eq423 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    grind
  clear eq421
  have eq840 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq406 X0 (σ X0)
       have i₂ := eq375 X0
       grind)
    | exact superpose eq375 eq406
    | exact resolve eq406 eq375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406
  have eq859 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq840 X0
       have i₂ := eq375 (M.op X0 X0)
       grind)
    | exact superpose eq375 eq840
    | exact resolve eq840 eq375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375 eq840
  have eq1090 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (σ X0)) (σ (M.op X0 (M.op X0 X0)))) = (M.op (σ X0) (M.op (M.op X2 (σ X0)) (σ (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 X1 (σ (M.op X0 X0)) (σ X0) X2
       have i₂ := eq423 X0
       grind)
    | exact superpose eq423 eq56
    | exact resolve eq56 eq423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423
  have eq1101 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1090 X0 X1 x
       have i₂ := eq407 X0 x
       grind)
    | exact superpose eq407 eq1090
    | exact resolve eq1090 eq407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407 eq1090
  have eq1293 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 (M.op (M.op X1 X0) X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq859 X0
       have i₂ := eq56 X0 X0 X0 X1
       grind)
    | exact superpose eq56 eq859
    | exact resolve eq859 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1299 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ (M.op (M.op X1 X0) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq859 X0
       have i₂ := eq97 (M.op X0 X0) X0 X0 X1
       grind)
    | (have i₁ := eq859 X0
       have i₂ := eq97 (M.op X0 X0) X0 X1 X0
       grind)
    | exact superpose eq97 eq859
    | exact resolve eq859 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq859
  have eq6190 : ∀ X0 X1 : G, (M.op X0 X0) = (τ X1) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq417 X0 X1
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq417 X0 (σ X0)
       grind)
    | exact superpose eq417 eq10
    | (have j1 := eq417 X0 X1
       grind)
    | exact resolve eq10 eq417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417
  have eq7240 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6190 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6190
    | (have j0 := eq6190 X1 (σ X0)
       grind)
    | exact resolve eq6190 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6190
  have eq7414 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7240 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq7240
    | (have j0 := eq7240 X0 X1
       grind)
    | exact resolve eq7240 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7240
  have eq9158 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7414 x y
       grind)
    | exact superpose eq7414 eq16
    | (have j1 := eq7414 x y
       grind)
    | exact resolve eq16 eq7414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7414
  have eq9313 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq9158
       have i₂ := eq321 y x
       grind)
    | exact superpose eq321 eq9158
    | (have j1 := eq321 y x
       grind)
    | exact resolve eq9158 eq321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321 eq9158
  have eq9326 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by grind
  clear eq9313
  have eq9327 : x = (M.op y y) := by grind
  clear eq9326
  have eq9345 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) (M.op (σ y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq412 y X0
       have i₂ := eq9327
       grind)
    | exact superpose eq9327 eq412
    | exact resolve eq412 eq9327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412
  have eq9357 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ (M.op (M.op X0 y) x))) := by
    intro X0
    first
    | (have i₁ := eq1299 y X0
       have i₂ := eq9327
       grind)
    | exact superpose eq9327 eq1299
    | exact resolve eq1299 eq9327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1299
  have eq9369 : ∀ X0 : G, (M.op y (M.op x (M.op y X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 y y
       have i₂ := eq9327
       grind)
    | exact superpose eq9327 eq9
    | exact resolve eq9 eq9327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9374 : ∀ X0 X1 : G, (M.op x (M.op y X0)) = (M.op y (M.op (M.op X1 y) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq56 y X0 y X1
       have i₂ := eq9327
       grind)
    | exact superpose eq9327 eq56
    | exact resolve eq56 eq9327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9380 : ∀ X0 : G, (M.op y (M.op y (M.op x X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq74 y X0 y
       have i₂ := eq9327
       grind)
    | exact superpose eq9327 eq74
    | exact resolve eq74 eq9327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq9381 : ∀ X0 : G, (M.op x (M.op y (M.op y X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq78 y y X0
       have i₂ := eq9327
       grind)
    | exact superpose eq9327 eq78
    | exact resolve eq78 eq9327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq9384 : ∀ X0 X1 : G, (M.op (M.op X0 y) X1) = (M.op x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq97 X1 y X0 y
       have i₂ := eq9327
       grind)
    | exact superpose eq9327 eq97
    | exact resolve eq97 eq9327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq9390 : (σ y) = (M.op (σ y) (σ (M.op y (M.op x y)))) := by
    first
    | (have i₁ := eq1293 y y
       have i₂ := eq9327
       grind)
    | exact superpose eq9327 eq1293
    | exact resolve eq1293 eq9327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1293
  have eq9397 : ∀ X0 : G, (M.op x (M.op y X0)) = (M.op y (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq9374 X0 x
       have i₂ := eq9384 x X0
       grind)
    | exact superpose eq9384 eq9374
    | exact resolve eq9374 eq9384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9374
  have eq9402 : (σ y) = (M.op (σ y) (σ (M.op x x))) := by
    first
    | (have i₁ := eq9357 x
       have i₂ := eq9384 x x
       grind)
    | exact superpose eq9384 eq9357
    | exact resolve eq9357 eq9384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9357
  have eq9498 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op x (M.op y X0)) X1)) = (M.op (M.op x (M.op y X0)) (M.op (M.op X2 (M.op x (M.op y X0))) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 y X1 (M.op x (M.op y X0)) X2
       have i₂ := eq9369 X0
       grind)
    | exact superpose eq9369 eq56
    | exact resolve eq56 eq9369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9369
  have eq9526 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x (M.op y X0)) X1)) = (M.op (M.op y X0) (M.op (M.op y X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9498 X0 X1 x
       have i₂ := eq89 X1 x (M.op y X0) x
       grind)
    | exact superpose eq89 eq9498
    | exact resolve eq9498 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9498
  have eq9541 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x (M.op y X0)) X1)) = (M.op X0 (M.op (M.op y (M.op y X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9526 X0 X1
       have i₂ := eq119 X0 y X1
       grind)
    | exact superpose eq119 eq9526
    | exact resolve eq9526 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9526
  have eq9563 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op y (M.op x X0)) X1)) = (M.op (M.op y (M.op x X0)) (M.op (M.op X2 (M.op y (M.op x X0))) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 y X1 (M.op y (M.op x X0)) X2
       have i₂ := eq9380 X0
       grind)
    | exact superpose eq9380 eq56
    | exact resolve eq56 eq9380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq9380
  have eq9601 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op y (M.op x X0)) X1)) = (M.op (M.op x X0) (M.op (M.op x X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9563 X0 X1 x
       have i₂ := eq89 X1 y (M.op x X0) x
       grind)
    | exact superpose eq89 eq9563
    | exact resolve eq9563 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq9563
  have eq9615 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op y (M.op x X0)) X1)) = (M.op X0 (M.op (M.op x (M.op x X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9601 X0 X1
       have i₂ := eq119 X0 x X1
       grind)
    | exact superpose eq119 eq9601
    | exact resolve eq9601 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9601
  have eq9625 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x (M.op y X0)) X1)) = (M.op X0 (M.op (M.op x (M.op x X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9615 X0 X1
       have i₂ := eq9397 X0
       grind)
    | exact superpose eq9397 eq9615
    | exact resolve eq9615 eq9397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9615
  have eq12958 : (σ (M.op y (M.op x y))) = (M.op (σ y) (σ (M.op (M.op y (M.op x y)) (M.op (M.op y (M.op x y)) (M.op y (M.op x y)))))) := by
    first
    | (have i₁ := eq1101 (M.op y (M.op x y)) (σ y)
       have i₂ := eq9390
       grind)
    | exact superpose eq9390 eq1101
    | exact resolve eq1101 eq9390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1101 eq9390
  have eq13008 : (σ (M.op y (M.op x y))) = (M.op (σ y) (σ (M.op (M.op x y) (M.op (M.op y (M.op y (M.op x y))) (M.op y (M.op x y)))))) := by
    first
    | (have i₁ := eq12958
       have i₂ := eq119 (M.op x y) y (M.op y (M.op x y))
       grind)
    | exact superpose eq119 eq12958
    | exact resolve eq12958 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq12958
  have eq13039 : (σ (M.op y (M.op x y))) = (M.op (σ y) (σ (M.op (M.op x y) (M.op (M.op x (M.op y (M.op x y))) (M.op y (M.op x y)))))) := by
    first
    | (have i₁ := eq13008
       have i₂ := eq9541 (M.op x y) (M.op y (M.op x y))
       grind)
    | exact superpose eq9541 eq13008
    | exact resolve eq13008 eq9541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9541 eq13008
  have eq13062 : (σ (M.op y (M.op x y))) = (M.op (σ y) (σ (M.op (M.op x y) (M.op (M.op x (M.op x (M.op x y))) (M.op y (M.op x y)))))) := by
    first
    | (have i₁ := eq13039
       have i₂ := eq9625 (M.op x y) (M.op y (M.op x y))
       grind)
    | exact superpose eq9625 eq13039
    | exact resolve eq13039 eq9625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9625 eq13039
  have eq13076 : (σ (M.op y (M.op x y))) = (M.op (σ y) (σ (M.op x (M.op (M.op x (M.op x (M.op x y))) (M.op y (M.op x y)))))) := by
    first
    | (have i₁ := eq13062
       have i₂ := eq9384 x (M.op (M.op x (M.op x (M.op x y))) (M.op y (M.op x y)))
       grind)
    | exact superpose eq9384 eq13062
    | exact resolve eq13062 eq9384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9384 eq13062
  have eq13086 : (σ (M.op y (M.op x y))) = (M.op (σ y) (σ (M.op x (M.op y (M.op y (M.op x y)))))) := by
    first
    | (have i₁ := eq13076
       have i₂ := eq141 y x x (M.op y (M.op x y))
       grind)
    | exact superpose eq141 eq13076
    | exact resolve eq13076 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq13076
  have eq13094 : (σ (M.op y (M.op x y))) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq13086
       have i₂ := eq9381 (M.op x y)
       grind)
    | exact superpose eq9381 eq13086
    | exact resolve eq13086 eq9381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9381 eq13086
  have eq13098 : (σ (M.op x (M.op y y))) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq13094
       have i₂ := eq9397 y
       grind)
    | exact superpose eq9397 eq13094
    | exact resolve eq13094 eq9397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9397 eq13094
  have eq13100 : (σ (M.op x x)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq13098
       have i₂ := eq9327
       grind)
    | exact superpose eq9327 eq13098
    | exact resolve eq13098 eq9327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9327 eq13098
  have eq13453 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ y) (σ (M.op x x)))) := by
    first
    | (have i₁ := eq9345 (σ (M.op x y))
       have i₂ := eq13100
       grind)
    | exact superpose eq13100 eq9345
    | exact resolve eq9345 eq13100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9345 eq13100
  have eq13488 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13453
       have i₂ := eq9402
       grind)
    | exact superpose eq9402 eq13453
    | exact resolve eq13453 eq9402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9402 eq13453
  have eq13854 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13488
       grind)
    | exact superpose eq13488 eq16
    | (have r₁ := eq16
       have r₂ := eq13488
       grind)
    | exact resolve eq16 eq13488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13488
  have eq13875 : False := by grind
  exact eq13875

/-- `Equation964`: `x = y ◇ ((z ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,X) else if X = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pxx_pxy_pyx_Equation964 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law964 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law964.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X1 X0))) = X0 := by
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
  have eq177 : ∀ X0 : G, y = (M.op x (M.op (M.op X0 x) (M.op x y))) := by
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
  have eq178 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) (σ x) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X1) (M.op X1 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op (M.op X3 X1) (M.op X1 X0)) X1 X2
       have i₂ := eq16 X0 X1 X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq570 : ∀ X0 : G, (M.op X0 (k (M.op X0 X0) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 X0 X0
       have i₂ := eq180 X0
       grind)
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq731 : (M.op x y) = (k y x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq18
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq744 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11 sF3 sF2
       grind)
    | exact superpose eq11 eq26
    | (have j1 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq786 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq787 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq786 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq786 X0
       have r₂ := eq13 X0 X0
       grind)
    | (have r₁ := eq786 (M.op x x)
       have r₂ := eq13 (M.op (M.op x x) (M.op x x)) x
       grind)
    | (have r₁ := eq786 x
       have r₂ := eq13 (k x x) x
       grind)
    | exact resolve eq786 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq786
  have eq791 : ∀ X0 : G, (M.op X0 (k (k X0 X0) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq570 X0
       have i₂ := eq787 X0
       grind)
    | exact superpose eq787 eq570
    | exact resolve eq570 eq787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570
  have eq794 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X0) (k X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X0 X1
       have i₂ := eq787 X0
       grind)
    | exact superpose eq787 eq16
    | exact resolve eq16 eq787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq795 : ∀ X0 X1 : G, (M.op X0 (M.op (k X0 X0) (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 X0
       have i₂ := eq787 X0
       grind)
    | exact superpose eq787 eq16
    | exact resolve eq16 eq787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq796 : y = (M.op x (M.op (k x x) (M.op x y))) := by
    first
    | (have i₁ := eq177 x
       have i₂ := eq787 x
       grind)
    | exact superpose eq787 eq177
    | exact resolve eq177 eq787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq801 : (σ y) = (M.op (σ x) (M.op (k (σ x) (σ x)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq178 sF2
       have i₂ := eq787 sF2
       grind)
    | exact superpose eq787 eq178
    | exact resolve eq178 eq787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq803 : ∀ X0 : G, (k (M.op X0 X0) X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq180 X0
       have i₂ := eq787 (M.op X0 X0)
       grind)
    | exact superpose eq787 eq180
    | exact resolve eq180 eq787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq820 : ∀ X0 : G, (k (k X0 X0) X0) = (k (k X0 X0) (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq803 X0
       have i₂ := eq787 X0
       grind)
    | exact superpose eq787 eq803
    | exact resolve eq803 eq787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803
  have eq873 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (k (σ (k X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq791 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq791
    | exact resolve eq791 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq898 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k (k X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq873 X0
       have i₂ := eq10 (k X0 X0) X0
       grind)
    | exact superpose eq10 eq873
    | exact resolve eq873 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873
  have eq1081 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op X1 X0)) = (M.op X1 (M.op (k X1 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq795 X1 (M.op (M.op X2 X1) (M.op X1 X0))
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq795
    | exact resolve eq795 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1083 : ∀ X0 X1 : G, (M.op (k X1 X1) (M.op X1 X0)) = (M.op X1 (M.op (k X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq795 X1 (M.op (k X1 X1) (M.op X1 X0))
       have i₂ := eq795 X1 X0
       grind)
    | exact superpose eq795 eq795
    | exact resolve eq795 eq795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1094 : (M.op (k x x) (M.op x y)) = (M.op x (M.op (k x x) y)) := by
    first
    | exact superpose eq796 eq795
    | exact resolve eq795 eq796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq796
  have eq1103 : (M.op (k (σ x) (σ x)) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (k (σ x) (σ x)) (σ y))) := by
    first
    | exact superpose eq801 eq795
    | exact resolve eq795 eq801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq801
  have eq1506 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq731
       grind)
    | exact superpose eq731 eq39
    | exact resolve eq39 eq731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq731
  have eq1507 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1506
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1506
    | exact resolve eq1506 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1506
  have eq1509 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq1507
    | exact resolve eq1507 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1507
  have eq1511 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq1509
       have i₂ := eq787 x
       grind)
    | exact superpose eq787 eq1509
    | exact resolve eq1509 eq787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1509
  have eq1837 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X0) = (M.op X2 (M.op (M.op X3 X2) (M.op (k X2 X2) (M.op X2 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq179 (M.op (k X2 X2) (M.op X2 X0)) X2 X3 X1
       have i₂ := eq795 X2 X0
       grind)
    | exact superpose eq795 eq179
    | exact resolve eq179 eq795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1945 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X0 x
       have i₂ := eq179 X2 X0 X1 x
       grind)
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1961 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 (k X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq794 X1 x
       have i₂ := eq179 (k X1 X1) X1 x X0
       grind)
    | exact superpose eq179 eq794
    | exact resolve eq794 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq794
  have eq2062 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X2 (M.op (k X2 X2) X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1837 X0 X1 X2 X3
       have i₂ := eq1083 X0 X2
       grind)
    | exact superpose eq1083 eq1837
    | exact resolve eq1837 eq1083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1083 eq1837
  have eq2106 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X0) = (M.op (k X2 X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2062 X0 X1 X2 x
       have i₂ := eq16 (M.op (k X2 X2) X0) X2 x
       grind)
    | exact superpose eq16 eq2062
    | exact resolve eq2062 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2062
  have eq2387 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op (k X0 X0) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1945 X0 X0 X1
       have i₂ := eq787 X0
       grind)
    | exact superpose eq787 eq1945
    | exact resolve eq1945 eq787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2458 : ∀ X0 X1 : G, (k (k (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) = (M.op X1 (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1945 X1 X0 (k (k (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1))
       have i₂ := eq791 (M.op X0 X1)
       grind)
    | exact superpose eq791 eq1945
    | exact resolve eq1945 eq791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4480 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (k x x) ∨ x = y := by
    first
    | exact superpose eq1511 eq744
    | exact resolve eq744 eq1511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744 eq1511
  have eq4489 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (k x x) ∨ x = y := by
    first
    | (have r₁ := eq4480
       have r₂ := eq27
       grind)
    | exact resolve eq4480 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4480
  have eq4494 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq4489
       have i₂ := eq787 sF2
       grind)
    | exact superpose eq787 eq4489
    | exact resolve eq4489 eq787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4489
  have eq4497 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ x = y := by
    first
    | exact superpose eq4494 eq97
    | exact resolve eq97 eq4494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq4494
  have eq4517 : y = (k x x) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ x = y := by
    first
    | exact superpose eq31 eq4497
    | exact resolve eq4497 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4497
  have eq4518 : y = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq4517
  have eq4528 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq4518
       grind)
    | exact superpose eq4518 eq39
    | exact resolve eq39 eq4518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4532 : (k y x) = (k y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq820 x
       have i₂ := eq4518
       grind)
    | exact superpose eq4518 eq820
    | exact resolve eq820 eq4518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4536 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1961 X0 x
       have i₂ := eq4518
       grind)
    | exact superpose eq4518 eq1961
    | exact resolve eq1961 eq4518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4537 : ∀ X0 : G, (M.op x (M.op x (M.op y X0))) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq2387 x X0
       have i₂ := eq4518
       grind)
    | exact superpose eq4518 eq2387
    | exact resolve eq2387 eq4518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4538 : x = (M.op x (M.op (k x x) y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq4536 x
       have i₂ := eq1081 y x x
       grind)
    | exact superpose eq1081 eq4536
    | exact resolve eq4536 eq1081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4536
  have eq4541 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq4528
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4528
    | exact resolve eq4528 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4528
  have eq4543 : x = (M.op (k x x) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq4538
       have i₂ := eq1094
       grind)
    | exact superpose eq1094 eq4538
    | exact resolve eq4538 eq1094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1094 eq4538
  have eq4546 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq4541
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4541
    | exact resolve eq4541 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4541
  have eq4548 : x = (M.op y (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq4518 eq4543
    | exact resolve eq4543 eq4518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4518 eq4543
  have eq4558 : (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq4546 eq820
    | exact resolve eq820 eq4546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq820
  have eq4562 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq4546 eq1961
    | exact resolve eq1961 eq4546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1961
  have eq4563 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (M.op (σ y) X0))) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq4546 eq2387
    | exact resolve eq2387 eq4546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2387
  have eq4564 : (σ x) = (M.op (σ x) (M.op (k (σ x) (σ x)) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq4562 x
       have i₂ := eq1081 sF3 sF2 x
       grind)
    | exact superpose eq1081 eq4562
    | exact resolve eq4562 eq1081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1081 eq4562
  have eq4570 : (σ x) = (M.op (k (σ x) (σ x)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1103 eq4564
    | exact resolve eq4564 eq1103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1103 eq4564
  have eq4575 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq4546 eq4570
    | exact resolve eq4570 eq4546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4546 eq4570
  have eq4589 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op x y) (M.op x X0))) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq4548 eq1945
    | exact resolve eq1945 eq4548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1945 eq4548
  have eq4635 : ∀ X0 : G, (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq4575 eq2106
    | exact resolve eq2106 eq4575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4575
  have eq5197 : (k (k y y) y) = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq4537 (k (k y y) y)
       have i₂ := eq791 y
       grind)
    | exact superpose eq791 eq4537
    | exact resolve eq4537 eq791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4537
  have eq5234 : (k (k y y) y) = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq5197
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq5197
    | exact resolve eq5197 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5197
  have eq5256 : (M.op x (M.op x y)) = (k (k y x) y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq4532 eq5234
    | exact resolve eq5234 eq4532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4532 eq5234
  have eq6335 : (k (k (σ y) (σ y)) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq4563 (k (k sF3 sF3) sF3)
       have i₂ := eq791 sF3
       grind)
    | exact superpose eq791 eq4563
    | exact resolve eq4563 eq791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq791 eq4563
  have eq6375 : (k (k (σ y) (σ y)) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq26 eq6335
    | exact resolve eq6335 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6335
  have eq6403 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (k (σ y) (σ x)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq4558 eq6375
    | exact resolve eq6375 eq4558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4558 eq6375
  have eq8906 : (k (σ (k y x)) (σ y)) = (σ (M.op x (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq40 (k y x)
       have i₂ := eq5256
       grind)
    | exact superpose eq5256 eq40
    | exact resolve eq40 eq5256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq5256
  have eq8913 : (k (k (σ y) (σ x)) (σ y)) = (σ (M.op x (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq8906
       have i₂ := eq39 y
       grind)
    | exact superpose eq39 eq8906
    | exact resolve eq8906 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8906
  have eq8917 : (k (k (σ y) (σ x)) (σ y)) = (σ (M.op x (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq8913
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq8913
    | exact resolve eq8913 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8913
  have eq8919 : (M.op (σ x) (M.op (σ x) (σ y))) = (σ (M.op x (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq6403 eq8917
    | exact resolve eq8917 eq6403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6403 eq8917
  have eq9038 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ (k (k (M.op x (M.op x y)) (M.op x (M.op x y))) (M.op x (M.op x y))))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq8919 eq898
    | exact resolve eq898 eq8919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq898 eq8919
  have eq9039 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ (k (k (M.op x (M.op x y)) (M.op x (M.op x y))) (M.op x (M.op x y))))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq9038
       have i₂ := eq2106 (σ (k (k (M.op x sF0) (M.op x sF0)) (M.op x sF0))) sF2 sF4
       grind)
    | exact superpose eq2106 eq9038
    | exact resolve eq9038 eq2106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2106 eq9038
  have eq9047 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ (M.op (M.op x y) (M.op (M.op x y) (M.op x (M.op x y)))))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq9039
       have i₂ := eq2458 x sF0
       grind)
    | exact superpose eq2458 eq9039
    | exact resolve eq9039 eq2458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2458 eq9039
  have eq9049 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq4589 eq9047
    | exact resolve eq9047 eq4589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4589 eq9047
  have eq9051 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq9049
    | exact resolve eq9049 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9049
  have eq9053 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq4635 eq9051
    | exact resolve eq9051 eq4635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4635 eq9051
  have eq9068 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (k (σ x) (σ x)) (M.op (σ x) (σ (M.op x y))))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq9053 eq795
    | exact resolve eq795 eq9053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9053
  have eq9084 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq9068
       have i₂ := eq795 sF2 sF1
       grind)
    | exact superpose eq795 eq9068
    | exact resolve eq9068 eq795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq795 eq9068
  have eq9104 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq9084
       have r₂ := eq27
       grind)
    | exact resolve eq9084 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9084
  have eq9120 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq9104 eq31
    | exact resolve eq31 eq9104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq9104
  have eq9171 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq9120
    | exact resolve eq9120 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq9120
  have eq9172 : x = y := by grind
  clear eq9171
  have eq9176 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq9172
       grind)
    | exact superpose eq9172 eq18
    | exact resolve eq18 eq9172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq9177 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq9172
       grind)
    | exact superpose eq9172 eq24
    | exact resolve eq24 eq9172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq9172
  have eq9203 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq9177
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq9177
    | exact resolve eq9177 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9177
  have eq9204 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq9176
       have i₂ := eq787 x
       grind)
    | exact superpose eq787 eq9176
    | exact resolve eq9176 eq787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9176
  have eq9213 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq9203 eq26
    | exact resolve eq26 eq9203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq9203
  have eq9265 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq9213
       have i₂ := eq787 sF2
       grind)
    | exact superpose eq787 eq9213
    | exact resolve eq9213 eq787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787 eq9213
  have eq9278 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq9204
       grind)
    | exact superpose eq9204 eq39
    | exact resolve eq39 eq9204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq9204
  have eq9295 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq9278
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq9278
    | exact resolve eq9278 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq9278
  have eq9302 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9265 eq9295
    | exact resolve eq9295 eq9265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9265 eq9295
  have eq9308 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq9302
    | exact resolve eq9302 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq9302
  have eq9310 : False := by grind
  exact eq9310

/-- `Equation964`: `x = y ◇ ((z ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyy_pyx_pxy_pyx_Equation964 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law964 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law964.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
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
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) (M.op X2 X1)) = (M.op X2 (M.op (M.op X3 X2) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X0 X2) (M.op X2 X1)) X2 X3
       have i₂ := eq9 X1 X2 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X3) (M.op X3 (M.op (M.op X0 (M.op X2 X3)) (M.op (M.op X2 X3) X1)))) = (M.op X3 X1) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq54 X4 (M.op (M.op X0 (M.op X2 X3)) (M.op (M.op X2 X3) X1)) X3 X2
       have i₂ := eq9 X1 (M.op X2 X3) X0
       grind)
    | exact superpose eq9 eq54
    | exact resolve eq54 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X2 X3 : G, (M.op X0 (M.op X0 (M.op (M.op X3 X0) X2))) = X2 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq9 X2 X0 x
       have i₂ := eq54 x X2 X0 X3
       grind)
    | exact superpose eq54 eq9
    | exact resolve eq9 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X0 x
       have i₂ := eq54 X1 (M.op X0 X2) X0 x
       grind)
    | exact superpose eq54 eq9
    | exact resolve eq9 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) (M.op (M.op X3 (M.op X1 X2)) X0)) = (M.op X2 (M.op X2 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq70 X2 (M.op (M.op X1 X2) (M.op (M.op X3 (M.op X1 X2)) X0)) X1
       have i₂ := eq70 (M.op X1 X2) X0 X3
       grind)
    | exact superpose eq70 eq70
    | exact resolve eq70 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op (M.op X4 X1) (M.op X1 (M.op (M.op X2 X1) X0)))) = (M.op (M.op X3 X1) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq54 X3 (M.op X1 (M.op (M.op X2 X1) X0)) X1 X4
       have i₂ := eq70 X1 X0 X2
       grind)
    | exact superpose eq70 eq54
    | exact resolve eq54 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq93 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) X0) = (M.op (M.op X3 X1) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq88 X0 X1 X2 X3 x
       have i₂ := eq9 (M.op (M.op X2 X1) X0) X1 x
       grind)
    | exact superpose eq9 eq88
    | exact resolve eq88 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq110 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 (M.op X2 X1)) X0) = (M.op (M.op X2 X1) (M.op (M.op X4 (M.op X2 X1)) (M.op X1 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq54 X3 (M.op X1 (M.op X1 X0)) (M.op X2 X1) X4
       have i₂ := eq74 X1 X2 X0
       grind)
    | exact superpose eq74 eq54
    | exact resolve eq54 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 X1 X3 X4 : G, (M.op X0 (M.op (M.op X1 (M.op X1 X0)) X3)) = (M.op (M.op X1 (M.op X1 X0)) (M.op (M.op X4 (M.op X1 (M.op X1 X0))) X3)) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq54 (M.op x X1) X3 (M.op X1 (M.op X1 X0)) X4
       have i₂ := eq74 X1 x X0
       grind)
    | exact superpose eq74 eq54
    | exact resolve eq54 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq74
  have eq115 : ∀ X0 X1 X3 : G, (M.op X0 (M.op (M.op X1 (M.op X1 X0)) X3)) = (M.op (M.op X1 X0) (M.op (M.op X1 X0) X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq111 X0 X1 X3 x
       have i₂ := eq85 X3 X1 (M.op X1 X0) x
       grind)
    | exact superpose eq85 eq111
    | exact resolve eq111 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq116 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X1)) X0) = (M.op X1 (M.op X1 (M.op X1 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq110 X0 X1 X2 X3 x
       have i₂ := eq85 (M.op X1 (M.op X1 X0)) X2 X1 x
       grind)
    | exact superpose eq85 eq110
    | exact resolve eq110 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq110
  have eq269 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq271 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq269 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq269
    | (have j0 := eq269 (σ X0)
       grind)
    | exact resolve eq269 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1188 : ∀ X0 X1 X2 : G, X1 ≠ X1 ∨ (M.op X1 X2) = (k X2 X1) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X2 X1
       have j1 := eq14 X0 X1
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
  have eq1300 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (k X2 X1) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1188 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1188
  have eq2250 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 (M.op X0 (M.op X2 X3))) X1) = (M.op (M.op X5 X3) (M.op (M.op X2 X3) (M.op (M.op X2 X3) (M.op (M.op X2 X3) X1)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq93 (M.op (M.op X2 X3) (M.op (M.op X2 X3) (M.op (M.op X2 X3) X1))) X3 X5 X2
       have i₂ := eq116 X1 (M.op X2 X3) X0 X4
       grind)
    | exact superpose eq116 eq93
    | exact resolve eq93 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq116
  have eq2259 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 (M.op X0 (M.op X2 X3))) X1) = (M.op (M.op X5 X3) (M.op X3 (M.op (M.op X2 (M.op X2 X3)) (M.op (M.op X2 X3) X1)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq2250 X0 X1 X2 X3 X4 X5
       have i₂ := eq115 X3 X2 (M.op (M.op X2 X3) X1)
       grind)
    | exact superpose eq115 eq2250
    | exact resolve eq2250 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq2250
  have eq2380 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X1) = (M.op (M.op X4 (M.op X0 (M.op X2 X3))) X1) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2259 X0 X1 X2 X3 X4 x
       have i₂ := eq66 X2 X1 X2 X3 x
       grind)
    | exact superpose eq66 eq2259
    | exact resolve eq2259 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq2259
  have eq10701 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1300 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1300
  have eq10702 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq10701 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10701
  have eq10799 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X1 X2
       have i₂ := eq10702 X0 X1
       grind)
    | (have i₁ := eq9 X0 X0 X2
       have i₂ := eq10702 X0 X1
       grind)
    | exact superpose eq10702 eq9
    | (have j1 := eq10702 X0 X1
       grind)
    | exact resolve eq9 eq10702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10919 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X4) = (M.op (M.op X2 (M.op X3 (M.op X1 X1))) X4) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2380 X3 X4 X0 X0 X2
       have i₂ := eq10702 X0 X1
       grind)
    | (have i₁ := eq2380 X0 X1 X1 X1 X4
       have i₂ := eq10702 X0 X1
       grind)
    | exact superpose eq10702 eq2380
    | (have j1 := eq10702 X0 X1
       grind)
    | exact resolve eq2380 eq10702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10702
  have eq10979 : ∀ X0 X1 X4 : G, (M.op X1 X4) = (M.op X0 X4) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq10919 X0 X1 x x X4
       have i₂ := eq2380 x X4 X1 X1 x
       grind)
    | exact superpose eq2380 eq10919
    | (have j0 := eq10919 X0 X1 x x X4
       grind)
    | exact resolve eq10919 eq2380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2380 eq10919
  have eq11079 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X1 X0))) = X0 ∨ (M.op X2 X1) = (k X1 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 X2 X3
       have i₂ := eq10979 X1 X2 X0
       grind)
    | (have i₁ := eq9 x X0 X2
       have i₂ := eq10979 X0 X1 x
       grind)
    | exact superpose eq10979 eq9
    | (have j1 := eq10979 X1 X2 x
       grind)
    | exact resolve eq9 eq10979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10979
  have eq19313 : ∀ X0 X2 : G, X0 = X2 ∨ (M.op X2 X0) = (k X0 X2) ∨ (M.op X2 X0) = (k X0 X2) := by
    intro X0 X2
    first
    | (have i₁ := eq10799 X0 X2 x
       have i₂ := eq11079 X0 X0 X2 x
       grind)
    | exact superpose eq11079 eq10799
    | (have j0 := eq10799 X0 X2 X2
       have j1 := eq11079 X0 X0 X2 x
       grind)
    | exact resolve eq10799 eq11079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10799 eq11079
  have eq19349 : ∀ X0 X2 : G, (M.op X2 X0) = (k X0 X2) ∨ X0 = X2 := by
    intro X0 X2
    first
    | (have j0 := eq19313 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19313
  have eq19381 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19349 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq19349
    | (have j0 := eq19349 (σ (k X0 X1)) (M.op (σ X1) (σ X0))
       grind)
    | exact resolve eq19349 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19392 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq19349 X1 (τ X0)
       grind)
    | exact superpose eq19349 eq18
    | (have j1 := eq19349 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq18 eq19349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq19349
  have eq19477 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19392 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq19392
    | exact resolve eq19392 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19392
  have eq19547 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19477 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq19477
    | (have j0 := eq19477 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq19477 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19477
  have eq19713 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19381 y x
       grind)
    | exact superpose eq19381 eq16
    | (have j1 := eq19381 x y
       grind)
    | exact resolve eq16 eq19381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19381
  have eq19807 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq19713
       have i₂ := eq19547 x y
       grind)
    | exact superpose eq19547 eq19713
    | (have j1 := eq19547 (σ x) (σ y)
       grind)
    | (have r₁ := eq19713
       have r₂ := eq19547 x y
       grind)
    | (have r₁ := eq19713
       have r₂ := eq19547 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq19713
       have r₂ := eq19547 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq19713 eq19547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19547 eq19713
  have eq19808 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq19807
  have eq20069 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq19808
       grind)
    | exact superpose eq19808 eq10
    | exact resolve eq10 eq19808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19808
  have eq20107 : x = y ∨ x = y := by
    first
    | (have i₁ := eq20069
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq20069
    | exact resolve eq20069 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20069
  have eq20108 : x = y := by grind
  clear eq20107
  have eq20109 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20108
       grind)
    | exact superpose eq20108 eq16
    | exact resolve eq16 eq20108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20108
  have eq20110 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq20109
       have i₂ := eq271 x
       grind)
    | exact superpose eq271 eq20109
    | (have j1 := eq271 x
       grind)
    | exact resolve eq20109 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq22364 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq20110
       have i₂ := eq269 x
       grind)
    | exact superpose eq269 eq20110
    | (have j1 := eq269 (σ x)
       grind)
    | exact resolve eq20110 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22367 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq22364
  have eq22380 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) X0) = (k X0 (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (σ x)
       have i₂ := eq22367
       grind)
    | exact superpose eq22367 eq12
    | (have j0 := eq12 X0 (σ x)
       grind)
    | (have r₁ := eq12 X0 (σ x)
       have r₂ := eq22367
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq22367
       grind)
    | exact resolve eq12 eq22367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22487 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq22380 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22380
  have eq22506 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (k X0 x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq22487 (σ X0)
       have i₂ := eq15 X0 x
       grind)
    | exact superpose eq15 eq22487
    | exact resolve eq22487 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22487
  have eq22544 : (σ x) = (σ (k x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq22367
       have i₂ := eq22506 x
       grind)
    | exact superpose eq22506 eq22367
    | exact resolve eq22367 eq22506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22367 eq22506
  have eq22665 : (σ x) = (σ (k x x)) ∨ x = (M.op x x) := by grind
  clear eq22544
  have eq22677 : (τ (σ x)) = (k x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (k x x)
       have i₂ := eq22665
       grind)
    | exact superpose eq22665 eq10
    | exact resolve eq10 eq22665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22665
  have eq22725 : x = (k x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq22677
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq22677
    | exact resolve eq22677 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22677
  have eq22732 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq269 x
       have i₂ := eq22725
       grind)
    | exact superpose eq22725 eq269
    | (have j0 := eq269 x
       grind)
    | exact resolve eq269 eq22725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269 eq22725
  have eq22735 : x = (M.op x x) := by grind
  clear eq22732
  have eq22749 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq22735
       grind)
    | exact superpose eq22735 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq22735
       grind)
    | exact resolve eq12 eq22735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22848 : ∀ X0 : G, (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq22749 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22749
  have eq22907 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq20110
       have i₂ := eq22848 x
       grind)
    | exact superpose eq22848 eq20110
    | exact resolve eq20110 eq22848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20110 eq22848
  have eq22910 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq22907
  have eq22935 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq20109
       have i₂ := eq22910
       grind)
    | exact superpose eq22910 eq20109
    | exact resolve eq20109 eq22910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20109 eq22910
  have eq23066 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq22935
       have i₂ := eq22735
       grind)
    | exact superpose eq22735 eq22935
    | exact resolve eq22935 eq22735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22735 eq22935
  have eq23067 : False := by grind
  exact eq23067

/-- `Equation964`: `x = y ◇ ((z ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pyx_pxx_pyx_Equation964 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law964 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law964.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) := by
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
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) (M.op X2 X1)) = (M.op X2 (M.op (M.op X3 X2) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X0 X2) (M.op X2 X1)) X2 X3
       have i₂ := eq9 X1 X2 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17 (σ y) (σ x)
       grind)
    | exact superpose eq17 eq16
    | (have j1 := eq17 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq57
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq57
    | exact resolve eq57 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq83 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X5 X1) (M.op X1 (M.op (M.op X4 (M.op X0 X1)) X3))) = (M.op X1 (M.op (M.op X2 (M.op X0 X1)) (M.op (M.op X0 X1) X3))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq55 X5 (M.op (M.op X4 (M.op X0 X1)) X3) X1 X0
       have i₂ := eq55 X2 X3 (M.op X0 X1) X4
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X2 X3 : G, (M.op X0 (M.op X0 (M.op (M.op X3 X0) X2))) = X2 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq9 X2 X0 x
       have i₂ := eq55 x X2 X0 X3
       grind)
    | exact superpose eq55 eq9
    | exact resolve eq9 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X0 x
       have i₂ := eq55 X1 (M.op X0 X2) X0 x
       grind)
    | exact superpose eq55 eq9
    | exact resolve eq9 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X2 X3)) (M.op (M.op X2 X3) X1)) = (M.op X3 (M.op X3 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq88 X3 (M.op (M.op X0 (M.op X2 X3)) (M.op (M.op X2 X3) X1)) X2
       have i₂ := eq9 X1 (M.op X2 X3) X0
       grind)
    | exact superpose eq9 eq88
    | exact resolve eq88 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 (M.op X0 X1)) X3) = (M.op X1 (M.op X1 (M.op (M.op X2 (M.op X0 X1)) (M.op (M.op X0 X1) X3)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq88 X1 (M.op (M.op X4 (M.op X0 X1)) X3) X0
       have i₂ := eq55 X2 X3 (M.op X0 X1) X4
       grind)
    | exact superpose eq55 eq88
    | exact resolve eq88 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) (M.op (M.op X3 (M.op X1 X2)) X0)) = (M.op X2 (M.op X2 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq88 X2 (M.op (M.op X1 X2) (M.op (M.op X3 (M.op X1 X2)) X0)) X1
       have i₂ := eq88 (M.op X1 X2) X0 X3
       grind)
    | exact superpose eq88 eq88
    | exact resolve eq88 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X1) X0) = (M.op X1 (M.op (M.op X4 X1) (M.op X1 (M.op (M.op X2 X1) X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq55 X3 (M.op X1 (M.op (M.op X2 X1) X0)) X1 X4
       have i₂ := eq88 X1 X0 X2
       grind)
    | exact superpose eq88 eq55
    | exact resolve eq55 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X1) X0) = (M.op (M.op X2 X1) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq116 X0 X1 X2 X3 x
       have i₂ := eq9 (M.op (M.op X2 X1) X0) X1 x
       grind)
    | exact superpose eq9 eq116
    | exact resolve eq116 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq131 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X4 (M.op X0 X1)) X3) = (M.op X1 (M.op X1 (M.op X1 (M.op X1 X3)))) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq107 X0 X1 x X3 X4
       have i₂ := eq106 x X3 X0 X1
       grind)
    | exact superpose eq106 eq107
    | exact resolve eq107 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq134 : ∀ X0 X1 X3 X4 X5 : G, (M.op (M.op X5 X1) (M.op X1 (M.op (M.op X4 (M.op X0 X1)) X3))) = (M.op X1 (M.op X1 (M.op X1 X3))) := by
    intro X0 X1 X3 X4 X5
    first
    | (have i₁ := eq83 X0 X1 x X3 X4 X5
       have i₂ := eq106 x X3 X0 X1
       grind)
    | exact superpose eq106 eq83
    | exact resolve eq83 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq106
  have eq171 : ∀ X0 X1 X3 X4 : G, (M.op X0 (M.op (M.op X1 (M.op X1 X0)) X3)) = (M.op (M.op X1 (M.op X1 X0)) (M.op (M.op X4 (M.op X1 (M.op X1 X0))) X3)) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq55 (M.op x X1) X3 (M.op X1 (M.op X1 X0)) X4
       have i₂ := eq94 X1 x X0
       grind)
    | exact superpose eq94 eq55
    | exact resolve eq55 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X3 : G, (M.op X0 (M.op (M.op X1 (M.op X1 X0)) X3)) = (M.op (M.op X1 X0) (M.op (M.op X1 X0) X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq171 X0 X1 X3 x
       have i₂ := eq108 X3 X1 (M.op X1 X0) x
       grind)
    | exact superpose eq108 eq171
    | exact resolve eq171 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq171
  have eq778 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq780 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq778 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq778 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq778 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778
  have eq783 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq780 X1
       grind)
    | exact superpose eq780 eq12
    | (have j0 := eq12 X0 X1
       grind)
    | exact resolve eq12 eq780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq784 : ∀ X0 X1 : G, (k X1 X1) = X1 ∨ (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq780 X1
       grind)
    | exact superpose eq780 eq13
    | (have j0 := eq13 X0 X1
       grind)
    | exact resolve eq13 eq780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq801 : ∀ X0 X1 : G, (k X1 X1) = X1 ∨ (k X0 X1) = (k X0 X0) ∨ (M.op X1 X0) ≠ (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq784 X0 X1
       have i₂ := eq780 X0
       grind)
    | exact superpose eq780 eq784
    | (have j0 := eq784 X0 X1
       grind)
    | exact resolve eq784 eq780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq784
  have eq809 : ∀ X0 X1 : G, (M.op X0 (M.op (k X0 X0) (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 X0
       have i₂ := eq780 X0
       grind)
    | exact superpose eq780 eq9
    | exact resolve eq9 eq780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq823 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op (k X0 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq122 X2 X0 X1 X0
       have i₂ := eq780 X0
       grind)
    | exact superpose eq780 eq122
    | exact resolve eq122 eq780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq842 : ∀ X0 : G, (M.op X0 (M.op (k X0 X0) (k X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq809 X0 X0
       have i₂ := eq780 X0
       grind)
    | exact superpose eq780 eq809
    | exact resolve eq809 eq780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq809
  have eq898 : ∀ X0 : G, (M.op X0 (k (k X0 X0) (k X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq842 X0
       have i₂ := eq780 (k X0 X0)
       grind)
    | exact superpose eq780 eq842
    | exact resolve eq842 eq780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842
  have eq1200 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (k (σ (k X0 X0)) (σ (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq898 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq898
    | exact resolve eq898 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq898
  have eq1254 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k (k X0 X0) (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq1200 X0
       have i₂ := eq15 (k X0 X0) (k X0 X0)
       grind)
    | exact superpose eq15 eq1200
    | exact resolve eq1200 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1200
  have eq1301 : ∀ X0 X1 X2 : G, (M.op (σ (k X0 X0)) X1) = (M.op (M.op X2 (σ X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq823 (σ X0) X2 X1
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq823
    | exact resolve eq823 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1701 : ∀ X1 X2 X3 : G, (M.op (M.op X3 (σ X1)) (M.op (σ X1) X2)) = (M.op (σ X1) (M.op (σ (k X1 X1)) X2)) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq55 X3 X2 (σ X1) x
       have i₂ := eq1301 X1 X2 x
       grind)
    | exact superpose eq1301 eq55
    | exact resolve eq55 eq1301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq1301
  have eq3876 : ∀ X0 X1 X2 : G, X1 ≠ X1 ∨ (M.op X1 X2) = (k X2 X1) ∨ (k X0 X1) = (k X0 X0) ∨ (M.op X1 X0) ≠ (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq783 X2 X1
       have i₂ := eq801 X0 X1
       grind)
    | exact superpose eq801 eq783
    | (have j0 := eq783 X2 X1
       have j1 := eq801 X0 X1
       grind)
    | (have r₁ := eq783 X0 X1
       have r₂ := eq801 X0 X1
       grind)
    | exact resolve eq783 eq801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq783 eq801
  have eq3898 : ∀ X0 X1 X2 : G, (k X0 X1) = (k X0 X0) ∨ (M.op X1 X2) = (k X2 X1) ∨ (M.op X1 X0) ≠ (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq3876 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3876
  have eq11990 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 (M.op X1 (M.op X2 X3))) X4) = (M.op (M.op X5 X3) (M.op (M.op X2 X3) (M.op (M.op X2 X3) (M.op (M.op X2 X3) X4)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq122 (M.op (M.op X2 X3) (M.op (M.op X2 X3) (M.op (M.op X2 X3) X4))) X3 X2 X5
       have i₂ := eq131 X1 (M.op X2 X3) X4 X0
       grind)
    | exact superpose eq131 eq122
    | exact resolve eq122 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq131
  have eq12023 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 (M.op X1 (M.op X2 X3))) X4) = (M.op (M.op X5 X3) (M.op X3 (M.op (M.op X2 (M.op X2 X3)) (M.op (M.op X2 X3) X4)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq11990 X0 X1 X2 X3 X4 X5
       have i₂ := eq177 X3 X2 (M.op (M.op X2 X3) X4)
       grind)
    | exact superpose eq177 eq11990
    | exact resolve eq11990 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq11990
  have eq12340 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 (M.op X2 X3))) X4) = (M.op X3 (M.op X3 (M.op X3 (M.op (M.op X2 X3) X4)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq12023 X0 X1 X2 X3 X4 x
       have i₂ := eq134 X2 X3 (M.op (M.op X2 X3) X4) X2 x
       grind)
    | exact superpose eq134 eq12023
    | exact resolve eq12023 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134 eq12023
  have eq12565 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X4) = (M.op (M.op X0 (M.op X1 (M.op X2 X3))) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq12340 X0 X1 X2 X3 X4
       have i₂ := eq88 X3 X4 X2
       grind)
    | exact superpose eq88 eq12340
    | exact resolve eq12340 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq12340
  have eq13123 : ∀ X0 X2 X3 X4 : G, (M.op X2 X0) = (M.op (k (M.op X4 (M.op X3 X2)) (M.op X4 (M.op X3 X2))) X0) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq823 (M.op X4 (M.op X3 X2)) x X0
       have i₂ := eq12565 x X4 X3 X2 X0
       grind)
    | exact superpose eq12565 eq823
    | exact resolve eq823 eq12565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32548 : (σ (k y x)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq63
       have i₂ := eq17 y x
       grind)
    | exact superpose eq17 eq63
    | (have j1 := eq17 (σ y) (σ x)
       grind)
    | exact resolve eq63 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq32549 : (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq32548
  have eq32550 : (σ (k y x)) ≠ (σ (M.op y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq32549 eq63
    | exact resolve eq63 eq32549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq132943 : ∀ X0 X1 : G, (M.op y X1) = (M.op (k (M.op X0 (M.op y x)) (M.op X0 (M.op y x))) X1) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq13123 X0 y x x
       have i₂ := eq32549
       grind)
    | exact superpose eq32549 eq13123
    | exact resolve eq13123 eq32549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132949 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x X1) = (M.op y X1) := by
    intro X1
    first
    | (have i₁ := eq132943 x X1
       have i₂ := eq13123 X1 x y x
       grind)
    | exact superpose eq13123 eq132943
    | exact resolve eq132943 eq13123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132943
  have eq132956 : (M.op y x) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq132949 eq32549
    | exact resolve eq32549 eq132949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32549
  have eq132962 : (M.op y x) = (k y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq132956
       have i₂ := eq780 y
       grind)
    | exact superpose eq780 eq132956
    | exact resolve eq132956 eq780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132956
  have eq132963 : (σ (k y x)) ≠ (σ (k y y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq132962 eq32550
    | exact resolve eq32550 eq132962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32550
  have eq145325 : ∀ X0 : G, (σ (k y y)) ≠ (σ (k y y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x X0) = (k X0 x) ∨ (M.op x y) ≠ (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq132963
       have i₂ := eq3898 y x X0
       grind)
    | exact superpose eq3898 eq132963
    | (have j1 := eq3898 y x X0
       grind)
    | (have r₁ := eq132963
       have r₂ := eq3898 (σ y) (σ x) x
       grind)
    | (have r₁ := eq132963
       have r₂ := eq3898 (σ x) (σ y) x
       grind)
    | exact resolve eq132963 eq3898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3898
  have eq145326 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x X0) = (k X0 x) ∨ (M.op x y) ≠ (M.op y x) := by
    intro X0
    first
    | (have j0 := eq145325 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145325
  have eq170897 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ y) (σ x)) ∨ (M.op y X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq132949 X0
       grind)
    | exact superpose eq132949 eq16
    | (have j1 := eq132949 X0
       grind)
    | exact resolve eq16 eq132949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq170906 : ∀ X0 X1 X2 X3 : G, (M.op (σ y) X0) = (M.op (M.op X1 (M.op X2 (M.op (σ y) (σ x)))) X0) ∨ (M.op y X3) = (M.op x X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12565 X1 X2 (σ x) (σ y) X0
       have i₂ := eq132949 X3
       grind)
    | exact superpose eq132949 eq12565
    | (have j1 := eq132949 X3
       grind)
    | exact resolve eq12565 eq132949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq170907 : ∀ X0 X3 : G, (M.op y X3) = (M.op x X3) ∨ (M.op (σ y) X0) = (M.op (σ x) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq170906 X0 x x X3
       have i₂ := eq12565 x x (σ y) (σ x) X0
       grind)
    | exact superpose eq12565 eq170906
    | (have j0 := eq170906 X0 x x X3
       grind)
    | exact resolve eq170906 eq12565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170906
  have eq170916 : ∀ X1 : G, (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x X1) = (M.op y X1) := by
    intro X1
    first
    | exact superpose eq170907 eq132949
    | (have j0 := eq132949 X1
       have j1 := eq170907 x X1
       grind)
    | exact resolve eq132949 eq170907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132949 eq170907
  have eq170921 : ∀ X1 : G, (M.op (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (M.op x X1) = (M.op y X1) := by
    intro X1
    first
    | (have i₁ := eq170916 X1
       have i₂ := eq780 (σ y)
       grind)
    | exact superpose eq780 eq170916
    | (have j0 := eq170916 X1
       grind)
    | exact resolve eq170916 eq780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170916
  have eq170925 : ∀ X1 : G, (M.op (σ y) (σ x)) = (σ (k y y)) ∨ (M.op x X1) = (M.op y X1) := by
    intro X1
    first
    | (have i₁ := eq170921 X1
       have i₂ := eq15 y y
       grind)
    | exact superpose eq15 eq170921
    | (have j0 := eq170921 X1
       grind)
    | exact resolve eq170921 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170921
  have eq170927 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y y)) ∨ (M.op y X0) = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq170925 eq170897
    | (have j0 := eq170897 X0
       have j1 := eq170925 X0
       grind)
    | exact resolve eq170897 eq170925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170897
  have eq171067 : ∀ X0 X1 : G, (σ x) = (M.op (M.op X0 (σ y)) (M.op (σ y) (σ (k y y)))) ∨ (M.op x X1) = (M.op y X1) := by
    intro X0 X1
    first
    | (have i₁ := eq94 (σ y) X0 (σ x)
       have i₂ := eq170925 X1
       grind)
    | exact superpose eq170925 eq94
    | (have j1 := eq170925 X1
       grind)
    | exact resolve eq94 eq170925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq170925
  have eq171078 : ∀ X1 : G, (σ x) = (M.op (σ y) (M.op (σ (k y y)) (σ (k y y)))) ∨ (M.op x X1) = (M.op y X1) := by
    intro X1
    first
    | (have i₁ := eq171067 x X1
       have i₂ := eq1701 y (σ (k y y)) x
       grind)
    | exact superpose eq1701 eq171067
    | (have j0 := eq171067 x X1
       grind)
    | exact resolve eq171067 eq1701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1701 eq171067
  have eq171080 : ∀ X1 : G, (σ x) = (M.op (σ y) (k (σ (k y y)) (σ (k y y)))) ∨ (M.op x X1) = (M.op y X1) := by
    intro X1
    first
    | (have i₁ := eq171078 X1
       have i₂ := eq780 (σ (k y y))
       grind)
    | exact superpose eq780 eq171078
    | (have j0 := eq171078 X1
       grind)
    | exact resolve eq171078 eq780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171078
  have eq171081 : ∀ X1 : G, (σ x) = (M.op (σ y) (σ (k (k y y) (k y y)))) ∨ (M.op x X1) = (M.op y X1) := by
    intro X1
    first
    | (have i₁ := eq171080 X1
       have i₂ := eq15 (k y y) (k y y)
       grind)
    | exact superpose eq15 eq171080
    | (have j0 := eq171080 X1
       grind)
    | exact resolve eq171080 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171080
  have eq171082 : ∀ X1 : G, (σ x) = (σ y) ∨ (M.op x X1) = (M.op y X1) := by
    intro X1
    first
    | (have i₁ := eq171081 X1
       have i₂ := eq1254 y
       grind)
    | exact superpose eq1254 eq171081
    | (have j0 := eq171081 X1
       grind)
    | exact resolve eq171081 eq1254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1254 eq171081
  have eq171088 : ∀ X0 : G, x = (τ (σ y)) ∨ (M.op y X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq10 x
       have i₂ := eq171082 X0
       grind)
    | exact superpose eq171082 eq10
    | (have j1 := eq171082 X0
       grind)
    | exact resolve eq10 eq171082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171082
  have eq171144 : ∀ X0 : G, x = y ∨ (M.op y X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq171088 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq171088
    | (have j0 := eq171088 X0
       grind)
    | exact resolve eq171088 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171088
  have eq171158 : ∀ X0 : G, (σ (k y y)) ≠ (σ (M.op y y)) ∨ (M.op y X0) = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq171144 eq170927
    | (have j0 := eq170927 X0
       have j1 := eq171144 X0
       grind)
    | exact resolve eq170927 eq171144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170927 eq171144
  have eq171165 : ∀ X0 : G, (σ (k y y)) ≠ (σ (k y y)) ∨ (M.op y X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq171158 X0
       have i₂ := eq780 y
       grind)
    | exact superpose eq780 eq171158
    | (have j0 := eq171158 X0
       grind)
    | exact resolve eq171158 eq780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171158
  have eq171166 : ∀ X0 : G, (M.op y X0) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq171165 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171165
  have eq171167 : ∀ X0 : G, (M.op y X0) = (k X0 x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) ≠ (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq145326 X0
       have i₂ := eq171166 X0
       grind)
    | exact superpose eq171166 eq145326
    | exact resolve eq145326 eq171166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145326
  have eq171185 : (M.op (σ x) (σ y)) ≠ (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq171166 y
       grind)
    | exact superpose eq171166 eq16
    | exact resolve eq16 eq171166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq171201 : (M.op (σ x) (σ y)) ≠ (σ (k y y)) := by
    first
    | (have i₁ := eq171185
       have i₂ := eq780 y
       grind)
    | exact superpose eq780 eq171185
    | exact resolve eq171185 eq780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171185
  have eq171203 : ∀ X0 : G, (M.op y x) ≠ (M.op y y) ∨ (M.op y X0) = (k X0 x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq171167 X0
       have i₂ := eq171166 y
       grind)
    | exact superpose eq171166 eq171167
    | (have j0 := eq171167 X0
       grind)
    | exact resolve eq171167 eq171166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171166 eq171167
  have eq171205 : ∀ X0 : G, (M.op y x) ≠ (k y y) ∨ (M.op y X0) = (k X0 x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq171203 X0
       have i₂ := eq780 y
       grind)
    | exact superpose eq780 eq171203
    | (have j0 := eq171203 X0
       grind)
    | exact resolve eq171203 eq780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171203
  have eq171207 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op y X0) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq171205 X0
       grind)
    | (have r₁ := eq171205 X0
       have r₂ := eq132962
       grind)
    | exact resolve eq171205 eq132962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132962 eq171205
  have eq174680 : ∀ X0 : G, (M.op (σ y) (σ x)) ≠ (σ (k y y)) ∨ (M.op y X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq171201
       have i₂ := eq171207 X0
       grind)
    | exact superpose eq171207 eq171201
    | (have j1 := eq171207 X0
       grind)
    | exact resolve eq171201 eq171207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq174693 : ∀ X0 X1 X2 X3 : G, (M.op (σ y) X1) = (M.op (M.op X2 (M.op X3 (M.op (σ y) (σ x)))) X1) ∨ (M.op y X0) = (k X0 x) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12565 X2 X3 (σ x) (σ y) X1
       have i₂ := eq171207 X0
       grind)
    | exact superpose eq171207 eq12565
    | (have j1 := eq171207 X0
       grind)
    | exact resolve eq12565 eq171207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq174694 : ∀ X0 X1 : G, (M.op (σ y) X1) = (M.op (σ x) X1) ∨ (M.op y X0) = (k X0 x) := by
    intro X0 X1
    first
    | (have i₁ := eq174693 X0 X1 x x
       have i₂ := eq12565 x x (σ y) (σ x) X1
       grind)
    | exact superpose eq12565 eq174693
    | (have j0 := eq174693 X0 X1 x x
       grind)
    | exact resolve eq174693 eq12565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12565 eq174693
  have eq174703 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op y X0) = (k X0 x) := by
    intro X0
    first
    | exact superpose eq174694 eq171207
    | (have j0 := eq171207 X0
       have j1 := eq174694 X0 x
       grind)
    | exact resolve eq171207 eq174694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171207 eq174694
  have eq174709 : ∀ X0 : G, (M.op (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (M.op y X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq174703 X0
       have i₂ := eq780 (σ y)
       grind)
    | exact superpose eq780 eq174703
    | (have j0 := eq174703 X0
       grind)
    | exact resolve eq174703 eq780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174703
  have eq174713 : ∀ X0 : G, (M.op (σ y) (σ x)) = (σ (k y y)) ∨ (M.op y X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq174709 X0
       have i₂ := eq15 y y
       grind)
    | exact superpose eq15 eq174709
    | (have j0 := eq174709 X0
       grind)
    | exact resolve eq174709 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174709
  have eq174717 : ∀ X0 : G, (M.op y X0) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq174713 X0
       have j1 := eq174680 X0
       grind)
    | (have r₁ := eq174713 X0
       have r₂ := eq174680 X0
       grind)
    | exact resolve eq174713 eq174680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174680 eq174713
  have eq175033 : (k y x) = (k y y) := by
    first
    | (have i₁ := eq174717 y
       have i₂ := eq780 y
       grind)
    | exact superpose eq780 eq174717
    | exact resolve eq174717 eq780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175082 : ∀ X0 X1 : G, (M.op (k X0 X0) X1) = (M.op (k X0 x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq823 X0 y X1
       have i₂ := eq174717 X0
       grind)
    | exact superpose eq174717 eq823
    | exact resolve eq823 eq174717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq823
  have eq175260 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (k (k (M.op X0 X1) x) (k (M.op X0 X1) x)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13123 X0 X2 x y
       have i₂ := eq174717 (M.op x X2)
       grind)
    | exact superpose eq174717 eq13123
    | exact resolve eq13123 eq174717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13123 eq174717
  have eq179015 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (k (k (M.op X0 X1) x) x) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq175260 X0 X1 X2
       have i₂ := eq175082 (k (M.op X0 X1) x) X2
       grind)
    | exact superpose eq175082 eq175260
    | exact resolve eq175260 eq175082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175082 eq175260
  have eq183244 : (σ (k y y)) ≠ (σ (k y y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq132963
       have i₂ := eq175033
       grind)
    | exact superpose eq175033 eq132963
    | exact resolve eq132963 eq175033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132963 eq175033
  have eq183247 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq183244
  have eq189031 : (M.op (σ y) (σ x)) ≠ (σ (k y y)) := by
    first
    | (have i₁ := eq171201
       have i₂ := eq183247
       grind)
    | exact superpose eq183247 eq171201
    | exact resolve eq171201 eq183247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171201
  have eq202252 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (k (k (M.op (σ y) (σ x)) x) x) X0) := by
    intro X0
    first
    | (have i₁ := eq179015 (σ x) (σ y) X0
       have i₂ := eq183247
       grind)
    | exact superpose eq183247 eq179015
    | exact resolve eq179015 eq183247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq202322 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq202252 X0
       have i₂ := eq179015 (σ y) (σ x) X0
       grind)
    | exact superpose eq179015 eq202252
    | exact resolve eq202252 eq179015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179015 eq202252
  have eq202364 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq183247
       have i₂ := eq202322 (σ y)
       grind)
    | exact superpose eq202322 eq183247
    | exact resolve eq183247 eq202322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183247 eq202322
  have eq202372 : (M.op (σ y) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq202364
       have i₂ := eq780 (σ y)
       grind)
    | exact superpose eq780 eq202364
    | exact resolve eq202364 eq780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780 eq202364
  have eq202381 : (M.op (σ y) (σ x)) = (σ (k y y)) := by
    first
    | (have i₁ := eq202372
       have i₂ := eq15 y y
       grind)
    | exact superpose eq15 eq202372
    | exact resolve eq202372 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202372
  have eq202385 : False := by grind
  exact eq202385

/-- `Equation964`: `x = y ◇ ((z ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pyx_pyy_pyx_Equation964 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law964 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law964.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X1 X0))) = X0 := by
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
  have eq50 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op y X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 y x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X2 X0)) (M.op X0 (M.op (M.op (M.op X1 X2) (M.op X2 X0)) X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X2) (M.op X2 X0)) X2
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, y = (M.op x (M.op (M.op X0 x) (M.op x y))) := by
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
  have eq54 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X1) (M.op X1 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X3 X1) (M.op X1 X0)) X1 X2
       have i₂ := eq14 X0 X1 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq72 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq74 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq71
       have i₂ := eq74 y x
       grind)
    | exact superpose eq74 eq71
    | (have j1 := eq74 y x
       grind)
    | exact resolve eq71 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq96
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq96
    | exact resolve eq96 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq105 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq20 eq104
    | exact resolve eq104 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq106 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq105
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq105
    | exact resolve eq105 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq114 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq114 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq114 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq114 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq119 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq115 y
       grind)
    | exact superpose eq115 eq72
    | exact resolve eq72 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq124 : (σ (M.op y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq119
       have i₂ := eq115 sF3
       grind)
    | exact superpose eq115 eq119
    | exact resolve eq119 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq119
  have eq250 : ∀ X0 : G, (M.op (M.op x y) (M.op y X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq50 eq50
    | exact resolve eq50 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq252 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op y X0)) = (M.op y (M.op (M.op X1 y) X0)) := by
    intro X0 X1
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq254 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq256 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) = (M.op (σ y) (M.op (M.op X1 (σ y)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq478 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X1) (M.op X1 X0)) (M.op (M.op X4 (M.op (M.op X2 X1) (M.op X1 X0))) X3)) = (M.op X0 (M.op (M.op (M.op X2 X1) (M.op X1 X0)) X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq55 X3 (M.op (M.op X2 X1) (M.op X1 X0)) X4 X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq492 : ∀ X0 X1 X2 : G, (M.op (M.op X1 y) X0) = (M.op y (M.op (M.op X2 y) (M.op (M.op x y) (M.op y X0)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq50 eq55
    | exact resolve eq55 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq495 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (σ y)) X0) = (M.op (σ y) (M.op (M.op X2 (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq55
    | exact resolve eq55 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq579 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X3 X4))) X0) = (M.op (M.op (M.op X2 X3) (M.op X3 X4)) (M.op (M.op X5 (M.op (M.op X2 X3) (M.op X3 X4))) (M.op X4 (M.op (M.op (M.op X2 X3) (M.op X3 X4)) X0)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq55 (M.op X4 (M.op (M.op (M.op X2 X3) (M.op X3 X4)) X0)) (M.op (M.op X2 X3) (M.op X3 X4)) X5 X1
       have i₂ := eq52 X4 X2 X3 X0
       grind)
    | exact superpose eq52 eq55
    | exact resolve eq55 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq969 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq106 eq74
    | (have j0 := eq74 (σ y) (σ x)
       grind)
    | exact resolve eq74 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq970 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq969
    | exact resolve eq969 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq969
  have eq973 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq970
       have r₂ := eq27
       grind)
    | exact resolve eq970 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq970
  have eq975 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq973
    | exact resolve eq973 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq973
  have eq979 : (σ y) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq975 eq54
    | exact resolve eq54 eq975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq981 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq975 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq975
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq975
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq975
       grind)
    | exact resolve eq12 eq975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq988 : (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq981
       have r₂ := eq26
       grind)
    | exact resolve eq981 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq981
  have eq1394 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) X0)) = (M.op y (M.op (M.op X1 y) X0)) := by
    intro X0 X1
    first
    | exact superpose eq250 eq252
    | exact resolve eq252 eq250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252
  have eq1499 : ∀ X0 X1 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (σ y) (M.op (M.op X1 (σ y)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq254 eq256
    | exact resolve eq256 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256
  have eq1990 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq988 eq106
    | exact resolve eq106 eq988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq988
  have eq1993 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq1990
  have eq2011 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq1993 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq1993
       grind)
    | exact resolve eq13 eq1993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1993
  have eq2022 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq2011 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2011
  have eq2363 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2022 eq106
    | exact resolve eq106 eq2022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq2022
  have eq2370 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq2363
  have eq2376 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq2370
    | exact resolve eq2370 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2370
  have eq2379 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq2376
       have r₂ := eq27
       grind)
    | exact resolve eq2376 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2376
  have eq5440 : ∀ X0 X1 : G, (M.op (M.op X1 y) X0) = (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op y X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq492 X0 X1 x
       have i₂ := eq1394 (M.op sF0 (M.op y X0)) X1
       grind)
    | (have i₁ := eq492 X0 X1 X1
       have i₂ := eq1394 (M.op sF0 (M.op y X0)) X1
       grind)
    | exact superpose eq1394 eq492
    | (have j0 := eq492 X0 X1 x
       grind)
    | exact resolve eq492 eq1394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492 eq1394
  have eq5441 : ∀ X0 X1 : G, (M.op (M.op X1 y) X0) = (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) X0)))) := by
    intro X0 X1
    first
    | exact superpose eq250 eq5440
    | exact resolve eq5440 eq250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250 eq5440
  have eq5442 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op X1 y) X0) := by
    intro X0 X1
    first
    | exact superpose eq50 eq5441
    | exact resolve eq5441 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5441
  have eq5696 : ∀ X0 X1 : G, (M.op (M.op X1 (σ y)) X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)))) := by
    intro X0 X1
    first
    | exact superpose eq1499 eq495
    | (have j0 := eq495 X0 X1 (σ x)
       grind)
    | exact resolve eq495 eq1499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq495 eq1499
  have eq5697 : ∀ X0 X1 : G, (M.op (M.op X1 (σ y)) X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)))) := by
    intro X0 X1
    first
    | exact superpose eq254 eq5696
    | exact resolve eq5696 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254 eq5696
  have eq5698 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op X1 (σ y)) X0) := by
    intro X0 X1
    first
    | exact superpose eq51 eq5697
    | exact resolve eq5697 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq5697
  have eq66880 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X3 X4))) X0) = (M.op X4 (M.op (M.op (M.op X2 X3) (M.op X3 X4)) (M.op X4 (M.op (M.op (M.op X2 X3) (M.op X3 X4)) X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq579 X0 X1 X2 X3 X4 x
       have i₂ := eq478 X4 X3 X2 (M.op X4 (M.op (M.op (M.op X2 X3) (M.op X3 X4)) X0)) x
       grind)
    | exact superpose eq478 eq579
    | exact resolve eq579 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478 eq579
  have eq66881 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 X0) = (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X3 X4))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq66880 X0 X1 X2 X3 X4
       have i₂ := eq52 X4 X2 X3 X0
       grind)
    | exact superpose eq52 eq66880
    | exact resolve eq66880 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq66880
  have eq67515 : ∀ X0 X1 X2 : G, (M.op (σ x) X0) = (M.op (M.op X1 (M.op (M.op X2 (σ y)) (M.op (σ x) (σ y)))) X0) ∨ (M.op x y) = (M.op y x) := by
    intro X0 X1 X2
    first
    | exact superpose eq975 eq66881
    | exact resolve eq66881 eq975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68284 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (M.op X1 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) X0) ∨ (M.op x y) = (M.op y x) := by
    intro X0 X1
    first
    | exact superpose eq5698 eq67515
    | (have j0 := eq67515 X0 X1 (σ x)
       grind)
    | exact resolve eq67515 eq5698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5698 eq67515
  have eq68503 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) X0) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y x) := by
    intro X0
    first
    | exact superpose eq979 eq68284
    | exact resolve eq68284 eq979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq979 eq68284
  have eq68984 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) X0) ∨ (M.op x y) = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq68503 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68503
  have eq69132 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq68984 eq975
    | exact resolve eq975 eq68984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq975 eq68984
  have eq69453 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq69132
  have eq71293 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq69453 eq2379
    | exact resolve eq2379 eq69453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2379 eq69453
  have eq71463 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq71293
  have eq71479 : (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq71463
       have r₂ := eq27
       grind)
    | exact resolve eq71463 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71463
  have eq71488 : x = (M.op y (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq71479
       grind)
    | exact superpose eq71479 eq50
    | exact resolve eq50 eq71479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq71489 : y = (M.op x (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq53 y
       have i₂ := eq71479
       grind)
    | exact superpose eq71479 eq53
    | exact resolve eq53 eq71479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq71590 : ∀ X0 X1 X2 : G, (M.op x X0) = (M.op (M.op X1 (M.op (M.op X2 y) (M.op x y))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq66881 X0 X1 X2 y x
       have i₂ := eq71479
       grind)
    | exact superpose eq71479 eq66881
    | exact resolve eq66881 eq71479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66881 eq71479
  have eq71591 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op X1 (M.op (M.op x y) (M.op x y))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq71590 X0 X1 x
       have i₂ := eq5442 sF0 X1
       grind)
    | (have i₁ := eq71590 X0 X1 X1
       have i₂ := eq5442 sF0 X1
       grind)
    | exact superpose eq5442 eq71590
    | (have j0 := eq71590 X0 X1 x
       grind)
    | exact resolve eq71590 eq5442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5442 eq71590
  have eq75763 : ∀ X0 : G, (M.op y X0) = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq71489 eq71591
    | exact resolve eq71591 eq71489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71591
  have eq76405 : x = (M.op x (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq71488
       have i₂ := eq75763 (M.op sF0 sF0)
       grind)
    | exact superpose eq75763 eq71488
    | exact resolve eq71488 eq75763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71488
  have eq76417 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq124
       have i₂ := eq75763 y
       grind)
    | exact superpose eq75763 eq124
    | exact resolve eq124 eq75763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq75763
  have eq76753 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq76417
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq76417
    | exact resolve eq76417 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq76417
  have eq76761 : x = y := by
    first
    | exact superpose eq71489 eq76405
    | exact resolve eq76405 eq71489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71489 eq76405
  have eq76833 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq20 eq76753
    | exact resolve eq76753 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq76753
  have eq76890 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq76761
       grind)
    | exact superpose eq76761 eq24
    | exact resolve eq24 eq76761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq76761
  have eq76962 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq76890
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq76890
    | exact resolve eq76890 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq76890
  have eq76970 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq76962 eq26
    | exact resolve eq26 eq76962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq77300 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq76962 eq76833
    | exact resolve eq76833 eq76962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76833 eq76962
  have eq77453 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq77300 eq76970
    | exact resolve eq76970 eq77300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76970 eq77300
  have eq77454 : False := by grind
  exact eq77454

/-- `Equation964`: `x = y ◇ ((z ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyy_x_pyx_y_pyx_Equation964 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law964 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law964.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq63 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X1) (M.op X1 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X3 X1) (M.op X1 X0)) X1 X2
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X0 x
       have i₂ := eq63 X2 X0 X1 x
       grind)
    | exact superpose eq63 eq9
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X1 (M.op X1 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1 x
       have i₂ := eq63 (M.op X1 X2) X1 x X0
       grind)
    | exact superpose eq63 eq9
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 X0)) = (M.op (M.op X2 X1) (M.op (M.op X3 (M.op X2 X1)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq83 X1 X2 (M.op (M.op X2 X1) (M.op (M.op X3 (M.op X2 X1)) X0))
       have i₂ := eq83 (M.op X2 X1) X3 X0
       grind)
    | exact superpose eq83 eq83
    | exact resolve eq83 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X2) X0) = (M.op X2 (M.op (M.op X4 X2) (M.op X2 (M.op (M.op X3 X2) X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq63 (M.op X2 (M.op (M.op X3 X2) X0)) X2 X4 X1
       have i₂ := eq83 X2 X3 X0
       grind)
    | exact superpose eq83 eq63
    | exact resolve eq63 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X0) = (M.op (M.op X3 X2) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq102 X0 X1 X2 X3 x
       have i₂ := eq9 (M.op (M.op X3 X2) X0) X2 x
       grind)
    | exact superpose eq9 eq102
    | exact resolve eq102 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq190 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op X1 (M.op X2 (M.op X2 X0))) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq107 X3 X1 (M.op X2 (M.op X2 X0)) (M.op x X2)
       have i₂ := eq88 x X2 X0
       grind)
    | exact superpose eq88 eq107
    | exact resolve eq107 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq228 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X1) (M.op (M.op X5 (M.op X4 X1)) X2)) = (M.op (M.op X3 (M.op X4 X1)) (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq63 X2 (M.op X4 X1) X5 X3
       have i₂ := eq107 X2 X4 X1 X0
       grind)
    | (have i₁ := eq63 X2 (M.op X4 X1) X5 X3
       have i₂ := eq107 X2 X0 X1 X4
       grind)
    | exact superpose eq107 eq63
    | exact resolve eq63 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq244 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X1 X2)) = (M.op (M.op X3 (M.op X4 X1)) (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq228 X0 X1 X2 X3 X4 x
       have i₂ := eq99 X2 X1 X4 x
       grind)
    | exact superpose eq99 eq228
    | exact resolve eq228 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq228
  have eq266 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op X1 X0)) X2) = (M.op (M.op X3 (M.op (M.op X4 X1) X0)) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq190 (M.op X1 (M.op X1 X0)) X3 (M.op X4 X1) X2
       have i₂ := eq88 X4 X1 X0
       grind)
    | exact superpose eq88 eq190
    | exact resolve eq190 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq409 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) X0)) = X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X1 X2
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq14 (M.op X1 X0) X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X1 X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq420 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ X0 = X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq438 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq440 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq438 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq438 (M.op X1 X0) (k X0 X1)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq438 (k X0 X1) (M.op X1 X0)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq438 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq438 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438
  have eq449 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq420 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq420 (M.op X1 X1) X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq420 X1 (M.op X1 X1)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq420 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq420 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420
  have eq460 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) X0)) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq409 X0 X1 X2
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq409 X0 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq409 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409
  have eq477 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq449 X0 X1
       have j1 := eq440 X1 X0
       grind)
    | (have r₁ := eq449 X0 X1
       have r₂ := eq440 (k X0 X1) X1
       grind)
    | (have r₁ := eq449 X0 X0
       have r₂ := eq440 X0 (k X0 X0)
       grind)
    | (have r₁ := eq449 X0 X1
       have r₂ := eq440 X0 X1
       grind)
    | exact resolve eq449 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449
  have eq483 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq440 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440
  have eq489 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq483 (σ X0)
       grind)
    | exact superpose eq483 eq15
    | exact resolve eq15 eq483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq491 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq483 (τ X0)
       grind)
    | exact superpose eq483 eq32
    | exact resolve eq32 eq483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq496 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq491 X0
       have i₂ := eq483 X0
       grind)
    | exact superpose eq483 eq491
    | exact resolve eq491 eq483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491
  have eq498 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq489 X0
       have i₂ := eq483 X0
       grind)
    | exact superpose eq483 eq489
    | exact resolve eq489 eq483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489
  have eq548 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = X1 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (σ X0)
       have i₂ := eq498 X0
       grind)
    | exact superpose eq498 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq550 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq498 X0
       grind)
    | exact superpose eq498 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq552 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq548 X0 X1
       have j1 := eq550 X0 X1
       grind)
    | (have r₁ := eq548 X0 X1
       have r₂ := eq550 X0 X1
       grind)
    | (have r₁ := eq548 X0 (σ (M.op (M.op X0 X0) (M.op X0 X0)))
       have r₂ := eq550 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq548 X0 (σ X0)
       have r₂ := eq550 X0 X1
       grind)
    | exact resolve eq548 eq550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548 eq550
  have eq570 : ∀ X0 X1 : G, (τ X0) = (M.op (M.op X1 (τ X0)) (M.op (τ X0) (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq88 X1 (τ X0) (τ X0)
       have i₂ := eq496 X0
       grind)
    | exact superpose eq496 eq88
    | exact resolve eq88 eq496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq572 : ∀ X0 X1 X2 : G, (M.op (τ (M.op X0 X0)) X2) = (M.op (M.op X1 (τ X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq107 X2 X1 (τ X0) (τ X0)
       have i₂ := eq496 X0
       grind)
    | exact superpose eq496 eq107
    | exact resolve eq107 eq496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq596 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq477 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477
  have eq604 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (k (M.op (M.op X2 X1) (M.op X1 X0)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq596 (M.op (M.op X2 X1) (M.op X1 X0)) X1
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq596
    | (have j0 := eq596 (M.op (M.op X2 X1) (M.op X1 X0)) X1
       grind)
    | (have r₁ := eq596 (M.op (M.op X2 X0) (M.op X0 X0)) X0
       have r₂ := eq9 X0 X0 X2
       grind)
    | exact resolve eq596 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596
  have eq958 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) (M.op X1 X1)) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq604 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604
  have eq959 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq958 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq958 X0 X1
       have i₂ := eq14 (M.op X0 X1) X1
       grind)
    | exact superpose eq14 eq958
    | (have j1 := eq14 X1 X1
       grind)
    | exact resolve eq958 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq958
  have eq1020 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq959 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq959 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq959 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq959
  have eq1528 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op (M.op X0 X0) X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq483 (M.op X0 X0)
       have i₂ := eq1020 X0 (M.op X0 X0)
       grind)
    | exact superpose eq1020 eq483
    | (have j1 := eq1020 X0 (M.op X0 X0)
       grind)
    | exact resolve eq483 eq1020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483 eq1020
  have eq1537 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq1528 X0
       have j1 := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq1528 X0
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact resolve eq1528 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1528
  have eq1552 : ∀ X0 : G, (M.op (τ (M.op X0 X0)) (τ X0)) = (k (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1537 (τ X0)
       have i₂ := eq496 X0
       grind)
    | exact superpose eq496 eq1537
    | exact resolve eq1537 eq496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1563 : ∀ X0 : G, (M.op (τ (M.op X0 X0)) (τ X0)) = (τ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1552 X0
       have i₂ := eq32 (M.op X0 X0) X0
       grind)
    | exact superpose eq32 eq1552
    | exact resolve eq1552 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq1552
  have eq1572 : ∀ X0 : G, (M.op (τ (M.op X0 X0)) (τ X0)) = (τ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq1563 X0
       have i₂ := eq1537 X0
       grind)
    | exact superpose eq1537 eq1563
    | exact resolve eq1563 eq1537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1537 eq1563
  have eq2461 : ∀ X0 X1 : G, (M.op (M.op X1 (τ X0)) (τ X0)) = (τ (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq572 X0 X1 (τ X0)
       have i₂ := eq1572 X0
       grind)
    | exact superpose eq1572 eq572
    | exact resolve eq572 eq1572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572 eq1572
  have eq3369 : ∀ X0 X1 X2 : G, (τ (M.op (M.op (M.op (M.op X1 X1) X1) (M.op (M.op X1 X1) X1)) (M.op (M.op X1 X1) X1))) = (M.op (M.op X2 (M.op (M.op X0 (τ X1)) (τ X1))) (M.op (M.op X0 (τ X1)) (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2461 (M.op (M.op X0 X0) X0) X1
       have i₂ := eq2461 X0 X1
       grind)
    | exact superpose eq2461 eq2461
    | exact resolve eq2461 eq2461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2461
  have eq3472 : ∀ X1 : G, (τ (M.op (M.op (M.op (M.op X1 X1) X1) (M.op (M.op X1 X1) X1)) (M.op (M.op X1 X1) X1))) = (M.op (τ X1) (M.op (τ X1) (τ X1))) := by
    intro X1
    first
    | (have i₁ := eq3369 x X1 x
       have i₂ := eq244 x (τ X1) (τ X1) x (M.op x (τ X1))
       grind)
    | exact superpose eq244 eq3369
    | exact resolve eq3369 eq244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3369
  have eq3502 : ∀ X1 : G, (M.op (τ X1) (τ (M.op X1 X1))) = (τ (M.op (M.op (M.op (M.op X1 X1) X1) (M.op (M.op X1 X1) X1)) (M.op (M.op X1 X1) X1))) := by
    intro X1
    first
    | (have i₁ := eq3472 X1
       have i₂ := eq496 X1
       grind)
    | exact superpose eq496 eq3472
    | exact resolve eq3472 eq496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496 eq3472
  have eq3520 : ∀ X1 : G, (M.op (τ X1) (τ (M.op X1 X1))) = (τ (M.op (M.op X1 (M.op X1 X1)) (M.op (M.op X1 X1) X1))) := by
    intro X1
    first
    | (have i₁ := eq3502 X1
       have i₂ := eq266 X1 X1 (M.op (M.op X1 X1) X1) (M.op (M.op X1 X1) X1) X1
       grind)
    | exact superpose eq266 eq3502
    | exact resolve eq3502 eq266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266 eq3502
  have eq3524 : ∀ X1 : G, (M.op (τ X1) (τ (M.op X1 X1))) = (τ (M.op X1 (M.op X1 X1))) := by
    intro X1
    first
    | (have i₁ := eq3520 X1
       have i₂ := eq244 X1 X1 X1 X1 X1
       grind)
    | exact superpose eq244 eq3520
    | exact resolve eq3520 eq244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244 eq3520
  have eq3525 : ∀ X0 X1 : G, (τ X0) = (M.op (M.op X1 (τ X0)) (τ (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq570 X0 X1
       have i₂ := eq3524 X0
       grind)
    | exact superpose eq3524 eq570
    | exact resolve eq570 eq3524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570 eq3524
  have eq3567 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op (M.op X1 (τ (σ X0))) (τ (M.op (σ X0) (σ (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq3525 (σ X0) X1
       have i₂ := eq498 X0
       grind)
    | exact superpose eq498 eq3525
    | exact resolve eq3525 eq498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498 eq3525
  have eq3630 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (τ (M.op (σ X0) (σ (M.op X0 X0))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3567 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3567
    | exact resolve eq3567 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3567
  have eq3919 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (τ (M.op (σ X0) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq83 X0 x (τ (M.op (σ X0) (σ (M.op X0 X0))))
       have i₂ := eq3630 X0 x
       grind)
    | exact superpose eq3630 eq83
    | exact resolve eq83 eq3630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3630
  have eq4100 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ (M.op X0 X0)))
       have i₂ := eq3919 X0
       grind)
    | exact superpose eq3919 eq11
    | exact resolve eq11 eq3919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3919
  have eq4993 : ∀ X0 X2 : G, (M.op X0 X0) = X2 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X2
    first
    | (have i₁ := eq83 X0 x X2
       have i₂ := eq460 X2 X0 x
       grind)
    | exact superpose eq460 eq83
    | (have j1 := eq460 X2 X0 X2
       grind)
    | exact resolve eq83 eq460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq460
  have eq13483 : ∀ X0 X1 : G, (τ X0) = (M.op X1 X1) ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq552 X1 X0
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq552 X0 (σ X0)
       grind)
    | exact superpose eq552 eq10
    | (have j1 := eq552 X1 X0
       grind)
    | exact resolve eq10 eq552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552
  have eq16570 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq13483 (σ X1) X0
       grind)
    | exact superpose eq13483 eq15
    | (have j1 := eq13483 (σ X1) X0
       grind)
    | exact resolve eq15 eq13483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13483
  have eq16582 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16570 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq16570
    | (have j0 := eq16570 X0 X1
       grind)
    | exact resolve eq16570 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16570
  have eq19788 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16582 X0 X1
       have i₂ := eq4993 X0 X1
       grind)
    | exact superpose eq4993 eq16582
    | (have j0 := eq16582 X0 X1
       have j1 := eq4993 X0 X1
       grind)
    | exact resolve eq16582 eq4993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4993 eq16582
  have eq20022 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq19788 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19788
  have eq22894 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4100 X0
       have i₂ := eq20022 X0 X1
       grind)
    | (have i₁ := eq4100 X0
       have i₂ := eq20022 X0 (M.op X0 X0)
       grind)
    | exact superpose eq20022 eq4100
    | (have j1 := eq20022 X1 X0
       grind)
    | exact resolve eq4100 eq20022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4100 eq20022
  have eq23020 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq22894 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22894
  have eq23620 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq23020 y x
       grind)
    | exact superpose eq23020 eq16
    | (have r₁ := eq16
       have r₂ := eq23020 y x
       grind)
    | exact resolve eq16 eq23020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23020
  have eq23622 : False := by grind
  exact eq23622

/-- `Equation964`: `x = y ◇ ((z ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pyy_pxy_Equation964 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law964 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law964.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X2 X0)) (M.op X0 (M.op (M.op (M.op X1 X2) (M.op X2 X0)) X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X2) (M.op X2 X0)) X2
       have i₂ := eq9 X0 X2 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X1) (M.op X1 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X3 X1) (M.op X1 X0)) X1 X2
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq18
  have eq31 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq27 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq27
    | exact resolve eq27 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq32 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq31
  have eq56 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X2 X2) ∨ X1 = X2 ∨ (M.op X2 X2) = (k X1 X2) ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X2
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X2
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X1 X1)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) = (M.op X0 (M.op X1 X1)) ∨ (M.op X1 (M.op X0 X0)) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 X1
       have i₂ := eq14 X0 (M.op X1 X1)
       grind)
    | (have i₁ := eq9 x x x
       have i₂ := eq14 (M.op x x) X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 (M.op X1 X1)
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X0) = (M.op (M.op X1 X2) (M.op X2 (M.op (M.op X3 (M.op X4 X2)) (M.op (M.op X4 X2) X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq25 (M.op (M.op X3 (M.op X4 X2)) (M.op (M.op X4 X2) X0)) X2 X4 X1
       have i₂ := eq9 X0 (M.op X4 X2) X3
       grind)
    | exact superpose eq9 eq25
    | exact resolve eq25 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X1 X2)) = (M.op (M.op X3 X1) (M.op X1 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq25 X2 X1 x X0
       have i₂ := eq25 X2 X1 x X3
       grind)
    | exact superpose eq25 eq25
    | exact resolve eq25 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X0 x
       have i₂ := eq25 X2 X0 X1 x
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X2) = (M.op (M.op X3 X0) (M.op (M.op X4 (M.op X3 X0)) (M.op X0 (M.op (M.op X1 X0) X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 (M.op X0 X2) (M.op X3 X0) X4
       have i₂ := eq25 X2 X0 X1 X3
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X1 (M.op X1 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1 x
       have i₂ := eq25 (M.op X1 X2) X1 x X0
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op (M.op X1 X2) (M.op X2 X3)) X0)) = (M.op (M.op (M.op X1 X2) (M.op X2 X3)) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq24 X3 X1 X2 (M.op X3 (M.op (M.op (M.op X1 X2) (M.op X2 X3)) X0))
       have i₂ := eq24 X3 X1 X2 X0
       grind)
    | exact superpose eq24 eq24
    | exact resolve eq24 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq172 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq32 X0
       grind)
    | exact superpose eq32 eq10
    | exact resolve eq10 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq399 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 X0)) = (M.op (M.op X2 X1) (M.op (M.op X3 (M.op X2 X1)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq106 X1 X2 (M.op (M.op X2 X1) (M.op (M.op X3 (M.op X2 X1)) X0))
       have i₂ := eq106 (M.op X2 X1) X3 X0
       grind)
    | exact superpose eq106 eq106
    | exact resolve eq106 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq410 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X2) X0) = (M.op X2 (M.op (M.op X4 X2) (M.op X2 (M.op (M.op X3 X2) X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq25 (M.op X2 (M.op (M.op X3 X2) X0)) X2 X4 X1
       have i₂ := eq106 X2 X3 X0
       grind)
    | exact superpose eq106 eq25
    | exact resolve eq25 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq421 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X0) = (M.op (M.op X3 X2) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq410 X0 X1 X2 X3 x
       have i₂ := eq9 (M.op (M.op X3 X2) X0) X2 x
       grind)
    | exact superpose eq9 eq410
    | exact resolve eq410 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410
  have eq482 : ∀ X0 X1 : G, (M.op (τ (M.op X0 X0)) (M.op (τ X0) (M.op (τ X0) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq113 (τ X0) (τ X0) X1
       have i₂ := eq172 X0
       grind)
    | exact superpose eq172 eq113
    | exact resolve eq113 eq172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172
  have eq511 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op X2 X3)) X0) = (M.op (M.op X2 X3) (M.op (M.op X4 (M.op X2 X3)) (M.op X3 (M.op X3 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq25 (M.op X3 (M.op X3 X0)) (M.op X2 X3) X4 X1
       have i₂ := eq113 X2 X3 X0
       grind)
    | exact superpose eq113 eq25
    | exact resolve eq25 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq512 : ∀ X0 X2 X3 X4 : G, (M.op X0 (M.op (M.op X2 (M.op X2 X0)) X3)) = (M.op (M.op X2 (M.op X2 X0)) (M.op (M.op X4 (M.op X2 (M.op X2 X0))) X3)) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq25 X3 (M.op X2 (M.op X2 X0)) X4 (M.op x X2)
       have i₂ := eq113 x X2 X0
       grind)
    | exact superpose eq113 eq25
    | exact resolve eq25 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq518 : ∀ X0 X2 X3 : G, (M.op (M.op X2 X0) (M.op (M.op X2 X0) X3)) = (M.op X0 (M.op (M.op X2 (M.op X2 X0)) X3)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq512 X0 X2 X3 x
       have i₂ := eq399 X3 (M.op X2 X0) X2 x
       grind)
    | exact superpose eq399 eq512
    | exact resolve eq512 eq399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512
  have eq519 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 X3)) X0) = (M.op X3 (M.op X3 (M.op X3 (M.op X3 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq511 X0 X1 X2 X3 x
       have i₂ := eq399 (M.op X3 (M.op X3 X0)) X3 X2 x
       grind)
    | exact superpose eq399 eq511
    | exact resolve eq511 eq399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511
  have eq623 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op X1 (M.op X2 (M.op X2 X0))) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq421 X3 X1 (M.op X2 (M.op X2 X0)) (M.op x X2)
       have i₂ := eq113 x X2 X0
       grind)
    | exact superpose eq113 eq421
    | exact resolve eq421 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2263 : ∀ X0 X1 : G, X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq56 X1 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq2264 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq2263 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2263
  have eq6115 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq2264 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2264
  have eq17445 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X2 (M.op (M.op X4 (M.op X1 X2)) X3)) = (M.op (M.op X5 X2) (M.op (M.op X6 (M.op X5 X2)) (M.op X2 (M.op (M.op X0 (M.op X1 X2)) (M.op (M.op X1 X2) X3))))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq107 X2 X1 (M.op (M.op X4 (M.op X1 X2)) X3) X5 X6
       have i₂ := eq25 X3 (M.op X1 X2) X4 X0
       grind)
    | exact superpose eq25 eq107
    | exact resolve eq107 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq17490 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) X3) = (M.op (M.op X1 (M.op X1 X0)) (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X1 X0)) X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq107 (M.op X1 X0) X2 X3 X1 x
       have i₂ := eq623 X0 x X1 (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X1 X0)) X3))
       grind)
    | exact superpose eq623 eq107
    | exact resolve eq107 eq623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623
  have eq17531 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X0 (M.op X0 X1))) = (M.op (M.op X3 (M.op X2 X0)) (M.op X0 (M.op (M.op X4 X0) X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq106 X0 X2 (M.op (M.op X3 (M.op X2 X0)) (M.op X0 (M.op (M.op X4 X0) X1)))
       have i₂ := eq107 X0 X4 X1 X2 X3
       grind)
    | exact superpose eq107 eq106
    | exact resolve eq106 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq107
  have eq17664 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) X3) = (M.op X0 (M.op X0 (M.op X0 (M.op (M.op X2 (M.op X1 X0)) X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq17490 X0 X1 X2 X3
       have i₂ := eq17531 X0 (M.op (M.op X2 (M.op X1 X0)) X3) X1 X1 X1
       grind)
    | exact superpose eq17531 eq17490
    | exact resolve eq17490 eq17531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17490 eq17531
  have eq17702 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X4 (M.op X1 X2)) X3)) = (M.op X2 (M.op X2 (M.op X2 (M.op (M.op X0 (M.op X1 X2)) (M.op (M.op X1 X2) X3))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq17445 X0 X1 X2 X3 X4 x x
       have i₂ := eq399 (M.op X2 (M.op (M.op X0 (M.op X1 X2)) (M.op (M.op X1 X2) X3))) X2 x x
       grind)
    | exact superpose eq399 eq17445
    | exact resolve eq17445 eq399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399 eq17445
  have eq17943 : ∀ X1 X2 X3 X4 : G, (M.op (M.op X1 X2) (M.op (M.op X1 X2) X3)) = (M.op X2 (M.op (M.op X4 (M.op X1 X2)) X3)) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq17702 x X1 X2 X3 X4
       have i₂ := eq17664 X2 X1 x (M.op (M.op X1 X2) X3)
       grind)
    | exact superpose eq17664 eq17702
    | exact resolve eq17702 eq17664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17664 eq17702
  have eq26993 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) X3) = (M.op (M.op X2 X2) (M.op (M.op X2 X2) (M.op (M.op X2 X2) (M.op (M.op X2 X2) X3)))) ∨ (M.op X2 (M.op X0 X0)) = (k X2 (M.op X0 X0)) ∨ (M.op X0 X0) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq519 X3 X1 X0 (M.op X2 X2)
       have i₂ := eq62 X2 X0
       grind)
    | exact superpose eq62 eq519
    | (have j1 := eq62 X2 X0
       grind)
    | exact resolve eq519 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq27671 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 (M.op X1 (M.op X2 X3))) X4) = (M.op (M.op X5 X3) (M.op (M.op X2 X3) (M.op (M.op X2 X3) (M.op (M.op X2 X3) X4)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq421 (M.op (M.op X2 X3) (M.op (M.op X2 X3) (M.op (M.op X2 X3) X4))) X5 X3 X2
       have i₂ := eq519 X4 X0 X1 (M.op X2 X3)
       grind)
    | exact superpose eq519 eq421
    | exact resolve eq421 eq519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421 eq519
  have eq27730 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 (M.op X1 (M.op X2 X3))) X4) = (M.op (M.op X5 X3) (M.op X3 (M.op (M.op X2 (M.op X2 X3)) (M.op (M.op X2 X3) X4)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq27671 X0 X1 X2 X3 X4 X5
       have i₂ := eq518 X3 X2 (M.op (M.op X2 X3) X4)
       grind)
    | exact superpose eq518 eq27671
    | exact resolve eq27671 eq518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27671
  have eq28148 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) X3) = (M.op X2 (M.op (M.op X2 (M.op X2 X2)) (M.op (M.op X2 X2) (M.op (M.op X2 X2) X3)))) ∨ (M.op X2 (M.op X0 X0)) = (k X2 (M.op X0 X0)) ∨ (M.op X0 X0) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq26993 X0 X1 X2 X3
       have i₂ := eq518 X2 X2 (M.op (M.op X2 X2) (M.op (M.op X2 X2) X3))
       grind)
    | exact superpose eq518 eq26993
    | (have j0 := eq26993 X0 X1 X2 X3
       grind)
    | exact resolve eq26993 eq518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26993
  have eq28181 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X4) = (M.op (M.op X0 (M.op X1 (M.op X2 X3))) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq27730 X0 X1 X2 X3 X4 x
       have i₂ := eq100 X4 x X3 X2 X2
       grind)
    | exact superpose eq100 eq27730
    | exact resolve eq27730 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq27730
  have eq28428 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op X1 X0) X3) ∨ (M.op X2 (M.op X0 X0)) = (k X2 (M.op X0 X0)) ∨ (M.op X0 X0) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq28148 X0 X1 X2 X3
       have i₂ := eq113 X2 (M.op X2 X2) X3
       grind)
    | exact superpose eq113 eq28148
    | (have j0 := eq28148 X0 X1 X2 X3
       grind)
    | exact resolve eq28148 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28148
  have eq42251 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X1 X1)) ≠ (M.op (M.op X0 X1) (M.op X1 X1)) ∨ (M.op X2 (M.op X1 X1)) = (k X2 (M.op X1 X1)) ∨ (M.op X1 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6115 X2 (M.op X1 X1)
       have i₂ := eq105 X1 X1 X1 X0
       grind)
    | (have i₁ := eq6115 X2 (M.op X1 X1)
       have i₂ := eq105 X0 X1 X1 X1
       grind)
    | exact superpose eq105 eq6115
    | (have j0 := eq6115 X2 (M.op X1 X1)
       grind)
    | (have r₁ := eq6115 (M.op x X2) (M.op X2 X2)
       have r₂ := eq105 X2 X2 X2 x
       grind)
    | (have r₁ := eq6115 (M.op X0 X2) (M.op X2 X2)
       have r₂ := eq105 X0 X2 X2 X2
       grind)
    | exact resolve eq6115 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq6115
  have eq42340 : ∀ X1 X2 : G, (M.op X2 (M.op X1 X1)) = (k X2 (M.op X1 X1)) ∨ (M.op X1 X1) = X2 := by
    intro X1 X2
    first
    | (have j0 := eq42251 x X1 X2
       have j1 := eq28428 X1 X1 X2 x
       grind)
    | (have r₁ := eq42251 X1 x X2
       have r₂ := eq28428 x X1 X2 (M.op x x)
       grind)
    | (have r₁ := eq42251 x X1 (M.op X1 x)
       have r₂ := eq28428 x X1 (M.op x X1) (M.op X1 X1)
       grind)
    | (have r₁ := eq42251 x X1 (M.op X1 X1)
       have r₂ := eq28428 (M.op X1 X1) X1 (M.op (M.op x X1) (M.op X1 X1)) x
       grind)
    | exact resolve eq42251 eq28428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28428 eq42251
  have eq44862 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) (M.op (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) (M.op X1 (M.op X0 X1))))) = (k X2 (M.op (M.op X0 X1) (M.op (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) (M.op X1 (M.op X0 X1))))) ∨ (M.op (M.op X0 X1) (M.op (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) (M.op X1 (M.op X0 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq42340 (M.op (M.op X1 X2) (M.op X2 (M.op X1 X2))) X2
       have i₂ := eq148 (M.op X2 (M.op X1 X2)) X1 X2 (M.op X1 X2)
       grind)
    | exact superpose eq148 eq42340
    | exact resolve eq42340 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148 eq42340
  have eq44911 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X1 (M.op X0 X1)) (M.op (M.op X1 (M.op X0 X1)) (M.op X1 (M.op X0 X1))))) = (k X2 (M.op (M.op X1 (M.op X0 X1)) (M.op (M.op X1 (M.op X0 X1)) (M.op X1 (M.op X0 X1))))) ∨ (M.op (M.op X0 X1) (M.op (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) (M.op X1 (M.op X0 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq44862 X0 X1 X2
       have i₂ := eq17943 X1 (M.op X0 X1) (M.op X1 (M.op X0 X1)) (M.op X0 X1)
       grind)
    | exact superpose eq17943 eq44862
    | (have j0 := eq44862 X0 X1 X2
       grind)
    | exact resolve eq44862 eq17943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44862
  have eq44914 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) (M.op (M.op X1 (M.op X1 (M.op X0 X1))) (M.op X1 (M.op X0 X1))))) = (k X2 (M.op (M.op X0 X1) (M.op (M.op X1 (M.op X1 (M.op X0 X1))) (M.op X1 (M.op X0 X1))))) ∨ (M.op (M.op X0 X1) (M.op (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) (M.op X1 (M.op X0 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq44911 X0 X2 X2
       have i₂ := eq518 (M.op X0 X2) X2 (M.op X2 (M.op X0 X2))
       grind)
    | exact superpose eq518 eq44911
    | (have j0 := eq44911 X0 X1 X2
       grind)
    | exact resolve eq44911 eq518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44911
  have eq44916 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) (M.op X1 (M.op X1 (M.op X0 X1))))) = (k X2 (M.op (M.op X0 X1) (M.op X1 (M.op X1 (M.op X0 X1))))) ∨ (M.op (M.op X0 X1) (M.op (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) (M.op X1 (M.op X0 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq44914 X2 x X2
       have i₂ := eq28181 x x X2 x (M.op x (M.op X2 x))
       grind)
    | exact superpose eq28181 eq44914
    | (have j0 := eq44914 X0 X1 X2
       grind)
    | exact resolve eq44914 eq28181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44914
  have eq44917 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (k X2 (M.op X0 X1)) ∨ (M.op (M.op X0 X1) (M.op (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) (M.op X1 (M.op X0 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq44916 X0 X1 X2
       have i₂ := eq113 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq113 eq44916
    | (have j0 := eq44916 X0 X1 X2
       grind)
    | exact resolve eq44916 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44916
  have eq44918 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X1)) (M.op (M.op X1 (M.op X0 X1)) (M.op X1 (M.op X0 X1)))) = X2 ∨ (M.op X2 (M.op X0 X1)) = (k X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq44917 X0 X1 X2
       have i₂ := eq17943 X1 (M.op X0 X1) (M.op X1 (M.op X0 X1)) (M.op X0 X1)
       grind)
    | exact superpose eq17943 eq44917
    | (have j0 := eq44917 X0 X1 X2
       grind)
    | exact resolve eq44917 eq17943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17943 eq44917
  have eq44919 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X1 (M.op X1 (M.op X0 X1))) (M.op X1 (M.op X0 X1)))) = X2 ∨ (M.op X2 (M.op X0 X1)) = (k X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq44918 X0 X1 X2
       have i₂ := eq518 (M.op X0 X1) X1 (M.op X1 (M.op X0 X1))
       grind)
    | exact superpose eq518 eq44918
    | (have j0 := eq44918 X0 X1 X2
       grind)
    | exact resolve eq44918 eq518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518 eq44918
  have eq44920 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X1 (M.op X1 (M.op X0 X1)))) = X2 ∨ (M.op X2 (M.op X0 X1)) = (k X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq44919 X0 X1 X2
       have i₂ := eq28181 X1 X1 X0 X1 (M.op X1 (M.op X0 X1))
       grind)
    | exact superpose eq28181 eq44919
    | (have j0 := eq44919 X0 X1 X2
       grind)
    | exact resolve eq44919 eq28181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28181 eq44919
  have eq44921 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (k X2 (M.op X0 X1)) ∨ (M.op X0 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq44920 X0 X1 X2
       have i₂ := eq113 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq113 eq44920
    | (have j0 := eq44920 X0 X1 X2
       grind)
    | exact resolve eq44920 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq44920
  have eq46225 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq44921 (τ (M.op X0 X0)) (M.op (τ X0) (M.op (τ X0) X1)) x
       have i₂ := eq482 X0 X1
       grind)
    | exact superpose eq482 eq44921
    | (have j0 := eq44921 X1 X0 (k X1 X0)
       grind)
    | exact resolve eq44921 eq482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482 eq44921
  have eq47015 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq46225 (τ X1) X0
       grind)
    | exact superpose eq46225 eq19
    | (have j1 := eq46225 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq46225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq47016 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq46225 (σ X1) (σ X0)
       grind)
    | exact superpose eq46225 eq15
    | (have j1 := eq46225 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq46225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46225
  have eq51917 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq47015 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq47015
    | exact resolve eq47015 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47015
  have eq52015 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq51917 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq51917
    | (have j0 := eq51917 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq51917 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51917
  have eq54503 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq47016 x y
       grind)
    | exact superpose eq47016 eq16
    | (have j1 := eq47016 x y
       grind)
    | exact resolve eq16 eq47016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47016
  have eq55165 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq54503
       have i₂ := eq52015 y x
       grind)
    | exact superpose eq52015 eq54503
    | (have j1 := eq52015 (σ x) (σ y)
       grind)
    | (have r₁ := eq54503
       have r₂ := eq52015 y x
       grind)
    | (have r₁ := eq54503
       have r₂ := eq52015 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq54503
       have r₂ := eq52015 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq54503 eq52015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52015 eq54503
  have eq55166 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq55165
  have eq55865 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq55166
       grind)
    | exact superpose eq55166 eq10
    | exact resolve eq10 eq55166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55166
  have eq55927 : x = y ∨ x = y := by
    first
    | (have i₁ := eq55865
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq55865
    | exact resolve eq55865 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55865
  have eq55928 : x = y := by grind
  clear eq55927
  have eq59425 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq55928
       grind)
    | exact superpose eq55928 eq16
    | exact resolve eq16 eq55928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55928
  have eq59426 : False := by grind
  exact eq59426
