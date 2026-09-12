import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pyx_x_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
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
  have eq22 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
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
  have eq30 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k X0 (τ X1)) X2
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq15
    | exact resolve eq15 eq19
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
  have eq34 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  have eq35 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq58 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) (τ X1)) = X0 := by
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
  have eq77 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
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
  have eq82 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op X4 (M.op X2 (M.op X0 X3))) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq24 (M.op X1 (M.op X0 X2)) X1 X2 (M.op X0 X0)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq110 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57 (k (τ X0) X1) X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq57
    | exact resolve eq57 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57 (k X1 (τ X0)) X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq57
    | exact resolve eq57 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq25 (σ X0)
       have i₂ := eq57 X0 X0
       grind)
    | exact superpose eq57 eq25
    | (have j1 := eq57 X0 X0
       grind)
    | exact resolve eq25 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op X1 (M.op (σ X0) X2)) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X1 X2
       have i₂ := eq57 X0 X0
       grind)
    | exact superpose eq57 eq9
    | (have j1 := eq57 X0 X0
       grind)
    | exact resolve eq9 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq126 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (M.op X1 (M.op (σ X0) X2)) (σ (k X0 X0))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq122 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq128 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq120 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq217 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq34 X0
       have i₂ := eq25 (τ X0)
       grind)
    | exact superpose eq25 eq34
    | exact resolve eq34 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq218 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq217 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq217
    | exact resolve eq217 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq232 : ∀ X0 : G, (σ (τ X0)) = (k (σ (σ (M.op (τ (τ X0)) (τ (τ X0))))) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (σ (M.op (τ (τ X0)) (τ (τ X0))))
       have i₂ := eq218 (τ X0)
       grind)
    | exact superpose eq218 eq19
    | exact resolve eq19 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq235 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) X0) := by
    intro X0
    first
    | (have i₁ := eq23 (σ (M.op (τ (σ X0)) (τ (σ X0)))) X0
       have i₂ := eq218 (σ X0)
       grind)
    | exact superpose eq218 eq23
    | exact resolve eq23 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq237 : ∀ X0 : G, (τ (σ X0)) = (k (M.op (τ (σ X0)) (τ (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq235 X0
       have i₂ := eq10 (M.op (τ (σ X0)) (τ (σ X0)))
       grind)
    | exact superpose eq10 eq235
    | exact resolve eq235 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235
  have eq240 : ∀ X0 : G, (k (σ (σ (M.op (τ (τ X0)) (τ (τ X0))))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq232 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq232
    | exact resolve eq232 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq253 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq237 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq237
    | exact resolve eq237 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237
  have eq293 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq25 (M.op X0 X0)
       have i₂ := eq77 X0 X0
       grind)
    | exact superpose eq77 eq25
    | exact resolve eq25 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq307 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq23 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq253 (σ X0)
       grind)
    | exact superpose eq253 eq23
    | exact resolve eq23 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253
  have eq309 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq307 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq307
    | exact resolve eq307 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307
  have eq366 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq58 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq367 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq366 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366
  have eq371 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq367 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq367
    | (have j0 := eq367 X0
       grind)
    | exact resolve eq367 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367
  have eq405 : ∀ X0 : G, (σ (τ X0)) = (k (σ (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0))))))) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0))))))
       have i₂ := eq240 (τ X0)
       grind)
    | exact superpose eq240 eq19
    | exact resolve eq19 eq240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq406 : ∀ X0 : G, (k (σ (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0))))))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq405 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq405
    | exact resolve eq405 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405
  have eq643 : ∀ X0 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (k (σ (τ X0)) X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq128 (τ X0)
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq128
    | (have j0 := eq128 (τ X0)
       grind)
    | exact resolve eq128 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq128
  have eq657 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq643 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq643
    | (have j0 := eq643 X0
       grind)
    | exact resolve eq643 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643
  have eq661 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq657 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq657
    | (have j0 := eq657 X0
       grind)
    | exact resolve eq657 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657
  have eq699 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) ≠ (k X0 (σ X1)) ∨ (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) ∨ (k X0 (σ X1)) = (k (k X0 (σ X1)) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (k X0 (σ X1)) (σ X2)
       have i₂ := eq110 X0 X1 X2
       grind)
    | exact superpose eq110 eq13
    | (have j0 := eq13 (k X0 (σ X1)) (σ X2)
       have j1 := eq110 X0 X1 X2
       grind)
    | (have r₁ := eq13 (k X0 (σ X1)) (σ X2)
       have r₂ := eq110 X0 X1 X2
       grind)
    | exact resolve eq13 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq706 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) ≠ (k X0 (σ X1)) ∨ (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) ∨ (k X0 (σ X1)) = (k (k X0 (σ X1)) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq699 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699
  have eq707 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) ∨ (k X0 (σ X1)) = (k (k X0 (σ X1)) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq706 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706
  have eq709 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (σ (k (k (τ X0) X1) X2)) ∨ (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq707 X0 X1 X2
       have i₂ := eq22 X0 X1 X2
       grind)
    | exact superpose eq22 eq707
    | (have j0 := eq707 X0 X1 X2
       grind)
    | exact resolve eq707 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq707
  have eq750 : ∀ X0 X1 X2 : G, (k (σ X0) X1) ≠ (k (σ X0) X1) ∨ (k (σ X0) X1) = (M.op (σ X2) (σ X2)) ∨ (k (σ X0) X1) = (k (k (σ X0) X1) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (k (σ X0) X1) (σ X2)
       have i₂ := eq111 X0 X1 X2
       grind)
    | exact superpose eq111 eq13
    | (have j0 := eq13 (k (σ X0) X1) (σ X2)
       have j1 := eq111 X0 X1 X2
       grind)
    | (have r₁ := eq13 (k (σ X0) X1) (σ X2)
       have r₂ := eq111 X0 X1 X2
       grind)
    | exact resolve eq13 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq757 : ∀ X0 X1 X2 : G, (k (σ X0) X1) ≠ (k (σ X0) X1) ∨ (k (σ X0) X1) = (M.op (σ X2) (σ X2)) ∨ (k (σ X0) X1) = (k (k (σ X0) X1) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq750 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750
  have eq758 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (M.op (σ X2) (σ X2)) ∨ (k (σ X0) X1) = (k (k (σ X0) X1) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq757 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757
  have eq760 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (σ (k (k X0 (τ X1)) X2)) ∨ (k (σ X0) X1) = (M.op (σ X2) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq758 X0 X1 X2
       have i₂ := eq30 X0 X1 X2
       grind)
    | exact superpose eq30 eq758
    | (have j0 := eq758 X0 X1 X2
       grind)
    | exact resolve eq758 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq758
  have eq887 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X0 X1) (M.op (M.op X2 X0) (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq82 X0 X2 (M.op X0 X1) X1 (M.op x (M.op (M.op X0 X1) x))
       have i₂ := eq9 (M.op X0 X1) x x
       grind)
    | exact superpose eq9 eq82
    | exact resolve eq82 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq907 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 (M.op X0 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq82 X0 X0 X2 X3 X1
       have i₂ := eq77 X0 X0
       grind)
    | exact superpose eq77 eq82
    | exact resolve eq82 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq996 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (M.op (M.op X1 (M.op X0 X2)) (σ (k (τ X0) (τ X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq126 (τ X0) X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq126
    | exact resolve eq126 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq1024 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (k X0 (σ (τ X0)))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq996 X0 X1 X2
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq996
    | (have j0 := eq996 X0 X1 X2
       grind)
    | exact resolve eq996 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq996
  have eq1026 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1024 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1024
    | (have j0 := eq1024 X0 X1 X2
       grind)
    | exact resolve eq1024 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1024
  have eq2131 : ∀ X0 : G, (k (σ (τ X0)) X0) = X0 ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq218 X0
       have i₂ := eq371 X0
       grind)
    | exact superpose eq371 eq218
    | (have j1 := eq371 X0
       grind)
    | exact resolve eq218 eq371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq2134 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    grind
  clear eq371
  have eq2153 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq2134 X0
       have i₂ := eq35 X0 X0
       grind)
    | exact superpose eq35 eq2134
    | (have j0 := eq2134 X0
       grind)
    | exact resolve eq2134 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq2134
  have eq2155 : ∀ X0 : G, (k X0 X0) = X0 ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq2131 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2131
    | (have j0 := eq2131 X0
       grind)
    | exact resolve eq2131 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2131
  have eq2574 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ X0))) ∨ (σ (M.op (τ (σ X0)) (τ (σ X0)))) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 (σ X0)
       have i₂ := eq2155 (σ X0)
       grind)
    | exact superpose eq2155 eq31
    | (have j1 := eq2155 (σ X0)
       grind)
    | exact resolve eq31 eq2155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq2155
  have eq2597 : ∀ X0 : G, (k X0 X0) = X0 ∨ (σ (M.op (τ (σ X0)) (τ (σ X0)))) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq2574 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2574
    | (have j0 := eq2574 X0
       grind)
    | exact resolve eq2574 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2574
  have eq2618 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2597 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq2597
    | (have j0 := eq2597 X0
       grind)
    | exact resolve eq2597 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2597
  have eq2634 : ∀ X0 : G, (k X0 X0) = X0 ∨ (σ (k X0 X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2618 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2618
    | (have j0 := eq2618 X0
       grind)
    | exact resolve eq2618 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2618
  have eq5207 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq907 (k X0 X0) x X0 x
       have i₂ := eq1026 X0 x (M.op (k X0 X0) x)
       grind)
    | exact superpose eq1026 eq907
    | (have j1 := eq1026 X0 x x
       grind)
    | exact resolve eq907 eq1026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq907 eq1026
  have eq5261 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op X1 (k X0 X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq77 (k X0 X0) X1
       have i₂ := eq5207 X0
       grind)
    | exact superpose eq5207 eq77
    | (have j1 := eq5207 X0
       grind)
    | exact resolve eq77 eq5207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5207
  have eq7319 : ∀ X0 X1 : G, (M.op (M.op (k X0 X0) X1) (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq887 (k X0 X0) X1 X0
       have i₂ := eq661 X0
       grind)
    | exact superpose eq661 eq887
    | (have j1 := eq661 X0
       grind)
    | exact resolve eq887 eq661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661 eq887
  have eq12693 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) ≠ (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq709 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709
  have eq12694 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq12693 X0 X1 X2
       have j1 := eq110 X0 X1 X2
       grind)
    | (have r₁ := eq12693 X0 X1 X2
       have r₂ := eq110 X0 X1 X2
       grind)
    | exact resolve eq12693 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq12693
  have eq13100 : ∀ X0 X1 X2 : G, (k (σ X0) X1) ≠ (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (M.op (σ X2) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq760 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq760
  have eq13101 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (M.op (σ X2) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq13100 X0 X1 X2
       have j1 := eq111 X0 X1 X2
       grind)
    | (have r₁ := eq13100 X0 X1 X2
       have r₂ := eq111 X0 X1 X2
       grind)
    | exact resolve eq13100 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq13100
  have eq25742 : ∀ X0 : G, (k (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq7319 X0 (k (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq5261 (M.op X0 X0) (k X0 X0)
       grind)
    | exact superpose eq5261 eq7319
    | (have j0 := eq7319 X0 x
       have j1 := eq5261 X0 x
       grind)
    | exact resolve eq7319 eq5261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5261 eq7319
  have eq25849 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq25742 X0
       have i₂ := eq77 X0 X0
       grind)
    | exact superpose eq77 eq25742
    | (have j0 := eq25742 X0
       grind)
    | exact resolve eq25742 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25742
  have eq25850 : ∀ X0 : G, (k (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq25849 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25849
  have eq26265 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (σ (k (M.op X0 X0) (M.op X0 X0))) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq25850 X0
       have i₂ := eq2634 (M.op X0 X0)
       grind)
    | exact superpose eq2634 eq25850
    | (have j0 := eq25850 X0
       have j1 := eq2634 (M.op X0 X0)
       grind)
    | exact resolve eq25850 eq2634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2634 eq25850
  have eq26358 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ (k (M.op X0 X0) (M.op X0 X0))) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq26265 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26265
  have eq26371 : ∀ X0 : G, (σ X0) = (σ (k (M.op X0 X0) (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq26358 X0
       have i₂ := eq77 X0 X0
       grind)
    | exact superpose eq77 eq26358
    | (have j0 := eq26358 X0
       grind)
    | exact resolve eq26358 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26358
  have eq121296 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) ∨ (σ (M.op X0 X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq2153 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2153
    | exact resolve eq2153 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2153
  have eq121594 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) ∨ (σ (M.op X0 X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq121296 X0
       have i₂ := eq23 (σ X0) X0
       grind)
    | exact superpose eq23 eq121296
    | (have j0 := eq121296 X0
       grind)
    | exact resolve eq121296 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq121296
  have eq121628 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (σ (M.op X0 X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq121594 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq121594
    | (have j0 := eq121594 X0
       grind)
    | exact resolve eq121594 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121594
  have eq121654 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (σ (k X0 X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq121628 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq121628
    | (have j0 := eq121628 X0
       grind)
    | exact resolve eq121628 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121628
  have eq121945 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq121654 (τ X0)
       grind)
    | exact superpose eq121654 eq18
    | (have j1 := eq121654 (τ X0)
       grind)
    | exact resolve eq18 eq121654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121654
  have eq122056 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq121945 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq121945
    | (have j0 := eq121945 X0
       grind)
    | exact resolve eq121945 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121945
  have eq122195 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq122056 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq122056
    | (have j0 := eq122056 X0
       grind)
    | exact resolve eq122056 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122056
  have eq122311 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq122195 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq122195
    | (have j0 := eq122195 X0
       grind)
    | exact resolve eq122195 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122195
  have eq122312 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq122311 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122311
  have eq122461 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq122312 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq122312
    | exact resolve eq122312 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122807 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq122461 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq122461
    | exact resolve eq122461 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122461
  have eq125589 : ∀ X0 : G, (k X0 X0) = (τ (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq122807 X0
       grind)
    | exact superpose eq122807 eq10
    | exact resolve eq10 eq122807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125832 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq125589 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq125589
    | exact resolve eq125589 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125589
  have eq126965 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq125832 (σ X0)
       grind)
    | exact superpose eq125832 eq15
    | exact resolve eq15 eq125832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127120 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq126965 X0
       have i₂ := eq122807 X0
       grind)
    | exact superpose eq122807 eq126965
    | exact resolve eq126965 eq122807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126965
  have eq131679 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq293 (σ X0)
       have i₂ := eq127120 X0
       grind)
    | exact superpose eq127120 eq293
    | exact resolve eq293 eq127120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq224383 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12694 X0 X1 X2
       have i₂ := eq127120 X2
       grind)
    | exact superpose eq127120 eq12694
    | (have j0 := eq12694 X0 X1 X2
       grind)
    | exact resolve eq12694 eq127120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12694
  have eq224419 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (k (M.op (σ X0) (σ X0)) (σ X0)) (σ X1)) ∨ (k (M.op (σ X0) (σ X0)) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq224383 (M.op (σ X0) (σ X0)) X0 X1
       have i₂ := eq309 X0
       grind)
    | exact superpose eq309 eq224383
    | (have j0 := eq224383 (M.op (σ X0) (σ X0)) X0 X1
       grind)
    | exact resolve eq224383 eq309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309 eq224383
  have eq225234 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (M.op (σ X0) (M.op (σ X0) (σ X0))) (σ X1)) ∨ (k (M.op (σ X0) (σ X0)) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    grind
  clear eq224419
  have eq225512 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k (M.op (σ X0) (σ X0)) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq225234 X0 X1
       have i₂ := eq25 (σ X0)
       grind)
    | exact superpose eq25 eq225234
    | (have j0 := eq225234 X0 X1
       grind)
    | exact resolve eq225234 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225234
  have eq225718 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ X0) (σ X0))) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  clear eq225512
  have eq225827 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq225718 X0 X1
       have i₂ := eq25 (σ X0)
       grind)
    | exact superpose eq25 eq225718
    | (have j0 := eq225718 X0 X1
       grind)
    | exact resolve eq225718 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq225718
  have eq226056 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13101 X0 X1 X2
       have i₂ := eq127120 X2
       grind)
    | exact superpose eq127120 eq13101
    | (have j0 := eq13101 X0 X1 X2
       grind)
    | exact resolve eq13101 eq127120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13101
  have eq226134 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (k (σ (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0))))))) X0) (σ X1)) ∨ (k (σ (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0))))))) X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq226056 (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0)))))) X0 X1
       have i₂ := eq240 (τ X0)
       grind)
    | exact superpose eq240 eq226056
    | (have j0 := eq226056 (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0)))))) X0 X1
       grind)
    | exact resolve eq226056 eq240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240 eq226056
  have eq226920 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (k (σ (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0))))))) X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq226134 X0 X1
       have i₂ := eq406 X0
       grind)
    | exact superpose eq406 eq226134
    | (have j0 := eq226134 X0 X1
       grind)
    | exact resolve eq226134 eq406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226134
  have eq227221 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k (σ (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0))))))) X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq226920 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq226920
    | (have j0 := eq226920 X0 X1
       grind)
    | exact resolve eq226920 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq226920
  have eq227448 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq227221 X0 X1
       have i₂ := eq406 X0
       grind)
    | exact superpose eq406 eq227221
    | (have j0 := eq227221 X0 X1
       grind)
    | exact resolve eq227221 eq406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406 eq227221
  have eq230776 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (σ (M.op (τ X0) (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq227448 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq227448
    | (have j0 := eq227448 X1 (τ X0)
       grind)
    | exact resolve eq227448 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227448
  have eq231545 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq230776 X0 X1
       have i₂ := eq122312 X0
       grind)
    | exact superpose eq122312 eq230776
    | (have j0 := eq230776 X0 X1
       grind)
    | exact resolve eq230776 eq122312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122312 eq230776
  have eq231764 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq231545 X0 X1
       have i₂ := eq125832 X0
       grind)
    | exact superpose eq125832 eq231545
    | (have j0 := eq231545 X0 X1
       grind)
    | exact resolve eq231545 eq125832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125832 eq231545
  have eq436283 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq225827 x y
       grind)
    | exact superpose eq225827 eq16
    | (have j1 := eq225827 x y
       grind)
    | exact resolve eq16 eq225827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225827
  have eq439018 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq436283
       have i₂ := eq231764 y x
       grind)
    | exact superpose eq231764 eq436283
    | (have j1 := eq231764 y x
       grind)
    | exact resolve eq436283 eq231764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231764 eq436283
  have eq439040 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq439018
  have eq439191 : y = (M.op x x) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq77 y y
       have i₂ := eq439040
       grind)
    | exact superpose eq439040 eq77
    | exact resolve eq77 eq439040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq439040
  have eq444309 : (σ x) = (σ (k y y)) ∨ x = y ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq26371 x
       have i₂ := eq439191
       grind)
    | exact superpose eq439191 eq26371
    | exact resolve eq26371 eq439191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26371 eq439191
  have eq444580 : (σ x) = (σ (M.op y y)) ∨ x = y ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq444309
       have i₂ := eq122807 y
       grind)
    | exact superpose eq122807 eq444309
    | exact resolve eq444309 eq122807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122807 eq444309
  have eq444581 : x = y ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq444580
  have eq444620 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq444581
       grind)
    | exact superpose eq444581 eq16
    | exact resolve eq16 eq444581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444581
  have eq444646 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq444620
       have r₂ := eq127120 x
       grind)
    | exact resolve eq444620 eq127120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127120 eq444620
  have eq446026 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq131679 y
       have i₂ := eq444646
       grind)
    | exact superpose eq444646 eq131679
    | exact resolve eq131679 eq444646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131679
  have eq446045 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq444646
       grind)
    | exact superpose eq444646 eq10
    | exact resolve eq10 eq444646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444646
  have eq446542 : x = (M.op y y) := by
    first
    | (have i₁ := eq446045
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq446045
    | exact resolve eq446045 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446045
  have eq446826 : x = (M.op x y) := by
    first
    | (have i₁ := eq293 y
       have i₂ := eq446542
       grind)
    | exact superpose eq446542 eq293
    | exact resolve eq293 eq446542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293 eq446542
  have eq464613 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq446026
       grind)
    | exact superpose eq446026 eq16
    | exact resolve eq16 eq446026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446026
  have eq464889 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq464613
       have i₂ := eq446826
       grind)
    | exact superpose eq446826 eq464613
    | exact resolve eq464613 eq446826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446826 eq464613
  have eq464890 : False := by grind
  exact eq464890

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_x_pyx_pxx_pyx_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  have eq51 : ∀ X0 : G, x = (M.op (M.op X0 (M.op x y)) (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (σ x))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 X0)
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X1 : G, (k (M.op X1 X1) X1) = X1 := by
    intro X1
    grind
  have eq68 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq85 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq86 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq87 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq90 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq85
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq85
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq85 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq85
       grind)
    | exact superpose eq85 eq16
    | exact resolve eq16 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq96
    | exact resolve eq96 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq101 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq86
       grind)
    | exact superpose eq86 eq16
    | exact resolve eq16 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq114 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq87 eq16
    | exact resolve eq16 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq166 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ x)) := by
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
  have eq212 : ∀ X0 X1 : G, (M.op X1 (M.op x y)) = (M.op (M.op X0 x) (M.op (M.op X1 (M.op x y)) (M.op X1 (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq245 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq27 eq56
    | (have j0 := eq56 (σ y) (σ x)
       grind)
    | exact resolve eq56 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq248 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq65 (M.op X0 X0)
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq65
    | exact resolve eq65 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq270 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq405 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) X2)) = (M.op X0 (M.op (M.op X1 (M.op (M.op X0 X0) X2)) (M.op X1 (M.op (M.op X0 X0) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 (M.op X0 X0) X0 X1 X2
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq413 : ∀ X0 X1 : G, (M.op X0 (M.op y X1)) = (M.op (M.op x y) (M.op (M.op X0 (M.op y X1)) (M.op X0 (M.op y X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq53 y x X0 X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq53
    | (have j0 := eq53 y x X0 X1
       grind)
    | exact resolve eq53 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq415 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) X1)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (M.op (σ y) X1)) (M.op X0 (M.op (σ y) X1)))) := by
    intro X0 X1
    first
    | exact superpose eq27 eq53
    | (have j0 := eq53 (σ y) (σ x) X0 X1
       grind)
    | exact resolve eq53 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq417 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 X1 X2 (M.op X0 X0)
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq419 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X0 (M.op X1 X2))) = (M.op (M.op X5 (M.op X4 X1)) (M.op (M.op X3 (M.op X0 (M.op X1 X2))) (M.op X3 (M.op X0 (M.op X1 X2))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq53 (M.op X1 X0) X1 X2 (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))
       have i₂ := eq53 X0 X1 X2 X3
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq420 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op X4 (M.op X2 (M.op X0 X3))) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 (M.op X1 (M.op X0 X2)) X1 X2 (M.op X0 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq422 : ∀ X0 X1 X2 : G, (M.op X0 x) = (M.op (M.op X2 (M.op X1 (M.op x y))) (M.op (M.op X0 x) (M.op X0 x))) := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq423 : ∀ X0 X1 X2 : G, (M.op X0 (σ x)) = (M.op (M.op X2 (M.op X1 (M.op (σ x) (σ y)))) (M.op (M.op X0 (σ x)) (M.op X0 (σ x)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq442 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) ≠ (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))) ∨ (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))) = (M.op (M.op X3 X1) (M.op X3 X1)) ∨ (M.op (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))) (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))) = (k (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))) (M.op X3 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))) (M.op X3 X1)
       have i₂ := eq53 X1 X3 X0 X2
       grind)
    | exact superpose eq53 eq12
    | (have j0 := eq12 (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))
       grind)
    | exact resolve eq12 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq444 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) ≠ (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))) ∨ (M.op X0 (M.op X1 X2)) = (k (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))) (M.op X3 X1)) ∨ (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))) = (M.op (M.op X3 X1) (M.op X3 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq442 X0 X1 X2 X3
       have i₂ := eq56 (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))
       grind)
    | exact superpose eq56 eq442
    | (have j0 := eq442 X0 X1 X2 X3
       grind)
    | exact resolve eq442 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442
  have eq463 : ∀ X0 : G, (k (τ X0) (k y x)) = (τ (k X0 (k (σ y) (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq270 X0 (k y x)
       have i₂ := eq85
       grind)
    | exact superpose eq85 eq270
    | exact resolve eq270 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq469 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq270 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq270
    | (have j0 := eq270 X0 x
       grind)
    | exact resolve eq270 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq554 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq68 X0 X1
       grind)
    | exact superpose eq68 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq68 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq68 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq68 X0 X0
       grind)
    | exact resolve eq12 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq559 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq554 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554
  have eq566 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq559 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq559 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq559 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq559 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559
  have eq575 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq566 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq566
    | (have j0 := eq566 X0 X1
       grind)
    | exact resolve eq566 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566
  have eq3311 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq417 X0 X0 X1
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq417
    | exact resolve eq417 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417
  have eq3339 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq27 eq3311
    | (have j0 := eq3311 (σ y) (σ x)
       grind)
    | exact resolve eq3311 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3486 : ∀ X0 X1 : G, (M.op x x) = (M.op (M.op X0 (M.op X1 (M.op x y))) x) := by
    intro X0 X1
    first
    | (have i₁ := eq422 x X1 X0
       have i₂ := eq56 x x
       grind)
    | exact superpose eq56 eq422
    | exact resolve eq422 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422
  have eq3517 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (M.op (M.op X0 (M.op X1 (M.op (σ x) (σ y)))) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq423 sF2 X1 x
       have i₂ := eq56 sF2 sF2
       grind)
    | exact superpose eq56 eq423
    | exact resolve eq423 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423
  have eq3534 : (M.op x x) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq3486 sF0 sF0
       have i₂ := eq54 sF0
       grind)
    | exact superpose eq54 eq3486
    | exact resolve eq3486 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3486
  have eq3777 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq3517 sF4 sF4
       have i₂ := eq54 sF4
       grind)
    | exact superpose eq54 eq3517
    | exact resolve eq3517 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3517
  have eq3799 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ x))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq3777 eq14
    | exact resolve eq14 eq3777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3816 : ∀ X0 : G, (M.op (M.op y X0) (M.op y X0)) = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq413 (M.op y X0) X0
       have i₂ := eq56 (M.op y X0) (M.op y X0)
       grind)
    | exact superpose eq56 eq413
    | exact resolve eq413 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413
  have eq3837 : ∀ X0 : G, (M.op (M.op (σ y) X0) (M.op (σ y) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq415 (M.op sF3 x) x
       have i₂ := eq56 (M.op sF3 x) (M.op sF3 x)
       grind)
    | exact superpose eq56 eq415
    | exact resolve eq415 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415
  have eq3950 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X0 X1) (M.op (M.op X2 X0) (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq420 X0 X2 (M.op X0 X1) X1 (M.op X0 X1)
       have i₂ := eq54 (M.op X0 X1)
       grind)
    | exact superpose eq54 eq420
    | exact resolve eq420 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4003 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 (M.op X0 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq420 X0 X0 X2 X3 X1
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq420
    | exact resolve eq420 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420
  have eq4203 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq3799 sF2
       have i₂ := eq54 sF2
       grind)
    | exact superpose eq54 eq3799
    | exact resolve eq3799 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3799
  have eq4693 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq166 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166
  have eq6659 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq405 X0 X1 (M.op X0 X0)
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq405
    | exact resolve eq405 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6702 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) = (M.op X0 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq405 X0 (M.op (M.op X0 X0) X1) X1
       have i₂ := eq56 (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq56 eq405
    | exact resolve eq405 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405
  have eq7108 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq575 (M.op x x) x
       have i₂ := eq65 x
       grind)
    | exact superpose eq65 eq575
    | (have j0 := eq575 X0 (M.op X0 X0)
       grind)
    | exact resolve eq575 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575
  have eq7836 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X2 (M.op X3 X0)) (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    by_contra hcon
    push Not at hcon
    have f7836_12 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X0 (M.op X1 X2))) = (M.op (M.op X5 (M.op X4 X1)) (M.op (M.op X3 (M.op X0 (M.op X1 X2))) (M.op X3 (M.op X0 (M.op X1 X2))))) := by
      intro X0 X1 X2 X3 X4 X5
      grind
    have f7836_13 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
      intro X0
      grind
    have f7836_19 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
      intro X0 X1 X2
      grind
    have f7836_22 : (M.op X0 X1) ≠ (M.op (M.op X2 (M.op X3 X0)) (M.op (M.op X0 X1) (M.op X0 X1))) := by grind
    have f7836_26 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
      intro X0 X1
      first
      | (have i₁ := f7836_19 X0 X1 (M.op X0 X0)
         have i₂ := f7836_13 X0
         grind)
      | exact superpose f7836_13 f7836_19
      | exact resolve f7836_19 f7836_13
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f7836_27 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
      intro X0 X1 X2 X3
      first
      | (have i₁ := f7836_19 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
         have i₂ := f7836_19 X0 X2 X3
         grind)
      | exact superpose f7836_19 f7836_19
      | exact resolve f7836_19 f7836_19
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f7836_35 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X0 X0) X2)) X0) := by
      intro X0 X1 X2
      first
      | (have i₁ := f7836_19 (M.op X0 X0) X1 X2
         have i₂ := f7836_26 X0 X0
         grind)
      | exact superpose f7836_26 f7836_19
      | exact resolve f7836_19 f7836_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f7836_91 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op X3 (M.op X4 X0)) (M.op (M.op X1 (M.op X2 X0)) (M.op X1 (M.op X2 X0)))) := by
      intro X0 X1 X2 X3 X4
      first
      | (have i₁ := f7836_12 X0 X0 (M.op X0 X0) X3 X4 x
         have i₂ := f7836_13 X0
         grind)
      | exact superpose f7836_13 f7836_12
      | exact resolve f7836_12 f7836_13
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f7836_109 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))) = (M.op (M.op X3 (M.op X4 X1)) (M.op X0 (M.op X1 X2))) := by
      intro X0 X1 X2 X3 X4
      first
      | (have i₁ := f7836_12 X0 X1 X2 (M.op X0 (M.op X1 X2)) X4 X3
         have i₂ := f7836_26 (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))
         grind)
      | exact superpose f7836_26 f7836_12
      | exact resolve f7836_12 f7836_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f7836_411 : ∀ X0 X2 X3 : G, (M.op (M.op X2 (M.op X3 X0)) (M.op X0 X0)) = X0 := by
      intro X0 X2 X3
      first
      | (have i₁ := f7836_91 X0 (M.op x X0) X0 X3 x
         have i₂ := f7836_26 X0 x
         grind)
      | exact superpose f7836_26 f7836_91
      | exact resolve f7836_91 f7836_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f7836_718 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op X3 (M.op X0 (M.op X1 X2))) X1) := by
      intro X0 X1 X2 X3
      first
      | (have i₁ := f7836_35 X1 X3 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))
         have i₂ := f7836_27 X1 X1 X0 X2
         grind)
      | exact superpose f7836_27 f7836_35
      | exact resolve f7836_35 f7836_27
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f7836_1261 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
      intro X0 X1
      first
      | (have i₁ := f7836_718 (M.op X0 X1) X0 X1 (M.op x (M.op x (M.op X0 X1)))
         have i₂ := f7836_411 (M.op X0 X1) x x
         grind)
      | exact superpose f7836_411 f7836_718
      | exact resolve f7836_718 f7836_411
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f7836_1525 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X0 (M.op X1 X0)) := by
      intro X0 X1
      first
      | (have i₁ := f7836_1261 (M.op X1 X0) (M.op X0 X0)
         have i₂ := f7836_26 X0 X1
         grind)
      | exact superpose f7836_26 f7836_1261
      | exact resolve f7836_1261 f7836_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f7836_2980 : (M.op X0 X1) ≠ (M.op (M.op X2 (M.op X3 X0)) (M.op X1 (M.op X0 X1))) := by
      first
      | (have i₁ := f7836_22
         have i₂ := f7836_1525 X1 X0
         grind)
      | exact superpose f7836_1525 f7836_22
      | exact resolve f7836_22 f7836_1525
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f7836_3032 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 (M.op X1 X0)) (M.op X0 (M.op X1 X0))) := by
      intro X0 X1 X2
      first
      | (have i₁ := f7836_26 (M.op X1 X0) X2
         have i₂ := f7836_1525 X0 X1
         grind)
      | exact superpose f7836_1525 f7836_26
      | exact resolve f7836_26 f7836_1525
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f7836_3082 : (M.op X0 X1) ≠ (M.op (M.op X1 (M.op X0 X1)) (M.op X1 (M.op X0 X1))) := by
      first
      | (have i₁ := f7836_2980
         have i₂ := f7836_109 X1 X0 X1 X2 X3
         grind)
      | exact superpose f7836_109 f7836_2980
      | exact resolve f7836_2980 f7836_109
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f7836_3098 : False := by
      first
      | (have r₁ := f7836_3082
         have r₂ := f7836_3032 X1 X0 X1
         grind)
      | exact resolve f7836_3082 f7836_3032
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f7836_3098
  clear eq419
  have eq11247 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op x y))) ≠ (M.op (M.op X1 (M.op X0 (M.op x y))) (M.op X1 (M.op X0 (M.op x y)))) ∨ (M.op X1 (M.op X0 (M.op x y))) = (k (M.op (M.op X1 (M.op X0 (M.op x y))) (M.op X1 (M.op X0 (M.op x y)))) (M.op X3 (M.op X2 x))) ∨ (M.op (M.op X1 (M.op X0 (M.op x y))) (M.op X1 (M.op X0 (M.op x y)))) = (M.op (M.op X3 (M.op X2 x)) (M.op X3 (M.op X2 x))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq212 eq444
    | (have j0 := eq444 X1 X0 (M.op x y) X3
       grind)
    | exact resolve eq444 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212 eq444
  have eq12336 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq98 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12337 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq12336
    | exact resolve eq12336 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12336
  have eq12348 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq12337
       have r₂ := eq28
       grind)
    | exact resolve eq12337 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12337
  have eq12350 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq12348
    | exact resolve eq12348 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12348
  have eq12359 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq12350 eq54
    | exact resolve eq54 eq12350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12361 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq12350 eq65
    | exact resolve eq65 eq12350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12350
  have eq12381 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq12359
    | exact resolve eq12359 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12359
  have eq12392 : x = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq65 x
       have i₂ := eq12381
       grind)
    | exact superpose eq12381 eq65
    | exact resolve eq65 eq12381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12381
  have eq12552 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq85
       have i₂ := eq12392
       grind)
    | exact superpose eq12392 eq85
    | exact resolve eq85 eq12392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12392
  have eq12574 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12552
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq12552
    | exact resolve eq12552 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12552
  have eq12873 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12574 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq12574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12574
  have eq12876 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq12873
    | exact resolve eq12873 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12873
  have eq12877 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq12876
  have eq12889 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq12877
    | exact resolve eq12877 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12877
  have eq12890 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq12889
  have eq13043 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12890 eq54
    | exact resolve eq54 eq12890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12890
  have eq13065 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq13043
    | exact resolve eq13043 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13043
  have eq13066 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq13065
  have eq13068 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ y)) (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13066 eq52
    | exact resolve eq52 eq13066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq13069 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13066 eq101
    | (have r₁ := eq101
       have r₂ := eq13066
       grind)
    | exact resolve eq101 eq13066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq13082 : (σ y) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13066 eq4203
    | exact resolve eq4203 eq13066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4203
  have eq13083 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  have eq13084 : (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq13069
  have eq13589 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq13068
    | (have j0 := eq13068 (σ x)
       grind)
    | exact resolve eq13068 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13068
  have eq13618 : (σ x) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13066 eq13589
    | exact resolve eq13589 eq13066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13589
  have eq13645 : (σ x) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq13618
  have eq13649 : (σ x) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq13645
       have r₂ := eq13083
       grind)
    | exact resolve eq13645 eq13083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13645
  have eq14130 : (τ (σ x)) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq12361 eq95
    | exact resolve eq95 eq12361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14131 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq12361 eq98
    | exact resolve eq98 eq12361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12361
  have eq14144 : y = (M.op x x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq14131
  have eq14152 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (k y x) := by
    first
    | exact superpose eq29 eq14130
    | exact resolve eq14130 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14130
  have eq14158 : ∀ X0 : G, x = (M.op (M.op X0 (M.op x y)) y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq51 X0
       have i₂ := eq14144
       grind)
    | exact superpose eq14144 eq51
    | exact resolve eq51 eq14144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14144
  have eq14567 : x = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq65 x
       have i₂ := eq14152
       grind)
    | exact superpose eq14152 eq65
    | exact resolve eq65 eq14152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14152
  have eq14586 : x = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq14567
  have eq14591 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq85
       have i₂ := eq14586
       grind)
    | exact superpose eq14586 eq85
    | exact resolve eq85 eq14586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq14603 : x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq14586
       grind)
    | exact superpose eq14586 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq14586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14604 : x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14603
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14603
    | exact resolve eq14603 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14603
  have eq14614 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14591
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq14591
    | exact resolve eq14591 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14591
  have eq14616 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14604
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14604
    | exact resolve eq14604 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14604
  have eq14617 : y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq14616
  have eq14822 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq54 x
       have i₂ := eq14617
       grind)
    | exact superpose eq14617 eq54
    | exact resolve eq54 eq14617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14617
  have eq14845 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14822
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14822
    | exact resolve eq14822 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14822
  have eq14846 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq14845
  have eq15748 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (k (σ y) (σ x)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq463 X0
       have i₂ := eq14586
       grind)
    | exact superpose eq14586 eq463
    | exact resolve eq463 eq14586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463 eq14586
  have eq15784 : ∀ X0 : G, (τ (k X0 (k (σ y) (σ x)))) = (τ (k X0 (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq15748 X0
       have i₂ := eq469 X0
       grind)
    | exact superpose eq469 eq15748
    | exact resolve eq15748 eq469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469 eq15748
  have eq17323 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14158 eq3311
    | exact resolve eq3311 eq14158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14158
  have eq17324 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17323
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq17323
    | exact resolve eq17323 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17323
  have eq17340 : (M.op x y) = (k y (M.op x y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq248 y
       have i₂ := eq17324
       grind)
    | exact superpose eq17324 eq248
    | exact resolve eq248 eq17324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17324
  have eq17736 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17340 eq87
    | exact resolve eq87 eq17340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17340
  have eq17760 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq17736
    | exact resolve eq17736 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17736
  have eq20602 : ∀ X0 : G, (k X0 (k (σ y) (σ x))) = (σ (τ (k X0 (σ x)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq15784 eq15
    | exact resolve eq15 eq15784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15784
  have eq20692 : ∀ X0 : G, (k X0 (σ x)) = (k X0 (k (σ y) (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq20602 X0
       have i₂ := eq15 (k X0 sF2)
       grind)
    | exact superpose eq15 eq20602
    | exact resolve eq20602 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20602
  have eq20720 : ∀ X0 : G, (k X0 (σ x)) = (k X0 (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq98 eq20692
    | exact resolve eq20692 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20692
  have eq20764 : ∀ X0 : G, (k X0 (σ x)) = (k X0 (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq20720 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20720
  have eq38202 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ y) (M.op (M.op (σ y) X0) (M.op (σ y) X0))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13082 eq7836
    | exact resolve eq7836 eq13082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7836 eq13082
  have eq38550 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3837 eq38202
    | exact resolve eq38202 eq3837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38202
  have eq40967 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op (σ y) X0) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq38550 eq4003
    | exact resolve eq4003 eq38550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4003 eq38550
  have eq41175 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13649 eq40967
    | exact resolve eq40967 eq13649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13649 eq40967
  have eq41319 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq41175
  have eq41328 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq41319
    | exact resolve eq41319 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41319
  have eq41624 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq41328 eq245
    | exact resolve eq245 eq41328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245
  have eq41678 : (σ y) = (k (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq41328 eq65
    | exact resolve eq65 eq41328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41328
  have eq41770 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13066 eq41624
    | exact resolve eq41624 eq13066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41624
  have eq41858 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq41770
  have eq41870 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq41858
       have r₂ := eq13083
       grind)
    | exact resolve eq41858 eq13083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41858
  have eq42271 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13066 eq41678
    | exact resolve eq41678 eq13066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13066 eq41678
  have eq42281 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq42271
  have eq42285 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq42281
       have r₂ := eq13083
       grind)
    | exact resolve eq42281 eq13083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13083 eq42281
  have eq43710 : (τ (σ y)) = (k y y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq42285 eq107
    | exact resolve eq107 eq42285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42285
  have eq43777 : y = (k y y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq43710
    | exact resolve eq43710 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43710
  have eq44100 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq43777
       grind)
    | exact superpose eq43777 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq43777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43777
  have eq44101 : y = (M.op y y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq44100
  have eq44481 : ∀ X0 : G, y = (M.op (M.op y X0) (M.op y y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq3950 y x y
       have i₂ := eq44101
       grind)
    | exact superpose eq44101 eq3950
    | exact resolve eq3950 eq44101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63856 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq44481 X0
       have i₂ := eq44101
       grind)
    | exact superpose eq44101 eq44481
    | exact resolve eq44481 eq44101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44101 eq44481
  have eq63938 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq63856 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63856
  have eq389209 : (k y x) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13084 eq95
    | exact resolve eq95 eq13084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq13084
  have eq399846 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20764 eq14614
    | exact resolve eq14614 eq20764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14614 eq20764
  have eq400201 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq399846
  have eq400525 : (τ (σ x)) = (k y (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq400201 eq114
    | exact resolve eq114 eq400201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq400201
  have eq400575 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (k y (M.op x y)) := by
    first
    | exact superpose eq29 eq400525
    | exact resolve eq400525 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq400525
  have eq401055 : ∀ X0 : G, x = (M.op (M.op X0 (M.op x y)) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (k y (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq51 X0
       have i₂ := eq400575
       grind)
    | exact superpose eq400575 eq51
    | exact resolve eq51 eq400575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq400575
  have eq514847 : (M.op x y) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (k y (M.op x y)) := by
    first
    | exact superpose eq401055 eq3311
    | exact resolve eq3311 eq401055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3311 eq401055
  have eq515013 : (M.op x y) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (k y (M.op x y)) := by
    first
    | (have i₁ := eq514847
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq514847
    | exact resolve eq514847 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514847
  have eq515156 : (M.op x y) = (k y (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (k y (M.op x y)) := by
    first
    | (have i₁ := eq248 y
       have i₂ := eq515013
       grind)
    | exact superpose eq515013 eq248
    | exact resolve eq248 eq515013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515013
  have eq516618 : x ≠ (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (k y (M.op x y)) := by grind
  clear eq515156
  have eq516623 : x = (k y (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq516618
       have r₂ := eq14846
       grind)
    | exact resolve eq516618 eq14846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14846 eq516618
  have eq517167 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq516623 eq87
    | exact resolve eq87 eq516623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq516623
  have eq517284 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq517167
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq517167
    | exact resolve eq517167 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517167
  have eq517423 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq517284 eq17760
    | exact resolve eq17760 eq517284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17760 eq517284
  have eq517441 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq517423
  have eq517475 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq517441 eq3777
    | exact resolve eq3777 eq517441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3777
  have eq518731 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq517475 eq3837
    | exact resolve eq3837 eq517475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3837 eq517475
  have eq519047 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq518731
       have i₂ := eq56 sF2 sF2
       grind)
    | exact superpose eq56 eq518731
    | exact resolve eq518731 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518731
  have eq519845 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ x)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq519047 eq14
    | exact resolve eq14 eq519047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519047
  have eq551982 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq519845 eq6702
    | exact resolve eq6702 eq519845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519845
  have eq552264 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq517441 eq551982
    | exact resolve eq551982 eq517441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551982
  have eq552698 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq552264
  have eq552719 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq27 eq552698
    | exact resolve eq552698 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552698
  have eq552928 : (σ y) = (k (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq552719 eq65
    | exact resolve eq65 eq552719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq552719
  have eq555225 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq517441 eq552928
    | exact resolve eq552928 eq517441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517441 eq552928
  have eq555259 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq555225
  have eq556166 : (τ (σ y)) = (k y y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq555259 eq107
    | exact resolve eq107 eq555259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq555259
  have eq556334 : y = (k y y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq30 eq556166
    | exact resolve eq556166 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556166
  have eq556446 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq556334
       grind)
    | exact superpose eq556334 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq556334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556334
  have eq556477 : y = (M.op y y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq556446
  have eq556847 : ∀ X0 : G, y = (M.op (M.op y X0) (M.op y y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq3950 y x y
       have i₂ := eq556477
       grind)
    | exact superpose eq556477 eq3950
    | exact resolve eq3950 eq556477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3950
  have eq636111 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq556847 X0
       have i₂ := eq556477
       grind)
    | exact superpose eq556477 eq556847
    | exact resolve eq556847 eq556477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556477 eq556847
  have eq636321 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq636111 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636111
  have eq1239629 : (τ (σ y)) = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq41870 eq389209
    | exact resolve eq389209 eq41870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41870 eq389209
  have eq1240153 : (τ (σ y)) = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1239629
  have eq1240173 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq1240153
    | exact resolve eq1240153 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1240153
  have eq1240393 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1240173 eq54
    | exact resolve eq54 eq1240173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1240173
  have eq1240681 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq1240393
    | exact resolve eq1240393 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1240393
  have eq1240682 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1240681
  have eq1240846 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq1240682
       grind)
    | exact superpose eq1240682 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq1240682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1240682
  have eq1240892 : y = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1240846
  have eq1241002 : y = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1240892
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1240892
    | exact resolve eq1240892 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1240892
  have eq1241003 : y = (M.op x x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1241002
  have eq1241323 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq56 x x
       have i₂ := eq1241003
       grind)
    | exact superpose eq1241003 eq56
    | exact resolve eq56 eq1241003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1241003
  have eq1253062 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq63938 y
       have i₂ := eq1241323
       grind)
    | exact superpose eq1241323 eq63938
    | exact resolve eq63938 eq1241323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63938 eq1241323
  have eq1253374 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1253062
  have eq1253461 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1253374
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1253374
    | exact resolve eq1253374 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1253374
  have eq1253462 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1253461
  have eq1253493 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1253462 eq28
    | exact resolve eq28 eq1253462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1253505 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1253462 eq3339
    | exact resolve eq3339 eq1253462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3339
  have eq1254374 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq1253505
    | exact resolve eq1253505 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1253505
  have eq1254678 : (M.op (σ x) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1254374 eq248
    | exact resolve eq248 eq1254374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248 eq1254374
  have eq1256429 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1253462 eq1254678
    | exact resolve eq1254678 eq1253462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1253462 eq1254678
  have eq1256482 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq1256429
  have eq1264915 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1256482 eq98
    | exact resolve eq98 eq1256482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq1256482
  have eq1265021 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq1264915
  have eq1265036 : y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1265021
       have r₂ := eq1253493
       grind)
    | exact resolve eq1265021 eq1253493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1265021
  have eq1283454 : x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq56 x x
       have i₂ := eq1265036
       grind)
    | exact superpose eq1265036 eq56
    | exact resolve eq56 eq1265036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1265036
  have eq1292316 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq636321 y
       have i₂ := eq1283454
       grind)
    | exact superpose eq1283454 eq636321
    | exact resolve eq636321 eq1283454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636321 eq1283454
  have eq1292562 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1292316
  have eq1292686 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1292562
       have r₂ := eq1253493
       grind)
    | exact resolve eq1292562 eq1253493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1253493 eq1292562
  have eq1292709 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1292686
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1292686
    | exact resolve eq1292686 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1292686
  have eq1292710 : y = (M.op x y) := by grind
  clear eq1292709
  have eq1295037 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq1292710 eq21
    | exact resolve eq21 eq1292710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq1295209 : (M.op x x) = (M.op y x) := by
    first
    | exact superpose eq1292710 eq3534
    | exact resolve eq3534 eq1292710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3534
  have eq1295452 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1295037
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1295037
    | exact resolve eq1295037 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1295037
  have eq1295457 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1295452 eq27
    | exact resolve eq27 eq1295452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1299355 : (M.op (M.op x x) (M.op x x)) = (M.op (M.op x y) (M.op x x)) := by
    first
    | (have i₁ := eq3816 x
       have i₂ := eq1295209
       grind)
    | exact superpose eq1295209 eq3816
    | exact resolve eq3816 eq1295209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3816 eq1295209
  have eq1299526 : (M.op (M.op x x) (M.op x x)) = (M.op y (M.op x x)) := by
    first
    | exact superpose eq1292710 eq1299355
    | exact resolve eq1299355 eq1292710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1299355
  have eq1299536 : x = (M.op y (M.op x x)) := by
    first
    | (have i₁ := eq1299526
       have i₂ := eq56 x x
       grind)
    | exact superpose eq56 eq1299526
    | exact resolve eq1299526 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1299526
  have eq1303260 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 (M.op x x)
       have i₂ := eq1299536
       grind)
    | exact superpose eq1299536 eq14
    | exact resolve eq14 eq1299536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1299536
  have eq1366810 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 y)) ≠ (M.op (M.op X1 (M.op X0 y)) (M.op X1 (M.op X0 y))) ∨ (M.op X1 (M.op X0 (M.op x y))) = (k (M.op (M.op X1 (M.op X0 (M.op x y))) (M.op X1 (M.op X0 (M.op x y)))) (M.op X3 (M.op X2 x))) ∨ (M.op (M.op X1 (M.op X0 (M.op x y))) (M.op X1 (M.op X0 (M.op x y)))) = (M.op (M.op X3 (M.op X2 x)) (M.op X3 (M.op X2 x))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq1292710 eq11247
    | (have j0 := eq11247 X0 X1 X2 X3
       grind)
    | exact resolve eq11247 eq1292710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11247
  have eq1366811 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 y)) = (k (M.op (M.op X1 (M.op X0 y)) (M.op X1 (M.op X0 y))) (M.op X3 (M.op X2 x))) ∨ (M.op X1 (M.op X0 y)) ≠ (M.op (M.op X1 (M.op X0 y)) (M.op X1 (M.op X0 y))) ∨ (M.op (M.op X1 (M.op X0 (M.op x y))) (M.op X1 (M.op X0 (M.op x y)))) = (M.op (M.op X3 (M.op X2 x)) (M.op X3 (M.op X2 x))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq1292710 eq1366810
    | (have j0 := eq1366810 X0 X1 X2 X3
       grind)
    | exact resolve eq1366810 eq1292710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1366810
  have eq1366812 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 y)) ≠ (M.op (M.op X1 (M.op X0 y)) (M.op X1 (M.op X0 y))) ∨ (M.op X1 (M.op X0 y)) = (k (M.op (M.op X1 (M.op X0 y)) (M.op X1 (M.op X0 y))) (M.op X3 (M.op X2 x))) ∨ (M.op (M.op X3 (M.op X2 x)) (M.op X3 (M.op X2 x))) = (M.op (M.op X1 (M.op X0 y)) (M.op X1 (M.op X0 y))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq1292710 eq1366811
    | (have j0 := eq1366811 X0 X1 X2 X3
       grind)
    | exact resolve eq1366811 eq1292710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1366811
  have eq1366894 : ∀ X0 X1 : G, y ≠ (M.op y y) ∨ y = (k (M.op y y) (M.op X0 (M.op X1 x))) ∨ (M.op y y) = (M.op (M.op X0 (M.op X1 x)) (M.op X0 (M.op X1 x))) := by
    intro X0 X1
    first
    | (have i₁ := eq1366812 y y x x
       have i₂ := eq54 y
       grind)
    | exact superpose eq54 eq1366812
    | exact resolve eq1366812 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1366812
  have eq1371140 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq6702 x (M.op y y)
       have i₂ := eq1303260 x
       grind)
    | exact superpose eq1303260 eq6702
    | exact resolve eq6702 eq1303260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6702 eq1303260
  have eq1371308 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq1371140
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1371140
    | exact resolve eq1371140 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq1371140
  have eq1371316 : y = (M.op y y) := by
    first
    | exact superpose eq1292710 eq1371308
    | exact resolve eq1371308 eq1292710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1292710 eq1371308
  have eq1371508 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq7108 y
       have i₂ := eq1371316
       grind)
    | exact superpose eq1371316 eq7108
    | exact resolve eq7108 eq1371316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7108
  have eq1371571 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq1371508
  have eq1371572 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq1371571
  have eq1371596 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1371572
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1371572
    | exact resolve eq1371572 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1371572
  have eq1371619 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1295452 eq1371596
    | exact resolve eq1371596 eq1295452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1371596
  have eq1594291 : ∀ X0 X1 : G, y = (k (M.op y y) (M.op X0 (M.op X1 x))) ∨ (M.op y y) = (M.op (M.op X0 (M.op X1 x)) (M.op X0 (M.op X1 x))) := by
    intro X0 X1
    first
    | (have j0 := eq1366894 X0 X1
       grind)
    | (have r₁ := eq1366894 X0 X1
       have r₂ := eq1371316
       grind)
    | exact resolve eq1366894 eq1371316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1366894
  have eq1594292 : ∀ X0 X1 : G, y = (k y (M.op X0 (M.op X1 x))) ∨ (M.op y y) = (M.op (M.op X0 (M.op X1 x)) (M.op X0 (M.op X1 x))) := by
    intro X0 X1
    first
    | (have i₁ := eq1594291 X0 X1
       have i₂ := eq1371316
       grind)
    | exact superpose eq1371316 eq1594291
    | (have j0 := eq1594291 X0 X1
       grind)
    | exact resolve eq1594291 eq1371316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1594291
  have eq1594293 : ∀ X0 X1 : G, y = (M.op (M.op X0 (M.op X1 x)) (M.op X0 (M.op X1 x))) ∨ y = (k y (M.op X0 (M.op X1 x))) := by
    intro X0 X1
    first
    | (have i₁ := eq1594292 X0 X1
       have i₂ := eq1371316
       grind)
    | exact superpose eq1371316 eq1594292
    | (have j0 := eq1594292 X0 X1
       grind)
    | exact resolve eq1594292 eq1371316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1594292
  have eq1594335 : y = (k y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1594293 x x
       have i₂ := eq54 x
       grind)
    | exact superpose eq54 eq1594293
    | exact resolve eq1594293 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq1594293
  have eq1595613 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq4693 y
       have i₂ := eq1594335
       grind)
    | exact superpose eq1594335 eq4693
    | (have j0 := eq4693 y
       grind)
    | exact resolve eq4693 eq1594335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4693 eq1594335
  have eq1595712 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq1595613
  have eq1595803 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1595712
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1595712
    | exact resolve eq1595712 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1595712
  have eq1595911 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq1595803
    | exact resolve eq1595803 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1595803
  have eq1596014 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1295452 eq1595911
    | exact resolve eq1595911 eq1295452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1595911
  have eq1596112 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq1596014
       have r₂ := eq28
       grind)
    | exact resolve eq1596014 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1596014
  have eq1596192 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1596112
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1596112
    | exact resolve eq1596112 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1596112
  have eq1596263 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1295452 eq1596192
    | exact resolve eq1596192 eq1295452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1596192
  have eq1597111 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1596263 eq6659
    | exact resolve eq6659 eq1596263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6659 eq1596263
  have eq1597164 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1371619 eq1597111
    | exact resolve eq1597111 eq1371619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1597111
  have eq1597187 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1295457 eq1597164
    | exact resolve eq1597164 eq1295457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1597164
  have eq1597195 : y = (M.op x x) := by
    first
    | (have r₁ := eq1597187
       have r₂ := eq28
       grind)
    | exact resolve eq1597187 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1597187
  have eq1597285 : x = (M.op y y) := by
    first
    | (have i₁ := eq56 x x
       have i₂ := eq1597195
       grind)
    | exact superpose eq1597195 eq56
    | exact resolve eq56 eq1597195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq1597195
  have eq1597368 : x = y := by
    first
    | (have i₁ := eq1597285
       have i₂ := eq1371316
       grind)
    | exact superpose eq1371316 eq1597285
    | exact resolve eq1597285 eq1371316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1371316 eq1597285
  have eq1597484 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq1597368
       grind)
    | exact superpose eq1597368 eq25
    | exact resolve eq25 eq1597368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1597368
  have eq1599070 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1295452 eq1597484
    | exact resolve eq1597484 eq1295452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1295452 eq1597484
  have eq1599656 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1599070
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1599070
    | exact resolve eq1599070 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1599070
  have eq1600970 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1599656 eq1295457
    | exact resolve eq1295457 eq1599656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1295457 eq1599656
  have eq1600986 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1371619 eq1600970
    | exact resolve eq1600970 eq1371619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1371619 eq1600970
  have eq1601109 : False := by grind
  exact eq1601109

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pyx_x_pyx_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
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
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 X0)
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X1 : G, (k (M.op X1 X1) X1) = X1 := by
    intro X1
    grind
  have eq76 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq84 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq91 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq76
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq76
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq76 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq99
    | exact resolve eq99 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq100
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq100
    | exact resolve eq100 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq248 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq65 (M.op X0 X0)
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq65
    | exact resolve eq65 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq416 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 X1 X2 (M.op X0 X0)
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq553 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq84 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq3278 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq416 X0 X0 X1
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq416
    | exact resolve eq416 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq416
  have eq3304 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq3278 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq3278
    | (have j0 := eq3278 y x
       grind)
    | exact resolve eq3278 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3306 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq27 eq3278
    | (have j0 := eq3278 (σ y) (σ x)
       grind)
    | exact resolve eq3278 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3278
  have eq13552 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq101 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13559 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq13552
    | exact resolve eq13552 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13552
  have eq13570 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq13559
       have r₂ := eq28
       grind)
    | exact resolve eq13559 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13559
  have eq13572 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq13570
    | exact resolve eq13570 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13570
  have eq13581 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq13572 eq54
    | exact resolve eq54 eq13572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13572
  have eq13606 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq13581
    | exact resolve eq13581 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13581
  have eq13607 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq13606
  have eq13616 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq54 x
       have i₂ := eq13607
       grind)
    | exact superpose eq13607 eq54
    | exact resolve eq54 eq13607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13607
  have eq13641 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13616
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq13616
    | exact resolve eq13616 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13616
  have eq13642 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq13641
  have eq13644 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13642 eq28
    | exact resolve eq28 eq13642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13655 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13642 eq3306
    | exact resolve eq3306 eq13642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3306
  have eq13663 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq13655
    | exact resolve eq13655 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13655
  have eq13794 : (M.op (σ x) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13663 eq248
    | exact resolve eq248 eq13663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13663
  have eq14016 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13642 eq13794
    | exact resolve eq13794 eq13642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13642 eq13794
  have eq14029 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq14016
  have eq14532 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14029 eq101
    | exact resolve eq101 eq14029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq14029
  have eq14549 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq14532
  have eq14558 : y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq14549
       have r₂ := eq13644
       grind)
    | exact resolve eq14549 eq13644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13644 eq14549
  have eq14990 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq54 x
       have i₂ := eq14558
       grind)
    | exact superpose eq14558 eq54
    | exact resolve eq54 eq14558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14558
  have eq15015 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14990
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14990
    | exact resolve eq14990 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14990
  have eq15016 : x = (M.op x y) := by grind
  clear eq15015
  have eq15018 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq15016 eq21
    | exact resolve eq21 eq15016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq15078 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq15016 eq3304
    | exact resolve eq3304 eq15016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3304
  have eq15086 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq15078
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq15078
    | exact resolve eq15078 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq15078
  have eq15136 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq15018
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15018
    | exact resolve eq15018 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15018
  have eq15137 : x = (M.op y y) := by
    first
    | exact superpose eq15016 eq15086
    | exact resolve eq15086 eq15016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15016 eq15086
  have eq15138 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq15136 eq27
    | exact resolve eq27 eq15136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15284 : x = (k y x) := by
    first
    | (have i₁ := eq248 y
       have i₂ := eq15137
       grind)
    | exact superpose eq15137 eq248
    | exact resolve eq248 eq15137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248 eq15137
  have eq15673 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq553 x y
       have i₂ := eq15284
       grind)
    | exact superpose eq15284 eq553
    | (have j0 := eq553 x y
       grind)
    | exact resolve eq553 eq15284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553 eq15284
  have eq15677 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq15673
  have eq15681 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq15677
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq15677
    | exact resolve eq15677 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15677
  have eq15693 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq15681
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15681
    | exact resolve eq15681 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15681
  have eq15703 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq15693
    | exact resolve eq15693 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq15693
  have eq15712 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq15136 eq15703
    | exact resolve eq15703 eq15136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15703
  have eq15715 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq15712
       have r₂ := eq28
       grind)
    | exact resolve eq15712 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15712
  have eq15718 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq15715
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15715
    | exact resolve eq15715 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq15715
  have eq15720 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq15136 eq15718
    | exact resolve eq15718 eq15136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15136 eq15718
  have eq15722 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq15720
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq15720
    | exact resolve eq15720 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq15720
  have eq16243 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq15722 eq54
    | exact resolve eq54 eq15722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq15722
  have eq16268 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15138 eq16243
    | exact resolve eq16243 eq15138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15138 eq16243
  have eq16269 : False := by grind
  exact eq16269

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,X) else if X = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pxx_pxy_pyx_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
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
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  have eq37 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 x X0
       grind)
    | exact resolve eq10 eq24
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
  have eq45 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq55 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 X0)
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq68 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq45
  have eq75 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (k (M.op X0 X0) X0)) (k (M.op X0 X0) X0)) := by
    intro X0 X1
    grind
  have eq82 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq82
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq82
    | (have j1 := eq11 (σ (M.op x y)) (k (σ y) (σ x))
       grind)
    | exact resolve eq82 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq102
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq102
    | exact resolve eq102 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq108 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq22 eq107
    | exact resolve eq107 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq243 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    grind
  have eq246 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    grind
  clear eq57
  have eq349 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq75 X0 X1
       have i₂ := eq243 X0
       grind)
    | exact superpose eq243 eq75
    | exact resolve eq75 eq243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq359 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq28 eq349
    | (have j0 := eq349 (σ y) (σ x)
       grind)
    | exact resolve eq349 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq476 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq55 (σ X0)
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq55
    | (have j1 := eq66 X0
       grind)
    | exact resolve eq55 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq483 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ (k X0 X0))) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) X1 (σ X0)
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq14
    | (have j1 := eq66 X0
       grind)
    | exact resolve eq14 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq485 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq483 X0 x
       have i₂ := eq349 (σ (k X0 X0)) x
       grind)
    | exact superpose eq349 eq483
    | (have j0 := eq483 X0 x
       grind)
    | exact resolve eq483 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349 eq483
  have eq4153 : ∀ X0 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (k X0 (σ (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq476 (τ X0)
       have i₂ := eq36 X0 (τ X0)
       grind)
    | exact superpose eq36 eq476
    | (have j0 := eq476 (τ X0)
       grind)
    | exact resolve eq476 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq476
  have eq4176 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq4153 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq4153
    | (have j0 := eq4153 X0
       grind)
    | exact resolve eq4153 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4153
  have eq4187 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4176 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq4176
    | (have j0 := eq4176 X0
       grind)
    | exact resolve eq4176 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4176
  have eq16542 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq108 eq11
    | (have j0 := eq11 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq11 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16543 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq28 eq16542
    | exact resolve eq16542 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16542
  have eq16554 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq16543
       have r₂ := eq29
       grind)
    | exact resolve eq16543 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16543
  have eq16563 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq16554 eq55
    | exact resolve eq55 eq16554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16554
  have eq16594 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq16563
    | exact resolve eq16563 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16563
  have eq16596 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq68
       have i₂ := eq16594
       grind)
    | exact superpose eq16594 eq68
    | exact resolve eq68 eq16594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16606 : x = (k y x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq243 x
       have i₂ := eq16594
       grind)
    | exact superpose eq16594 eq243
    | exact resolve eq243 eq16594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16594
  have eq16633 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq16596
  have eq16638 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16633
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq16633
    | exact resolve eq16633 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16633
  have eq16789 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq82
       have i₂ := eq16606
       grind)
    | exact superpose eq16606 eq82
    | exact resolve eq82 eq16606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq16606
  have eq16811 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16789
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16789
    | exact resolve eq16789 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16789
  have eq17298 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16638 eq4187
    | (have j0 := eq4187 (σ x)
       grind)
    | exact resolve eq4187 eq16638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4187 eq16638
  have eq17299 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq17298
    | exact resolve eq17298 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17298
  have eq17300 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq17299
  have eq17397 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16811 eq11
    | (have j0 := eq11 (σ x) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq11 eq16811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16811
  have eq17398 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq17397
  have eq17402 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq17398
    | exact resolve eq17398 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17398
  have eq17403 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq17402
  have eq18104 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq17403 eq17300
    | exact resolve eq17300 eq17403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17300 eq17403
  have eq18141 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq18104
  have eq18148 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq18141 eq29
    | exact resolve eq29 eq18141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18153 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq18141 eq359
    | exact resolve eq359 eq18141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359
  have eq18187 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq28 eq18153
    | exact resolve eq18153 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18153
  have eq18208 : (M.op (σ x) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq18187 eq246
    | exact resolve eq246 eq18187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246 eq18187
  have eq18327 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq18141 eq18208
    | exact resolve eq18208 eq18141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18141 eq18208
  have eq18336 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq18327
  have eq18792 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq18336 eq108
    | exact resolve eq108 eq18336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq18336
  have eq18805 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq18792
  have eq18815 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq18805
       have r₂ := eq18148
       grind)
    | exact resolve eq18805 eq18148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18805
  have eq18867 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq55 x
       have i₂ := eq18815
       grind)
    | exact superpose eq18815 eq55
    | exact resolve eq55 eq18815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq18815
  have eq18899 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18867
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq18867
    | exact resolve eq18867 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18867
  have eq19037 : y = (τ (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq18899 eq31
    | exact resolve eq31 eq18899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18899
  have eq19183 : x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq19037
    | exact resolve eq19037 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq19037
  have eq19184 : x = (M.op x y) ∨ x = y := by grind
  clear eq19183
  have eq19187 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq19184 eq22
    | exact resolve eq22 eq19184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19321 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq19187
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq19187
    | exact resolve eq19187 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19187
  have eq19400 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq19321 eq18148
    | (have r₁ := eq18148
       have r₂ := eq19321
       grind)
    | exact resolve eq18148 eq19321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18148 eq19321
  have eq19407 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq19400
  have eq19408 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq19407
  have eq19613 : y = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq19408 eq31
    | exact resolve eq31 eq19408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq19408
  have eq19788 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq32 eq19613
    | exact resolve eq19613 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq19613
  have eq19872 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq19788 eq19184
    | exact resolve eq19184 eq19788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19184 eq19788
  have eq19873 : x = y := by grind
  clear eq19872
  have eq19926 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq20
       have i₂ := eq19873
       grind)
    | exact superpose eq19873 eq20
    | exact resolve eq20 eq19873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq19927 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq26
       have i₂ := eq19873
       grind)
    | exact superpose eq19873 eq26
    | exact resolve eq26 eq19873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq19873
  have eq20062 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq19927
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq19927
    | exact resolve eq19927 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19927
  have eq20069 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq20062 eq28
    | exact resolve eq28 eq20062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq20062
  have eq20226 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq68
       have i₂ := eq19926
       grind)
    | exact superpose eq19926 eq68
    | exact resolve eq68 eq19926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq20235 : x = (k (M.op x y) x) := by
    first
    | (have i₁ := eq243 x
       have i₂ := eq19926
       grind)
    | exact superpose eq19926 eq243
    | exact resolve eq243 eq19926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19926
  have eq20273 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22 eq20226
    | exact resolve eq20226 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20226
  have eq20301 : (σ x) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq20069 eq243
    | exact resolve eq243 eq20069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq21754 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  have eq21769 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20069 eq21754
    | exact resolve eq21754 eq20069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21754
  have eq21782 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq21769
       have r₂ := eq29
       grind)
    | exact resolve eq21769 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21769
  have eq21788 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20069 eq21782
    | exact resolve eq21782 eq20069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21782
  have eq21793 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21788 eq29
    | exact resolve eq29 eq21788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21833 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21788 eq20301
    | exact resolve eq20301 eq21788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20301 eq21788
  have eq21988 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21833 eq20273
    | exact resolve eq20273 eq21833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20273 eq21833
  have eq22008 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq21988
  have eq22018 : x = (M.op x y) := by
    first
    | (have r₁ := eq22008
       have r₂ := eq21793
       grind)
    | exact resolve eq22008 eq21793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21793 eq22008
  have eq22099 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq22018 eq22
    | exact resolve eq22 eq22018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq22186 : x = (k x x) := by
    first
    | exact superpose eq22018 eq20235
    | exact resolve eq20235 eq22018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20235 eq22018
  have eq22271 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22099
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq22099
    | exact resolve eq22099 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22099
  have eq22587 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq485 x
       have i₂ := eq22186
       grind)
    | exact superpose eq22186 eq485
    | (have j0 := eq485 x
       grind)
    | exact resolve eq485 eq22186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485 eq22186
  have eq22595 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq22587
  have eq22608 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq22595
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq22595
    | exact resolve eq22595 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq22595
  have eq22626 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20069 eq22608
    | exact resolve eq22608 eq20069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20069 eq22608
  have eq22642 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22271 eq22626
    | exact resolve eq22626 eq22271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22271 eq22626
  have eq22658 : False := by grind
  exact eq22658

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then X else if m(X,X) = m(Y,Y) then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_x_y_pxy_Equation1904 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  have eq47 : (σ (k x y)) = (k (σ x) (σ y)) := by
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
  have eq51 : ∀ X0 : G, x = (M.op (M.op X0 (M.op x y)) (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (σ x))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 X0)
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq108 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  have eq115 : (k (σ (M.op x y)) (σ x)) = (σ (M.op (M.op x y) x)) ∨ (M.op x x) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq108
       have i₂ := eq11 sF0 x
       grind)
    | exact superpose eq11 eq108
    | (have j1 := eq11 x (M.op x y)
       grind)
    | exact resolve eq108 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq108 eq16
    | exact resolve eq16 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq214 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq35 X0 X1
       have i₂ := eq11 (τ X0) X1
       grind)
    | exact superpose eq11 eq35
    | (have j1 := eq11 X1 (τ X0)
       grind)
    | exact resolve eq35 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq230 : y = (M.op (M.op x y) (M.op y y)) := by
    first
    | (have i₁ := eq56 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq56
    | (have j0 := eq56 y x
       grind)
    | exact resolve eq56 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq231 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq27 eq56
    | (have j0 := eq56 (σ y) (σ x)
       grind)
    | exact resolve eq56 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq236 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq54 (M.op X0 X0)
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq54
    | exact resolve eq54 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq237 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X0 X0) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 X0) X1 X2
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq241 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 y) (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq230 eq14
    | exact resolve eq14 eq230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230
  have eq244 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq231 eq14
    | exact resolve eq14 eq231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231
  have eq263 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq276 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) X2)) = (M.op X0 (M.op (M.op X1 (M.op (M.op X0 X0) X2)) (M.op X1 (M.op (M.op X0 X0) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 (M.op X0 X0) X0 X1 X2
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq282 : ∀ X0 X1 : G, (M.op X0 (M.op y X1)) = (M.op (M.op x y) (M.op (M.op X0 (M.op y X1)) (M.op X0 (M.op y X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq53 y x X0 X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq53
    | (have j0 := eq53 y x X0 X1
       grind)
    | exact resolve eq53 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq284 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) X1)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (M.op (σ y) X1)) (M.op X0 (M.op (σ y) X1)))) := by
    intro X0 X1
    first
    | exact superpose eq27 eq53
    | (have j0 := eq53 (σ y) (σ x) X0 X1
       grind)
    | exact resolve eq53 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq286 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 X1 X2 (M.op X0 X0)
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq289 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op X4 (M.op X2 (M.op X0 X3))) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 (M.op X1 (M.op X0 X2)) X1 X2 (M.op X0 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq290 : ∀ X0 X1 X2 : G, (M.op X0 x) = (M.op (M.op X2 (M.op X1 (M.op x y))) (M.op (M.op X0 x) (M.op X0 x))) := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq304 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X2 X0) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 X2 (M.op X0 X1) X1
       have i₂ := eq56 (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq56 eq53
    | exact resolve eq53 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq375 : ∀ X0 X1 X2 : G, (σ X2) = (M.op (M.op X1 (M.op (σ X0) (σ X0))) (M.op (σ X0) (σ X0))) ∨ (σ (k X0 X2)) = (M.op (σ X0) (σ X2)) ∨ (σ X0) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (σ X0) X1 (σ X0)
       have i₂ := eq76 X0 X1
       grind)
    | (have i₁ := eq14 (σ X1) X1 (σ X1)
       have i₂ := eq76 X0 X1
       grind)
    | exact superpose eq76 eq14
    | (have j1 := eq76 X0 X2
       grind)
    | exact resolve eq14 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq376 : ∀ X0 X2 : G, (σ X0) = (σ X2) ∨ (σ (k X0 X2)) = (M.op (σ X0) (σ X2)) ∨ (σ X0) = (σ X2) := by
    intro X0 X2
    first
    | (have i₁ := eq375 X0 x X2
       have i₂ := eq14 (σ X0) x (σ X0)
       grind)
    | exact superpose eq14 eq375
    | (have j0 := eq375 X0 x X2
       grind)
    | exact resolve eq375 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375
  have eq377 : ∀ X0 X2 : G, (σ (k X0 X2)) = (M.op (σ X0) (σ X2)) ∨ (σ X0) = (σ X2) := by
    intro X0 X2
    first
    | (have j0 := eq376 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376
  have eq419 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq217 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq217
    | exact resolve eq217 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq429 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq217 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq217
    | (have j0 := eq217 X0 x
       grind)
    | exact resolve eq217 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq503 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (M.op X1 X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq263 X0 X1
       have i₂ := eq11 (σ X0) X1
       grind)
    | exact superpose eq11 eq263
    | (have j1 := eq11 X1 (σ X0)
       grind)
    | exact resolve eq263 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263
  have eq2803 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq377 x X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq377
    | (have j0 := eq377 x X0
       grind)
    | exact resolve eq377 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2805 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ X0) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq21 eq377
    | (have j0 := eq377 (M.op x y) X0
       grind)
    | exact resolve eq377 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2806 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq377 X0 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq377
    | exact resolve eq377 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2864 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq377 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq377
    | (have j0 := eq377 X0 x
       grind)
    | exact resolve eq377 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2866 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ X0) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq21 eq377
    | (have j0 := eq377 X0 (M.op x y)
       grind)
    | exact resolve eq377 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2872 : ∀ X0 X1 X2 : G, (M.op X2 (σ X1)) = (M.op (σ (k X0 X1)) (M.op (M.op X2 (σ X1)) (M.op X2 (σ X1)))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq286 (σ X1) X2 (σ X0)
       have i₂ := eq377 X0 X1
       grind)
    | exact superpose eq377 eq286
    | (have j1 := eq377 X0 X1
       grind)
    | exact resolve eq286 eq377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377
  have eq2875 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2806 X0 X1
       have i₂ := eq39 X0 X1
       grind)
    | exact superpose eq39 eq2806
    | (have j0 := eq2806 X0 X1
       grind)
    | exact resolve eq2806 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq2806
  have eq2938 : ∀ X0 X1 : G, (M.op x x) = (M.op (M.op X0 (M.op X1 (M.op x y))) x) := by
    intro X0 X1
    first
    | (have i₁ := eq290 x X1 X0
       have i₂ := eq56 x x
       grind)
    | exact superpose eq56 eq290
    | exact resolve eq290 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq2953 : (M.op x x) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq2938 sF0 sF0
       have i₂ := eq54 sF0
       grind)
    | exact superpose eq54 eq2938
    | exact resolve eq2938 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2938
  have eq3019 : ∀ X0 : G, (M.op (M.op y X0) (M.op y X0)) = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq282 (M.op y X0) X0
       have i₂ := eq56 (M.op y X0) (M.op y X0)
       grind)
    | exact superpose eq56 eq282
    | exact resolve eq282 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3022 : ∀ X0 X1 X2 : G, (M.op x y) = (M.op (M.op X2 (M.op X0 (M.op y X1))) (M.op (M.op x y) (M.op x y))) := by
    intro X0 X1 X2
    first
    | exact superpose eq282 eq14
    | exact resolve eq14 eq282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282
  have eq3073 : ∀ X0 : G, (M.op (M.op (σ y) X0) (M.op (σ y) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq284 (M.op sF3 x) x
       have i₂ := eq56 (M.op sF3 x) (M.op sF3 x)
       grind)
    | exact superpose eq56 eq284
    | exact resolve eq284 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3121 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (σ x) (σ y))) = (M.op (M.op X3 (M.op X4 (M.op X0 (M.op (σ y) X1)))) (M.op (M.op X2 (M.op (σ x) (σ y))) (M.op X2 (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq284 eq289
    | exact resolve eq289 eq284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284
  have eq3206 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 (M.op X0 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq289 X0 X0 X2 X3 X1
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq289
    | exact resolve eq289 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289
  have eq4556 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq214 (σ X0) X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq214
    | exact resolve eq214 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq4643 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4556 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq4556
    | (have j0 := eq4556 X0 X1
       grind)
    | exact resolve eq4556 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4556
  have eq4749 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq276 X0 X1 (M.op X0 X0)
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq276
    | exact resolve eq276 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4790 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) = (M.op X0 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq276 X0 (M.op (M.op X0 X0) X1) X1
       have i₂ := eq56 (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq56 eq276
    | exact resolve eq276 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq5966 : ∀ X0 : G, (M.op y y) = (M.op (M.op X0 (M.op x y)) y) := by
    intro X0
    first
    | exact superpose eq241 eq237
    | exact resolve eq237 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241
  have eq5970 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | exact superpose eq244 eq237
    | exact resolve eq237 eq244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244
  have eq6065 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op X0 (M.op y y)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq5966 eq237
    | exact resolve eq237 eq5966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5966
  have eq6084 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op (σ y) (σ y))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq5970 eq237
    | exact resolve eq237 eq5970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237 eq5970
  have eq6300 : (M.op (M.op x y) (M.op x y)) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq6065 y
       have i₂ := eq54 y
       grind)
    | exact superpose eq54 eq6065
    | exact resolve eq6065 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6065
  have eq7278 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq6084 sF3
       have i₂ := eq54 sF3
       grind)
    | exact superpose eq54 eq6084
    | exact resolve eq6084 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6084
  have eq8955 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2803 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq2803
    | (have j0 := eq2803 y
       grind)
    | exact resolve eq2803 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2803
  have eq8970 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq8955
       have i₂ := eq47
       grind)
    | exact superpose eq47 eq8955
    | exact resolve eq8955 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8955
  have eq8981 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq8970
    | exact resolve eq8970 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8970
  have eq9181 : (σ (k (M.op x y) x)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2805 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq2805
    | (have j0 := eq2805 x
       grind)
    | exact resolve eq2805 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2805
  have eq9196 : (k (σ (M.op x y)) (σ x)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq108 eq9181
    | exact resolve eq9181 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq9181
  have eq9619 : ∀ X0 : G, (σ (k (τ X0) (M.op x y))) = (M.op X0 (σ (M.op x y))) ∨ (σ (M.op x y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq2866 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq2866
    | exact resolve eq2866 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2866
  have eq9702 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (M.op X0 (σ (M.op x y))) ∨ (σ (M.op x y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9619 X0
       have i₂ := eq35 X0 sF0
       grind)
    | exact superpose eq35 eq9619
    | (have j0 := eq9619 X0
       grind)
    | exact resolve eq9619 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9619
  have eq9704 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (M.op X0 (σ (M.op x y))) ∨ (σ (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq21 eq9702
    | (have j0 := eq9702 X0
       grind)
    | exact resolve eq9702 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9702
  have eq9850 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2875 X0 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq2875
    | exact resolve eq2875 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2875
  have eq10113 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq47
       have i₂ := eq9850 x y
       grind)
    | exact superpose eq9850 eq47
    | (have j1 := eq9850 (σ (M.op x y)) (k (σ x) (σ y))
       grind)
    | exact resolve eq47 eq9850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq9850
  have eq10300 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq10113
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq10113
    | exact resolve eq10113 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10113
  have eq10310 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq10300
    | exact resolve eq10300 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10300
  have eq10327 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq10310 eq8981
    | exact resolve eq8981 eq10310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8981 eq10310
  have eq10336 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq10327
       have r₂ := eq28
       grind)
    | exact resolve eq10327 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10327
  have eq10362 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq10336 eq30
    | exact resolve eq30 eq10336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq10336
  have eq10481 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq10362
    | exact resolve eq10362 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10362
  have eq10482 : x = y := by grind
  clear eq10481
  have eq10509 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq10482
       grind)
    | exact superpose eq10482 eq19
    | exact resolve eq19 eq10482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq10510 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq10482
       grind)
    | exact superpose eq10482 eq25
    | exact resolve eq25 eq10482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq10628 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq10510
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10510
    | exact resolve eq10510 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10510
  have eq10657 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq10628 eq27
    | exact resolve eq27 eq10628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq10841 : ∀ X0 X1 : G, x = (M.op (M.op X0 (M.op x X1)) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 x X0 X1
       have i₂ := eq10509
       grind)
    | exact superpose eq10509 eq14
    | exact resolve eq14 eq10509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10842 : x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq54 x
       have i₂ := eq10509
       grind)
    | exact superpose eq10509 eq54
    | exact resolve eq54 eq10509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10925 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq10657 eq54
    | exact resolve eq54 eq10657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11051 : ∀ X0 : G, (M.op (M.op x X0) (M.op x X0)) = (M.op (M.op x y) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq3019 X0
       have i₂ := eq10482
       grind)
    | exact superpose eq10482 eq3019
    | exact resolve eq3019 eq10482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3019
  have eq11149 : ∀ X0 X1 X2 : G, (M.op x y) = (M.op (M.op X2 (M.op X0 (M.op y X1))) (M.op y (M.op x y))) := by
    intro X0 X1 X2
    first
    | exact superpose eq6300 eq3022
    | exact resolve eq3022 eq6300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3022
  have eq11150 : ∀ X0 X1 X2 : G, (M.op x y) = (M.op (M.op X2 (M.op X0 (M.op x X1))) (M.op x (M.op x y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11149 X0 X1 X2
       have i₂ := eq10482
       grind)
    | exact superpose eq10482 eq11149
    | exact resolve eq11149 eq10482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11149
  have eq11151 : ∀ X0 X1 X2 : G, (M.op x y) = (M.op (M.op X2 (M.op X0 (M.op x X1))) x) := by
    intro X0 X1 X2
    first
    | exact superpose eq10842 eq11150
    | exact resolve eq11150 eq10842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11150
  have eq11175 : ∀ X0 : G, (M.op x y) = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq11151 (M.op x X0) X0 (M.op x X0)
       have i₂ := eq54 (M.op x X0)
       grind)
    | exact superpose eq54 eq11151
    | exact resolve eq11151 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11151
  have eq11310 : ∀ X0 : G, (M.op (M.op (σ x) X0) (M.op (σ x) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq10628 eq3073
    | exact resolve eq3073 eq10628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3073
  have eq11319 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (M.op X1 X0) (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0))) := by
    intro X0 X1
    first
    | exact superpose eq11310 eq286
    | exact resolve eq286 eq11310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286 eq11310
  have eq12198 : ∀ X0 : G, (M.op x X0) = (M.op X0 (M.op (M.op x y) (M.op x X0))) := by
    intro X0
    first
    | (have i₁ := eq4749 X0 x
       have i₂ := eq11051 X0
       grind)
    | (have i₁ := eq4749 y x
       have i₂ := eq11051 y
       grind)
    | exact superpose eq11051 eq4749
    | exact resolve eq4749 eq11051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11051
  have eq16047 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (σ x) (σ x)) X0)) = (M.op (M.op (M.op (σ x) (σ x)) X0) (M.op (M.op (σ x) (σ x)) X0)) := by
    intro X0
    first
    | exact superpose eq52 eq304
    | exact resolve eq304 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq16451 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq10657 eq16047
    | exact resolve eq16047 eq10657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16047
  have eq18538 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x X0)) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq12198 eq14
    | exact resolve eq14 eq12198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12198
  have eq20821 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3206 X0 (M.op x (M.op x (M.op X0 X1))) (M.op X0 X1) X1
       have i₂ := eq18538 (M.op X0 X1) x
       grind)
    | exact superpose eq18538 eq3206
    | exact resolve eq3206 eq18538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3206
  have eq20965 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20821 (M.op X1 X0) (M.op X0 X0)
       have i₂ := eq56 X0 X1
       grind)
    | exact superpose eq56 eq20821
    | exact resolve eq20821 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20821
  have eq24964 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ (k X0 x)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x)))) ∨ (σ X0) = (σ x) := by
    intro X0
    first
    | exact superpose eq2864 eq11319
    | (have j1 := eq2864 X0
       grind)
    | exact resolve eq11319 eq2864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2864 eq11319
  have eq25158 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ (k X0 x)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ X0) = (σ x) := by
    intro X0
    first
    | exact superpose eq10657 eq24964
    | (have j0 := eq24964 X0
       grind)
    | exact resolve eq24964 eq10657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24964
  have eq25229 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ (k X0 x)) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (σ X0) = (σ x) := by
    intro X0
    first
    | exact superpose eq7278 eq25158
    | (have j0 := eq25158 X0
       grind)
    | exact resolve eq25158 eq7278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7278 eq25158
  have eq25263 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ (k X0 x)) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ X0) = (σ x) := by
    intro X0
    first
    | exact superpose eq10628 eq25229
    | (have j0 := eq25229 X0
       grind)
    | exact resolve eq25229 eq10628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25229
  have eq25273 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ (k X0 x)) (σ x)) ∨ (σ X0) = (σ x) := by
    intro X0
    first
    | exact superpose eq10925 eq25263
    | (have j0 := eq25263 X0
       grind)
    | exact resolve eq25263 eq10925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25263
  have eq27955 : (k (σ (M.op x y)) (σ x)) = (σ (M.op x x)) ∨ (M.op x x) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2953 eq115
    | exact resolve eq115 eq2953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq2953
  have eq27956 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op x x) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq27955
       have i₂ := eq10509
       grind)
    | exact superpose eq10509 eq27955
    | exact resolve eq27955 eq10509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27955
  have eq27957 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op x x) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq27956
    | exact resolve eq27956 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27956
  have eq27958 : (M.op x x) = (M.op y (M.op x y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6300 eq27957
    | exact resolve eq27957 eq6300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6300 eq27957
  have eq27959 : (M.op x x) = (M.op x (M.op x y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq27958
       have i₂ := eq10482
       grind)
    | exact superpose eq10482 eq27958
    | exact resolve eq27958 eq10482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10482 eq27958
  have eq27960 : x = (M.op x x) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10842 eq27959
    | exact resolve eq27959 eq10842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27959
  have eq27961 : x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq27960
       have i₂ := eq10509
       grind)
    | exact superpose eq10509 eq27960
    | exact resolve eq27960 eq10509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27960
  have eq27962 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq27961
  have eq27963 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq9196 eq27962
    | exact resolve eq27962 eq9196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9196
  have eq27970 : (τ (σ (M.op x y))) = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27962 eq121
    | exact resolve eq121 eq27962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq27962
  have eq27993 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq27970
    | exact resolve eq27970 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27970
  have eq28014 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27993 eq25273
    | (have j0 := eq25273 (M.op x y)
       grind)
    | exact resolve eq25273 eq27993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25273 eq27993
  have eq28023 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq28014
    | exact resolve eq28014 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28014
  have eq28035 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq28023
    | exact resolve eq28023 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28023
  have eq29792 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28035 eq27963
    | exact resolve eq27963 eq28035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27963 eq28035
  have eq29827 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq29792
  have eq29843 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq29827
       have r₂ := eq28
       grind)
    | exact resolve eq29827 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29827
  have eq29869 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29843 eq29
    | exact resolve eq29 eq29843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq29843
  have eq30047 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq29869
    | exact resolve eq29869 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq29869
  have eq30048 : x = (M.op x y) := by grind
  clear eq30047
  have eq30140 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq30048 eq21
    | exact resolve eq21 eq30048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq30219 : ∀ X0 X1 : G, x = (M.op (M.op X0 (M.op x X1)) x) := by
    intro X0 X1
    first
    | exact superpose eq30048 eq10841
    | exact resolve eq10841 eq30048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10841
  have eq30320 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq30140
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq30140
    | exact resolve eq30140 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30140
  have eq30530 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq30320 eq10657
    | exact resolve eq10657 eq30320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10657
  have eq30532 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq30320 eq10925
    | exact resolve eq10925 eq30320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10925
  have eq41075 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq30320 eq16451
    | exact resolve eq16451 eq30320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16451
  have eq45112 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) X1)) = (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq41075 X1
       have i₂ := eq304 sF4 X1 x
       grind)
    | (have i₁ := eq41075 sF4
       have i₂ := eq304 sF4 sF4 sF4
       grind)
    | exact superpose eq304 eq41075
    | exact resolve eq41075 eq304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304 eq41075
  have eq66170 : ∀ X0 X1 : G, (M.op (σ (M.op x y)) (M.op X0 (M.op (σ x) (σ y)))) = (M.op (M.op X1 (M.op (σ x) (σ y))) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq45112 X0 (M.op (M.op X1 sF4) (M.op X1 sF4))
       have i₂ := eq4749 sF4 X1
       grind)
    | exact superpose eq4749 eq45112
    | exact resolve eq45112 eq4749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4749 eq45112
  have eq100092 : ∀ X0 : G, (σ (τ (k X0 (σ x)))) = (σ (M.op (τ X0) x)) ∨ (M.op x x) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq4643 (τ X0) x
       have i₂ := eq429 X0
       grind)
    | exact superpose eq429 eq4643
    | (have j0 := eq4643 x (τ X0)
       grind)
    | exact resolve eq4643 eq429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4643
  have eq100586 : ∀ X0 : G, (k X0 (σ x)) = (σ (M.op (τ X0) x)) ∨ (M.op x x) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq100092 X0
       have i₂ := eq15 (k X0 sF2)
       grind)
    | exact superpose eq15 eq100092
    | (have j0 := eq100092 X0
       grind)
    | exact resolve eq100092 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100092
  have eq100786 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (σ (M.op (τ X0) x)) ∨ (M.op x x) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = x := by
    intro X0
    first
    | exact superpose eq30320 eq100586
    | (have j0 := eq100586 X0
       grind)
    | exact resolve eq100586 eq30320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100586
  have eq100951 : ∀ X0 : G, (M.op x y) = (M.op (τ X0) (τ X0)) ∨ (k X0 (σ (M.op x y))) = (σ (M.op (τ X0) x)) ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq100786 X0
       have i₂ := eq10509
       grind)
    | exact superpose eq10509 eq100786
    | (have j0 := eq100786 X0
       grind)
    | exact resolve eq100786 eq10509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10509 eq100786
  have eq101090 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (σ (M.op (τ X0) x)) ∨ x = (M.op (τ X0) (τ X0)) ∨ (τ X0) = x := by
    intro X0
    first
    | exact superpose eq30048 eq100951
    | (have j0 := eq100951 X0
       grind)
    | exact resolve eq100951 eq30048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100951
  have eq106952 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X0) X1)) = (M.op X1 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4790 X0 X1
       have i₂ := eq20965 X1 (M.op X0 X0)
       grind)
    | exact superpose eq20965 eq4790
    | exact resolve eq4790 eq20965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4790
  have eq106965 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq106952 (M.op X0 X0) X1
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq106952
    | exact resolve eq106952 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq106952
  have eq131406 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (σ x) (σ y))) = (M.op (M.op X3 (M.op X4 (M.op X0 (M.op (σ y) X1)))) (M.op (σ (M.op x y)) (M.op X2 (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq66170 eq3121
    | exact resolve eq3121 eq66170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3121 eq66170
  have eq131407 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (σ x) (σ y))) = (M.op (M.op X3 (M.op X4 (M.op X0 (M.op (σ x) X1)))) (M.op (σ (M.op x y)) (M.op X2 (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq10628 eq131406
    | exact resolve eq131406 eq10628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10628 eq131406
  have eq131408 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (σ x) (σ y))) = (M.op (M.op X3 (M.op X4 (M.op X0 (M.op (σ (M.op x y)) X1)))) (M.op (σ (M.op x y)) (M.op X2 (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq30320 eq131407
    | exact resolve eq131407 eq30320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131407
  have eq131538 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (σ x) (σ y))) = (M.op (M.op X2 (M.op (σ (M.op x y)) X0)) (M.op (σ (M.op x y)) (M.op X1 (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq131408 (M.op sF1 X1) X1 X2 x (M.op sF1 X1)
       have i₂ := eq54 (M.op sF1 X1)
       grind)
    | exact superpose eq54 eq131408
    | exact resolve eq131408 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131408
  have eq141471 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) ∨ (M.op (σ X0) (σ X0)) = (M.op (M.op (σ X0) (σ X0)) (M.op (σ X0) (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq503 X0 (M.op (σ X0) (σ X0))
       have i₂ := eq54 (σ X0)
       grind)
    | exact superpose eq54 eq503
    | (have j0 := eq503 X0 (M.op (σ X0) (σ X0))
       grind)
    | exact resolve eq503 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503
  have eq141658 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 ∨ (M.op (σ X0) (σ X0)) = (M.op (M.op (σ X0) (σ X0)) (M.op (σ X0) (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq141471 X0
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq141471
    | (have j0 := eq141471 X0
       grind)
    | exact resolve eq141471 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141471
  have eq141779 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (M.op (σ X0) (σ X0))) ∨ (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq141658 X0
       have i₂ := eq106965 (σ X0) (σ X0)
       grind)
    | exact superpose eq106965 eq141658
    | (have j0 := eq141658 X0
       grind)
    | exact resolve eq141658 eq106965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106965 eq141658
  have eq141875 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq141779 X0
       have i₂ := eq54 (σ X0)
       grind)
    | exact superpose eq54 eq141779
    | (have j0 := eq141779 X0
       grind)
    | exact resolve eq141779 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq141779
  have eq141876 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq141875 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141875
  have eq193905 : ∀ X0 X1 X2 : G, (M.op X2 (σ X1)) = (M.op (σ (k X0 X1)) (M.op (σ X1) (M.op X2 (σ X1)))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2872 X0 X1 X2
       have i₂ := eq20965 (σ X1) X2
       grind)
    | exact superpose eq20965 eq2872
    | (have j0 := eq2872 X0 X1 X2
       grind)
    | exact resolve eq2872 eq20965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2872 eq20965
  have eq193931 : ∀ X0 X1 X2 : G, (M.op X2 (σ (τ X1))) = (M.op (σ (τ (k X0 X1))) (M.op (σ (τ X1)) (M.op X2 (σ (τ X1))))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq193905 (τ X0) (τ X1) X2
       have i₂ := eq419 X1 X0
       grind)
    | exact superpose eq419 eq193905
    | (have j0 := eq193905 (τ X0) (τ X1) X2
       grind)
    | exact resolve eq193905 eq419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419 eq193905
  have eq194576 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op (σ (τ (k X0 X1))) (M.op X1 (M.op X2 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq193931 X0 X0 X2
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq193931
    | (have j0 := eq193931 X0 X1 X2
       grind)
    | exact resolve eq193931 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193931
  have eq194791 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op (k X0 X1) (M.op X1 (M.op X2 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq194576 X0 X1 X2
       have i₂ := eq15 (k X0 X1)
       grind)
    | exact superpose eq15 eq194576
    | (have j0 := eq194576 X0 X1 X2
       grind)
    | exact resolve eq194576 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194576
  have eq194982 : ∀ X0 X1 X2 : G, (σ (τ X0)) = X1 ∨ (M.op X2 X1) = (M.op (k X0 X1) (M.op X1 (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq194791 X0 X1 X2
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq194791
    | (have j0 := eq194791 X0 X1 X2
       grind)
    | exact resolve eq194791 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194791
  have eq195156 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op (k X0 X1) (M.op X1 (M.op X2 X1))) ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq194982 X0 X1 X2
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq194982
    | (have j0 := eq194982 X0 X1 X2
       grind)
    | exact resolve eq194982 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194982
  have eq737884 : ∀ X1 : G, (M.op x y) = (M.op (k X1 x) (M.op x (M.op x y))) ∨ x = X1 := by
    intro X1
    first
    | (have i₁ := eq195156 x x (M.op x x)
       have i₂ := eq11175 x
       grind)
    | exact superpose eq11175 eq195156
    | (have j0 := eq195156 (M.op x y) (M.op (k X1 x) (M.op x (M.op x y))) x
       grind)
    | exact resolve eq195156 eq11175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11175 eq195156
  have eq739042 : ∀ X1 : G, (M.op x y) = (M.op (k X1 x) x) ∨ x = X1 := by
    intro X1
    first
    | exact superpose eq10842 eq737884
    | (have j0 := eq737884 X1
       grind)
    | exact resolve eq737884 eq10842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10842 eq737884
  have eq739553 : ∀ X1 : G, x = (M.op (k X1 x) x) ∨ x = X1 := by
    intro X1
    first
    | exact superpose eq30048 eq739042
    | (have j0 := eq739042 (M.op (k X1 x) x)
       grind)
    | exact resolve eq739042 eq30048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30048 eq739042
  have eq741218 : ∀ X0 : G, x = (M.op (τ (k X0 (σ x))) x) ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq739553 (τ X0)
       have i₂ := eq429 X0
       grind)
    | exact superpose eq429 eq739553
    | (have j0 := eq739553 (M.op (τ (k X0 (σ x))) x)
       grind)
    | exact resolve eq739553 eq429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429 eq739553
  have eq741481 : ∀ X0 : G, x = (M.op (τ (k X0 (σ (M.op x y)))) x) ∨ (τ X0) = x := by
    intro X0
    first
    | exact superpose eq30320 eq741218
    | (have j0 := eq741218 X0
       grind)
    | exact resolve eq741218 eq30320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741218
  have eq769452 : ∀ X0 : G, x = (M.op (τ (M.op X0 (σ (M.op x y)))) x) ∨ (τ X0) = x ∨ (σ (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq9704 eq741481
    | (have j0 := eq741481 X0
       have j1 := eq9704 X0
       grind)
    | exact resolve eq741481 eq9704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9704 eq741481
  have eq868962 : x = (M.op (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) x) ∨ x = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq769452 (M.op sF1 sF1)
       have i₂ := eq236 sF1
       grind)
    | exact superpose eq236 eq769452
    | (have j0 := eq769452 (M.op (σ (M.op x y)) (σ (M.op x y)))
       grind)
    | exact resolve eq769452 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236 eq769452
  have eq869367 : x = (M.op (τ (M.op (σ x) (σ y))) x) ∨ x = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq30530 eq868962
    | exact resolve eq868962 eq30530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq868962
  have eq869438 : x = (τ (M.op (σ x) (σ y))) ∨ x = (M.op (τ (M.op (σ x) (σ y))) x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq30530 eq869367
    | exact resolve eq869367 eq30530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869367
  have eq869484 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (τ (M.op (σ x) (σ y))) ∨ x = (M.op (τ (M.op (σ x) (σ y))) x) := by
    first
    | exact superpose eq30530 eq869438
    | exact resolve eq869438 eq30530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869438
  have eq869517 : x = (M.op (τ (M.op (σ x) (σ y))) x) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq869484
       have r₂ := eq28
       grind)
    | exact resolve eq869484 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869484
  have eq948388 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (τ (M.op (σ (τ X0)) (σ (τ X0)))))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq35 X0 (τ (M.op (σ (τ X0)) (σ (τ X0))))
       have i₂ := eq141876 (τ X0)
       grind)
    | exact superpose eq141876 eq35
    | (have j1 := eq141876 (τ X0)
       grind)
    | exact resolve eq35 eq141876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq141876
  have eq948688 : ∀ X0 : G, (σ (τ X0)) = (k X0 (M.op (σ (τ X0)) (σ (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq948388 X0
       have i₂ := eq15 (M.op (σ (τ X0)) (σ (τ X0)))
       grind)
    | exact superpose eq15 eq948388
    | (have j0 := eq948388 X0
       grind)
    | exact resolve eq948388 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq948388
  have eq948962 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq948688 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq948688
    | (have j0 := eq948688 X0
       grind)
    | exact resolve eq948688 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq948688
  have eq949202 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq948962 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq948962
    | (have j0 := eq948962 X0
       grind)
    | exact resolve eq948962 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq948962
  have eq955886 : (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (σ y)))) = (k (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (σ y)))) (M.op (σ (M.op x y)) (M.op (σ x) (σ y)))) ∨ (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq131538 eq949202
    | exact resolve eq949202 eq131538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131538 eq949202
  have eq956338 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq30532 eq955886
    | exact resolve eq955886 eq30532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq955886
  have eq956476 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq30530 eq956338
    | exact resolve eq956338 eq30530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq956338
  have eq956581 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq30532 eq956476
    | exact resolve eq956476 eq30532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30532 eq956476
  have eq956635 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq30530 eq956581
    | exact resolve eq956581 eq30530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30530 eq956581
  have eq956669 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq956635
       have r₂ := eq28
       grind)
    | exact resolve eq956635 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq956635
  have eq1195616 : (σ x) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ x = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq869517 eq101090
    | (have j0 := eq101090 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq101090 eq869517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101090 eq869517
  have eq1195832 : (σ x) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ x = (τ (M.op (σ x) (σ y))) := by grind
  clear eq1195616
  have eq1195897 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq956669 eq1195832
    | exact resolve eq1195832 eq956669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq956669 eq1195832
  have eq1195978 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1195897
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1195897
    | exact resolve eq1195897 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1195897
  have eq1196051 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq30320 eq1195978
    | exact resolve eq1195978 eq30320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1195978
  have eq1196114 : x = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq1196051
       have r₂ := eq28
       grind)
    | exact resolve eq1196051 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1196051
  have eq1196421 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op x (τ (M.op (σ x) (σ y))))) x) ∨ x = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq1196114 eq18538
    | exact resolve eq18538 eq1196114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18538 eq1196114
  have eq1196825 : x = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1196421 x
       have i₂ := eq30219 x (τ sF4)
       grind)
    | exact superpose eq30219 eq1196421
    | exact resolve eq1196421 eq30219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30219 eq1196421
  have eq1196826 : x = (τ (M.op (σ x) (σ y))) := by grind
  clear eq1196825
  have eq1196937 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1196826 eq15
    | exact resolve eq15 eq1196826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1196826
  have eq1197280 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1196937
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1196937
    | exact resolve eq1196937 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1196937
  have eq1197360 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30320 eq1197280
    | exact resolve eq1197280 eq30320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30320 eq1197280
  have eq1197385 : False := by grind
  exact eq1197385

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_x_pxx_y_pyx_Equation1904 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1904 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
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
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq22
  have eq26 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
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
  have eq28 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq19
  have eq32 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq28 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq28
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq33 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq32
  have eq47 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq72 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq10
    | exact resolve eq10 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq77 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ (M.op X0 X0))) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1 (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq9
    | exact resolve eq9 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq26 (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq26
    | exact resolve eq26 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq47 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq47
    | (have j0 := eq47 X0 X1
       grind)
    | exact resolve eq47 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq140 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq130 y x
       grind)
    | exact superpose eq130 eq16
    | (have j1 := eq130 y x
       grind)
    | exact resolve eq16 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq156 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq26 (τ X0)
       have i₂ := eq72 X0
       grind)
    | exact superpose eq72 eq26
    | exact resolve eq26 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq308 : ∀ X0 X1 : G, (τ X0) = (M.op (M.op X1 (τ X0)) (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (τ X0) X1 (τ (M.op X0 X0))
       have i₂ := eq156 X0
       grind)
    | exact superpose eq156 eq9
    | exact resolve eq9 eq156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156
  have eq309 : ∀ X0 X1 : G, (τ X0) = (M.op (M.op X1 (τ X0)) (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq308 X0 X1
       have i₂ := eq72 X0
       grind)
    | exact superpose eq72 eq308
    | exact resolve eq308 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq308
  have eq322 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op (M.op X1 (τ (σ X0))) (τ (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq309 (σ X0) X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq309
    | exact resolve eq309 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309
  have eq327 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op (M.op X1 (τ (σ X0))) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq322 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq322
    | exact resolve eq322 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322
  have eq330 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq327 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq327
    | exact resolve eq327 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327
  have eq378 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X0 X0) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) X1 X2
       have i₂ := eq330 X0 X0
       grind)
    | exact superpose eq330 eq9
    | exact resolve eq9 eq330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq771 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq140
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq140
    | (have j1 := eq14 y x
       grind)
    | (have r₁ := eq140
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq140
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq140 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq772 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq771
  have eq780 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq378 X0 X1 (M.op X0 X0)
       have i₂ := eq330 X0 X0
       grind)
    | exact superpose eq330 eq378
    | exact resolve eq378 eq330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378
  have eq13955 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq772
       grind)
    | exact superpose eq772 eq16
    | exact resolve eq16 eq772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772
  have eq13956 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq13955
       have r₂ := eq23 x
       grind)
    | exact resolve eq13955 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13955
  have eq120027 : y = (τ (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq13956
       grind)
    | exact superpose eq13956 eq10
    | exact resolve eq10 eq13956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13956
  have eq120297 : x = y ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq120027
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq120027
    | exact resolve eq120027 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120027
  have eq120300 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq120297
       grind)
    | exact superpose eq120297 eq16
    | exact resolve eq16 eq120297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120297
  have eq120301 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq120300
       have r₂ := eq23 x
       grind)
    | exact resolve eq120300 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120300
  have eq121333 : x = (M.op y y) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq330 x x
       have i₂ := eq120301
       grind)
    | exact superpose eq120301 eq330
    | exact resolve eq330 eq120301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330 eq120301
  have eq122907 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (σ x)) ∨ (σ y) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq77 y x
       have i₂ := eq121333
       grind)
    | exact superpose eq121333 eq77
    | exact resolve eq77 eq121333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq121333
  have eq123184 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq122907 x
       have i₂ := eq780 (σ x) x
       grind)
    | exact superpose eq780 eq122907
    | exact resolve eq122907 eq780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780 eq122907
  have eq123186 : (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq123184
       have i₂ := eq23 x
       grind)
    | exact superpose eq23 eq123184
    | exact resolve eq123184 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq123184
  have eq123187 : (σ y) = (σ (M.op x x)) := by grind
  clear eq123186
  have eq124018 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq78 x
       have i₂ := eq123187
       grind)
    | exact superpose eq123187 eq78
    | exact resolve eq78 eq123187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq124077 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq123187
       grind)
    | exact superpose eq123187 eq10
    | exact resolve eq10 eq123187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123187
  have eq124434 : y = (M.op x x) := by
    first
    | (have i₁ := eq124077
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq124077
    | exact resolve eq124077 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124077
  have eq125260 : x = (M.op x y) := by
    first
    | (have i₁ := eq26 x
       have i₂ := eq124434
       grind)
    | exact superpose eq124434 eq26
    | exact resolve eq26 eq124434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq124434
  have eq153619 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq124018
       grind)
    | exact superpose eq124018 eq16
    | exact resolve eq16 eq124018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124018
  have eq153856 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq153619
       have i₂ := eq125260
       grind)
    | exact superpose eq125260 eq153619
    | exact resolve eq153619 eq125260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125260 eq153619
  have eq153857 : False := by grind
  exact eq153857

/-- `Equation1924`: `x = (y ◇ (y ◇ x)) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pxy_pyx_pxy_Equation1924 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1924 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1924.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
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
  have eq54 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq54 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq54 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq54 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq55 (σ X0)
       grind)
    | exact superpose eq55 eq15
    | exact resolve eq15 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq57 X0
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq57
    | exact resolve eq57 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq57
  have eq80 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq66
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
    | (have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq86 X0 X1
       have i₂ := eq66 X1
       grind)
    | exact superpose eq66 eq86
    | (have j0 := eq86 X0 X1
       grind)
    | exact resolve eq86 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq86
  have eq186 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
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
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq92 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq92 X0 X1
       grind)
    | exact resolve eq13 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq189 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq186 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq193 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq189 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq189 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq189 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq203 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq193 X0 X1
       have j1 := eq80 X1 (σ X0)
       grind)
    | (have r₁ := eq193 X0 X0
       have r₂ := eq80 X0 X1
       grind)
    | exact resolve eq193 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq193
  have eq211 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq203 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq203
    | (have j0 := eq203 X0 X1
       grind)
    | exact resolve eq203 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq212 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq211 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq218 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq212 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq212
    | exact resolve eq212 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq229 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq212 x y
       grind)
    | exact superpose eq212 eq16
    | exact resolve eq16 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq276 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq218 X0 (τ X1)
       grind)
    | exact superpose eq218 eq18
    | exact resolve eq18 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq218
  have eq293 : ∀ X0 X1 : G, (M.op X0 X1) = (k (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq276 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq276
    | exact resolve eq276 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq301 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq293 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq293
    | exact resolve eq293 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293
  have eq321 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq229
       have i₂ := eq301 x y
       grind)
    | exact superpose eq301 eq229
    | exact resolve eq229 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229 eq301
  have eq322 : False := by grind
  exact eq322

/-- `Equation1924`: `x = (y ◇ (y ◇ x)) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,X) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pxy_pxx_pxy_Equation1924 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1924 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1924.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X1 X0)) (M.op X1 X0)) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X1 := by
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
  have eq58 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq53 (τ X0)
       grind)
    | exact superpose eq53 eq18
    | exact resolve eq18 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq61 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq58 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq58
    | exact resolve eq58 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
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
  clear eq55
  have eq67 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq61 X0
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq61
    | exact resolve eq61 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq61
  have eq76 : ∀ X0 : G, (σ X0) = (M.op (M.op (σ X0) (σ (M.op X0 X0))) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq9 (σ X0) (σ X0)
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq9
    | exact resolve eq9 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq88 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq82 X0 X1
       have i₂ := eq64 X1
       grind)
    | exact superpose eq64 eq82
    | (have j0 := eq82 X0 X1
       grind)
    | exact resolve eq82 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq91 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq88 X0 X1
       have i₂ := eq64 X1
       grind)
    | exact superpose eq64 eq88
    | (have j0 := eq88 X0 X1
       grind)
    | exact resolve eq88 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq170 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq91 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq91
    | (have j0 := eq91 X0 X1
       grind)
    | exact resolve eq91 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq193 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq170 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq170
    | (have j0 := eq170 X0 X1
       grind)
    | exact resolve eq170 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170
  have eq200 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq193 X0 X1
       have j1 := eq78 X1 X0
       grind)
    | (have r₁ := eq193 X0 X0
       have r₂ := eq78 X0 X1
       grind)
    | exact resolve eq193 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq193
  have eq518 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq200 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq200
    | exact resolve eq200 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq530 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq200 (σ X0) X1
       grind)
    | exact superpose eq200 eq15
    | (have j1 := eq200 (σ X0) X1
       grind)
    | exact resolve eq15 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq551 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq518 X0 X1
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq518
    | (have j0 := eq518 X0 X1
       grind)
    | exact resolve eq518 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq518
  have eq575 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq551 X1 (τ X0)
       grind)
    | exact superpose eq551 eq17
    | (have j1 := eq551 X1 (τ X0)
       grind)
    | exact resolve eq17 eq551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq551
  have eq929 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq575 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq575
    | exact resolve eq575 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575
  have eq975 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq929 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq929
    | (have j0 := eq929 X0 X1
       grind)
    | exact resolve eq929 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq929
  have eq3795 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq530 x y
       grind)
    | exact superpose eq530 eq16
    | (have j1 := eq530 x y
       grind)
    | exact resolve eq16 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530
  have eq3989 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq3795
       have i₂ := eq975 x y
       grind)
    | exact superpose eq975 eq3795
    | (have j1 := eq975 x y
       grind)
    | (have r₁ := eq3795
       have r₂ := eq975 x y
       grind)
    | exact resolve eq3795 eq975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq975 eq3795
  have eq3990 : (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (M.op y y) = (M.op y x) := by grind
  clear eq3989
  have eq4003 : (σ x) = (M.op (M.op (σ y) (σ (M.op y y))) (σ (M.op y y))) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq9 (σ x) (σ y)
       have i₂ := eq3990
       grind)
    | exact superpose eq3990 eq9
    | exact resolve eq9 eq3990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3990
  have eq4004 : (M.op y y) = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4003
       have i₂ := eq76 y
       grind)
    | exact superpose eq76 eq4003
    | exact resolve eq4003 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq4003
  have eq4061 : y = (M.op (M.op y (M.op y x)) (M.op y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9 y y
       have i₂ := eq4004
       grind)
    | exact superpose eq4004 eq9
    | exact resolve eq9 eq4004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4004
  have eq4063 : x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4061
       have i₂ := eq9 x y
       grind)
    | exact superpose eq9 eq4061
    | exact resolve eq4061 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4061
  have eq4067 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4063
       grind)
    | exact superpose eq4063 eq16
    | exact resolve eq16 eq4063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4063
  have eq4068 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq4067
       have r₂ := eq64 x
       grind)
    | exact resolve eq4067 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4067
  have eq4169 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4068
       grind)
    | exact superpose eq4068 eq16
    | exact resolve eq16 eq4068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4170 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq4068
       grind)
    | exact superpose eq4068 eq10
    | exact resolve eq10 eq4068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4068
  have eq4222 : x = y := by
    first
    | (have i₁ := eq4170
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq4170
    | exact resolve eq4170 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4170
  have eq4223 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq4169
       have i₂ := eq64 x
       grind)
    | exact superpose eq64 eq4169
    | exact resolve eq4169 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq4169
  have eq4225 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq4223
       have i₂ := eq4222
       grind)
    | exact superpose eq4222 eq4223
    | exact resolve eq4223 eq4222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4222 eq4223
  have eq4226 : False := by grind
  exact eq4226
