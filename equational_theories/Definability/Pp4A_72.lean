import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation964`: `x = y ◇ ((z ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_y_pxx_pxy_pyx_Equation964 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law964 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law964.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
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
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
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
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq22
  have eq26 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq19
  have eq30 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq26 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq26
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq31 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq30
  have eq58 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq31 X0
       grind)
    | exact superpose eq31 eq10
    | exact resolve eq10 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq91 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq9
    | exact resolve eq9 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) (M.op X2 X1)) = (M.op X2 (M.op (M.op X3 X2) X1)) := by
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
  have eq101 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq91 X0 (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq91
    | exact resolve eq91 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1)) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq91 X0 (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1))
       have i₂ := eq91 X0 X1
       grind)
    | exact superpose eq91 eq91
    | exact resolve eq91 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq101 X0
       have i₂ := eq23 (M.op X0 X0)
       grind)
    | exact superpose eq23 eq101
    | exact resolve eq101 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq114 : ∀ X0 : G, (σ (σ X0)) = (M.op (σ (σ X0)) (σ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq106 (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq106
    | exact resolve eq106 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : ∀ X0 : G, (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ (M.op (M.op X0 X0) (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq114 X0
       have i₂ := eq23 (M.op X0 X0)
       grind)
    | exact superpose eq23 eq114
    | exact resolve eq114 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq124 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq130 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op (τ X1) X0)) ∨ (M.op X0 X0) = (τ X1) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq20
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq20 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq139 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq124 X0 X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq124
    | (have j0 := eq124 X0 X1
       grind)
    | exact resolve eq124 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq188 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (σ X0)) X1) = (M.op (σ X0) (M.op (M.op X3 (σ X0)) (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq96 X2 (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1)) (σ X0) X3
       have i₂ := eq91 X0 X1
       grind)
    | exact superpose eq91 eq96
    | exact resolve eq96 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq210 : ∀ X0 X2 X3 : G, (M.op X0 (M.op X0 (M.op (M.op X3 X0) X2))) = X2 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq9 X2 X0 x
       have i₂ := eq96 x X2 X0 X3
       grind)
    | exact superpose eq96 eq9
    | exact resolve eq9 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq212 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 (M.op (M.op X1 X0) X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq106 X0
       have i₂ := eq96 X0 X0 X0 X1
       grind)
    | exact superpose eq96 eq106
    | exact resolve eq106 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq220 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X0 x
       have i₂ := eq96 X1 (M.op X0 X2) X0 x
       grind)
    | exact superpose eq96 eq9
    | exact resolve eq9 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq229 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (σ X0)) X1) = (M.op (σ X0) (M.op (M.op X3 (σ X0)) (M.op (σ X0) (M.op (σ (M.op X0 X0)) X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq188 X0 X1 X2 X3
       have i₂ := eq102 X0 X1
       grind)
    | exact superpose eq102 eq188
    | exact resolve eq188 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq188
  have eq233 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 X0)) X1) = (M.op (M.op X2 (σ X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq229 X0 X1 X2 x
       have i₂ := eq9 (M.op (σ (M.op X0 X0)) X1) (σ X0) x
       grind)
    | exact superpose eq9 eq229
    | exact resolve eq229 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq248 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) (M.op (M.op X3 (M.op X1 X2)) X0)) = (M.op X2 (M.op X2 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq210 X2 (M.op (M.op X1 X2) (M.op (M.op X3 (M.op X1 X2)) X0)) X1
       have i₂ := eq210 (M.op X1 X2) X0 X3
       grind)
    | exact superpose eq210 eq210
    | exact resolve eq210 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq252 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op (M.op X4 X1) (M.op X1 (M.op (M.op X2 X1) X0)))) = (M.op (M.op X3 X1) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq96 X3 (M.op X1 (M.op (M.op X2 X1) X0)) X1 X4
       have i₂ := eq210 X1 X0 X2
       grind)
    | exact superpose eq210 eq96
    | exact resolve eq96 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq259 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) X0) = (M.op (M.op X3 X1) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq252 X0 X1 X2 X3 x
       have i₂ := eq9 (M.op (M.op X2 X1) X0) X1 x
       grind)
    | exact superpose eq9 eq252
    | exact resolve eq252 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252
  have eq384 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ (M.op (M.op X0 X1) (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq106 X1
       have i₂ := eq259 (M.op X1 X1) X1 X1 X0
       grind)
    | (have i₁ := eq106 X1
       have i₂ := eq259 (M.op X1 X1) X1 X0 X1
       grind)
    | exact superpose eq259 eq106
    | exact resolve eq106 eq259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq389 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 (M.op X3 X2)) (M.op (M.op X0 X2) X1)) = (M.op (M.op X3 X2) (M.op (M.op X5 (M.op X3 X2)) X1)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq96 X4 X1 (M.op X3 X2) X5
       have i₂ := eq259 X1 X2 X3 X0
       grind)
    | (have i₁ := eq96 X4 X1 (M.op X3 X2) X5
       have i₂ := eq259 X1 X2 X0 X3
       grind)
    | exact superpose eq259 eq96
    | exact resolve eq96 eq259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq409 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X2 X1)) = (M.op (M.op X4 (M.op X3 X2)) (M.op (M.op X0 X2) X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq389 X0 X1 X2 X3 X4 x
       have i₂ := eq248 X1 X3 X2 x
       grind)
    | exact superpose eq248 eq389
    | exact resolve eq389 eq248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248 eq389
  have eq812 : ∀ X0 X1 X2 X3 : G, (M.op (σ X0) X3) = (M.op (M.op X2 (σ (M.op X0 (M.op (M.op X1 X0) X0)))) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq259 X3 (σ (M.op X0 (M.op (M.op X1 X0) X0))) X2 (σ X0)
       have i₂ := eq212 X0 X1
       grind)
    | exact superpose eq212 eq259
    | exact resolve eq259 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq929 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (σ (M.op (M.op X1 (τ X0)) (τ (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq384 X1 (τ X0)
       have i₂ := eq58 X0
       grind)
    | exact superpose eq58 eq384
    | exact resolve eq384 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384
  have eq959 : ∀ X0 X1 : G, (M.op X0 (σ (M.op (M.op X1 (τ X0)) (τ (M.op X0 X0))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq929 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq929
    | exact resolve eq929 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq929
  have eq1030 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op X0 X1))) = (σ (M.op (M.op X2 (τ (M.op X0 X1))) (τ (M.op (M.op X0 X1) (M.op X0 X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq210 X1 (σ (M.op (M.op X2 (τ (M.op X0 X1))) (τ (M.op (M.op X0 X1) (M.op X0 X1))))) X0
       have i₂ := eq959 (M.op X0 X1) X2
       grind)
    | exact superpose eq959 eq210
    | exact resolve eq210 eq959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq959
  have eq8397 : ∀ X0 X1 : G, (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ (M.op (M.op X1 X0) (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq120 X0
       have i₂ := eq259 (M.op X0 X0) X0 X0 X1
       grind)
    | (have i₁ := eq120 X0
       have i₂ := eq259 (M.op X0 X0) X0 X1 X0
       grind)
    | exact superpose eq259 eq120
    | exact resolve eq120 eq259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq259
  have eq14739 : ∀ X1 X2 X3 X4 : G, (M.op (σ (M.op (M.op X1 X2) X2)) X3) = (M.op (M.op X4 (σ (M.op (M.op (M.op X1 X2) X2) (M.op X2 (M.op X2 X2))))) X3) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq812 (M.op (M.op X1 X2) X2) x X4 X3
       have i₂ := eq409 X1 X2 X2 (M.op X1 X2) x
       grind)
    | exact superpose eq409 eq812
    | exact resolve eq812 eq409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409 eq812
  have eq14965 : ∀ X1 X2 X3 X4 : G, (M.op (σ (M.op (M.op X1 X2) X2)) X3) = (M.op (M.op X4 (σ X2)) X3) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq14739 X1 X2 X3 X4
       have i₂ := eq220 X2 (M.op X1 X2) X2
       grind)
    | exact superpose eq220 eq14739
    | exact resolve eq14739 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220 eq14739
  have eq15342 : ∀ X0 X2 X3 : G, (M.op (σ (M.op X0 X0)) X3) = (M.op (σ (M.op (M.op X2 X0) X0)) X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq233 X0 X3 x
       have i₂ := eq14965 X2 X0 X3 x
       grind)
    | exact superpose eq14965 eq233
    | exact resolve eq233 eq14965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233 eq14965
  have eq24825 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq139 X0 X1
       grind)
    | (have i₁ := eq10 X1
       have i₂ := eq139 X0 X1
       grind)
    | exact superpose eq139 eq10
    | (have j1 := eq139 X0 X1
       grind)
    | exact resolve eq10 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq24884 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op X0 X0) = X1 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq24825 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq24825
    | (have j0 := eq24825 X0 X1
       grind)
    | exact resolve eq24825 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24825
  have eq24937 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ (σ (M.op (M.op X1 (τ X0)) (M.op (τ X0) (τ X0)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq8397 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq8397
    | exact resolve eq8397 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8397
  have eq25175 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ (σ (M.op (M.op X1 (τ X0)) (τ (M.op X0 X0)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq24937 X0 X1
       have i₂ := eq58 X0
       grind)
    | exact superpose eq58 eq24937
    | exact resolve eq24937 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq24937
  have eq30736 : ∀ X0 X1 X2 : G, (σ (M.op (M.op X0 X1) X1)) = (M.op (σ (M.op X1 X1)) (σ (σ (M.op (M.op X2 (τ (M.op (M.op X0 X1) X1))) (τ (M.op (M.op (M.op X0 X1) X1) (M.op (M.op X0 X1) X1))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15342 X1 X0 (σ (σ (M.op (M.op X2 (τ (M.op (M.op X0 X1) X1))) (τ (M.op (M.op (M.op X0 X1) X1) (M.op (M.op X0 X1) X1))))))
       have i₂ := eq25175 (M.op (M.op X0 X1) X1) X2
       grind)
    | exact superpose eq25175 eq15342
    | exact resolve eq15342 eq25175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15342 eq25175
  have eq30809 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X1) X1)) = (M.op (σ (M.op X1 X1)) (σ (M.op X1 (M.op X1 (M.op (M.op X0 X1) X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq30736 X0 X1 x
       have i₂ := eq1030 (M.op X0 X1) X1 x
       grind)
    | exact superpose eq1030 eq30736
    | exact resolve eq30736 eq1030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1030 eq30736
  have eq30859 : ∀ X0 X1 : G, (M.op (σ (M.op X1 X1)) (σ X1)) = (σ (M.op (M.op X0 X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq30809 X0 X1
       have i₂ := eq210 X1 X1 X0
       grind)
    | exact superpose eq210 eq30809
    | exact resolve eq30809 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210 eq30809
  have eq99406 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq130 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq130
    | exact resolve eq130 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq100112 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq99406 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq99406
    | (have j0 := eq99406 X0 X1
       grind)
    | exact resolve eq99406 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99406
  have eq143403 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24884 y x
       grind)
    | exact superpose eq24884 eq16
    | (have j1 := eq24884 y x
       grind)
    | exact resolve eq16 eq24884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24884
  have eq437146 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq143403
       have i₂ := eq100112 x y
       grind)
    | exact superpose eq100112 eq143403
    | (have j1 := eq100112 x y
       grind)
    | (have r₁ := eq143403
       have r₂ := eq100112 x y
       grind)
    | (have r₁ := eq143403
       have r₂ := eq100112 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq143403
       have r₂ := eq100112 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq143403 eq100112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100112 eq143403
  have eq437148 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq437146
  have eq437149 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq437148
  have eq437402 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq30859 y y
       have i₂ := eq437149
       grind)
    | exact superpose eq437149 eq30859
    | exact resolve eq30859 eq437149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30859 eq437149
  have eq442342 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq437402
       grind)
    | exact superpose eq437402 eq16
    | (have r₁ := eq16
       have r₂ := eq437402
       grind)
    | exact resolve eq16 eq437402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437402
  have eq442538 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq442342
  have eq442610 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq442538
       grind)
    | exact superpose eq442538 eq10
    | exact resolve eq10 eq442538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442538
  have eq442808 : x = y ∨ x = y := by
    first
    | (have i₁ := eq442610
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq442610
    | exact resolve eq442610 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442610
  have eq442809 : x = y := by grind
  clear eq442808
  have eq443686 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq442809
       grind)
    | exact superpose eq442809 eq16
    | exact resolve eq16 eq442809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442809
  have eq443687 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq443686
       have i₂ := eq23 x
       grind)
    | exact superpose eq23 eq443686
    | (have r₁ := eq443686
       have r₂ := eq23 x
       grind)
    | exact resolve eq443686 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq443686
  have eq443688 : False := by grind
  exact eq443688
