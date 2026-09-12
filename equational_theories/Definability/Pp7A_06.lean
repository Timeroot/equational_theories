import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1473`: `x = (x ◇ y) ◇ (z ◇ (w ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,Y) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyx_pyy_pxy_pyx_Equation1473 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1473 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1473.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
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
  have eq31 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq51 : ∀ X0 X1 X4 X5 : G, (M.op X0 X1) = (M.op X0 (M.op X4 (M.op X5 (M.op X0 X1)))) := by
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
  have eq52 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op (M.op X1 (M.op X2 X0)) X3) (M.op X4 X0)) := by
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
  have eq53 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 X0) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 (M.op X0 x) x
       have i₂ := eq9 X0 x x X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X0)) = (M.op X1 (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq51 X1 (M.op X2 X0) X3 (M.op X0 x)
       have i₂ := eq9 X0 x X1 X2
       grind)
    | exact superpose eq9 eq51
    | exact resolve eq51 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 X3 X4 X5 : G, (M.op X1 X0) = (M.op X1 (M.op X5 (M.op X3 (M.op X4 X0)))) := by
    intro X0 X1 X3 X4 X5
    first
    | (have i₁ := eq74 (M.op X3 (M.op X4 X0)) X1 (M.op X0 x) X5
       have i₂ := eq9 X0 x X3 X4
       grind)
    | exact superpose eq9 eq74
    | exact resolve eq74 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq136 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq136 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq136 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq140 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq137 (σ X0)
       grind)
    | exact superpose eq137 eq15
    | exact resolve eq15 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq144 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq137 (τ X0)
       grind)
    | exact superpose eq137 eq18
    | exact resolve eq18 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq147 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq144 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq144
    | exact resolve eq144 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq151 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq140 X0
       have i₂ := eq137 X0
       grind)
    | exact superpose eq137 eq140
    | exact resolve eq140 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq155 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq147 X0
       have i₂ := eq137 X0
       grind)
    | exact superpose eq137 eq147
    | exact resolve eq147 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137 eq147
  have eq161 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op X1 (M.op X2 (σ X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) (σ X0) X1 X2
       have i₂ := eq151 X0
       grind)
    | exact superpose eq151 eq9
    | exact resolve eq9 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq162 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op (σ X0) X1) (M.op X2 (σ (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X1 X2 (σ X0)
       have i₂ := eq151 X0
       grind)
    | exact superpose eq151 eq9
    | exact resolve eq9 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq167 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (σ X0) (σ X0) x
       have i₂ := eq151 X0
       grind)
    | exact superpose eq151 eq53
    | exact resolve eq53 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq168 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (σ X0))) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq74 (σ X0) X1 X2 (σ X0)
       have i₂ := eq151 X0
       grind)
    | exact superpose eq151 eq74
    | exact resolve eq74 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq155 X0
       grind)
    | exact superpose eq155 eq10
    | exact resolve eq10 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq199 : ∀ X0 X1 X2 : G, (τ X0) = (M.op (M.op (τ X0) X1) (M.op X2 (τ (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (τ X0) X1 X2 (τ X0)
       have i₂ := eq183 X0
       grind)
    | exact superpose eq183 eq9
    | exact resolve eq9 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq204 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op (M.op (τ (M.op X0 X0)) X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (τ X0) (τ X0) x
       have i₂ := eq183 X0
       grind)
    | exact superpose eq183 eq53
    | exact resolve eq53 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq183
  have eq219 : ∀ X0 X1 X2 X3 : G, (M.op X1 (σ X0)) = (M.op X1 (M.op X2 (M.op X3 (σ (M.op X0 X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq84 (σ X0) X1 X3 (σ X0) X2
       have i₂ := eq151 X0
       grind)
    | exact superpose eq151 eq84
    | exact resolve eq84 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq242 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = (k (M.op X2 (M.op X3 (M.op X4 X1))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq12 (M.op X2 (M.op X3 (M.op X4 X1))) X0
       have i₂ := eq84 X1 X0 X3 X4 X2
       grind)
    | exact superpose eq84 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | exact resolve eq12 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq363 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X0 (σ (M.op X1 X1)))) = (M.op X2 (M.op X3 (M.op X4 (σ X1)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq74 (M.op X4 (σ X1)) X2 X3 X0
       have i₂ := eq168 X1 X0 X4
       grind)
    | exact superpose eq168 eq74
    | exact resolve eq74 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq501 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op X1 (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq161 X0 X1 (σ X0)
       have i₂ := eq151 X0
       grind)
    | exact superpose eq151 eq161
    | exact resolve eq161 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161
  have eq572 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ X0) X1) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq162 X0 X1 (σ (M.op X0 X0))
       have i₂ := eq151 (M.op X0 X0)
       grind)
    | exact superpose eq151 eq162
    | exact resolve eq162 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162
  have eq618 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op (σ X0) X2) (σ (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq167 (M.op X2 (M.op x X2)) X1
       have i₂ := eq9 X2 (M.op x X2) X2 x
       grind)
    | exact superpose eq9 eq167
    | exact resolve eq167 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq765 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (σ (M.op (τ X0) (τ (M.op X0 X0)))))) = (M.op X1 (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq168 (M.op (τ X0) (τ (M.op X0 X0))) X1 X2
       have i₂ := eq199 X0 (τ (M.op X0 X0)) (τ X0)
       grind)
    | exact superpose eq199 eq168
    | exact resolve eq168 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq782 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 (M.op X2 (σ (M.op (τ X0) (τ (M.op X0 X0)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq765 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq765
    | exact resolve eq765 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765
  have eq830 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq185 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq185 X0 X1
       grind)
    | exact superpose eq185 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq185 X1 X0
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq185 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq185 X0 X1
       grind)
    | exact resolve eq13 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq843 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq830 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830
  have eq844 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq843 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843
  have eq850 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq844 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq844
    | (have j0 := eq844 X0 X1
       grind)
    | exact resolve eq844 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844
  have eq851 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq850 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850
  have eq876 : ∀ X0 X1 X2 : G, (τ X0) = (M.op (M.op (τ X0) X2) (τ (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq204 (M.op X2 (M.op x X2)) X1
       have i₂ := eq9 X2 (M.op x X2) X2 x
       grind)
    | exact superpose eq9 eq204
    | exact resolve eq204 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq927 : ∀ X0 X1 X2 : G, (σ (M.op X0 (M.op X1 X0))) = (M.op (σ X0) (M.op X2 (σ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq501 (M.op X2 (M.op x X2)) X1
       have i₂ := eq9 X2 (M.op x X2) X2 x
       grind)
    | exact superpose eq9 eq501
    | exact resolve eq501 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq930 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ (M.op X0 X0)))) = (M.op (σ (τ X0)) (M.op X1 (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq501 (M.op (τ X0) (τ (M.op X0 X0))) X1
       have i₂ := eq199 X0 (τ (M.op X0 X0)) (τ X0)
       grind)
    | exact superpose eq199 eq501
    | exact resolve eq501 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq968 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq930 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq930
    | exact resolve eq930 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq930
  have eq975 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq618 X0 X1 (σ X0)
       have i₂ := eq151 X0
       grind)
    | exact superpose eq151 eq618
    | exact resolve eq618 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1260 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (τ (M.op (σ X0) (M.op X2 (σ X0))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq876 (σ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq876
    | exact resolve eq876 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq876
  have eq1575 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X0)) = (τ (M.op (σ X0) (M.op X1 (σ X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (M.op X0 (M.op X2 X0))
       have i₂ := eq927 X0 X2 X1
       grind)
    | exact superpose eq927 eq10
    | exact resolve eq10 eq927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1917 : ∀ X0 X1 : G, (τ (M.op X0 (M.op X1 X0))) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ (M.op X0 X0)))
       have i₂ := eq968 X0 X1
       grind)
    | exact superpose eq968 eq10
    | exact resolve eq10 eq968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq968
  have eq4303 : ∀ X0 X1 X2 : G, (M.op (τ (σ (M.op X0 X0))) (τ (M.op (σ (M.op X0 X0)) (M.op X1 (σ X0))))) = (τ (M.op (σ (M.op X0 X0)) (M.op X2 (σ (M.op X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1917 (σ (M.op X0 X0)) X2
       have i₂ := eq168 X0 (σ (M.op X0 X0)) X1
       grind)
    | exact superpose eq168 eq1917
    | exact resolve eq1917 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1917
  have eq4426 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op (τ (σ (M.op X0 X0))) (τ (M.op (σ (M.op X0 X0)) (M.op X1 (σ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq4303 X0 X1 x
       have i₂ := eq501 X0 x
       grind)
    | exact superpose eq501 eq4303
    | exact resolve eq4303 eq501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4303
  have eq4472 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op (M.op X0 X0) (τ (M.op (σ (M.op X0 X0)) (M.op X1 (σ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq4426 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq4426
    | exact resolve eq4426 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4426
  have eq4500 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (τ (M.op (σ (M.op X0 X0)) (M.op X1 (σ X0))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4472 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4472
    | exact resolve eq4472 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4472
  have eq4523 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq851 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq851
    | exact resolve eq851 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4557 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq851 x y
       grind)
    | exact superpose eq851 eq16
    | (have j1 := eq851 x y
       grind)
    | exact resolve eq16 eq851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4598 : ∀ X0 X1 X2 X3 : G, (σ (k X0 X1)) = (M.op (σ X1) (M.op X2 (M.op X3 (σ (k X0 X1))))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq51 (σ X0) (σ X1) x x
       have i₂ := eq851 X0 X1
       grind)
    | exact superpose eq851 eq51
    | (have j1 := eq851 X1 X0
       grind)
    | exact resolve eq51 eq851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4603 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (σ X0))) = (M.op X2 (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq74 (σ X0) X2 X3 (σ X1)
       have i₂ := eq851 X1 X0
       grind)
    | exact superpose eq851 eq74
    | (have j1 := eq851 X1 X0
       grind)
    | exact resolve eq74 eq851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4606 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (σ X0)) = (M.op X2 (M.op X3 (M.op X4 (σ (k X0 X1))))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq84 (σ X0) X2 X4 (σ X1) X3
       have i₂ := eq851 X1 X0
       grind)
    | exact superpose eq851 eq84
    | (have j1 := eq851 X1 X0
       grind)
    | exact resolve eq84 eq851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4631 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq851 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851
  have eq4677 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4523 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq4523
    | (have j0 := eq4523 X0 X1
       grind)
    | exact resolve eq4523 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq4523
  have eq6070 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4631 (τ X1) (τ X0)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq4631
    | (have j0 := eq4631 (τ X1) (τ X0)
       grind)
    | exact resolve eq4631 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6086 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq6070 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq6070
    | (have j0 := eq6070 X0 X1
       grind)
    | exact resolve eq6070 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6070
  have eq6090 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq6086 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq6086
    | (have j0 := eq6086 X0 X1
       grind)
    | exact resolve eq6086 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6086
  have eq6091 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6090 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6090
    | (have j0 := eq6090 X0 X1
       grind)
    | exact resolve eq6090 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6090
  have eq6092 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6091 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6091
    | (have j0 := eq6091 X0 X1
       grind)
    | exact resolve eq6091 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6091
  have eq6098 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4677 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4677
    | exact resolve eq4677 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6118 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 X0
       have i₂ := eq4677 X0 X1
       grind)
    | exact superpose eq4677 eq28
    | (have j1 := eq4677 X0 X1
       grind)
    | exact resolve eq28 eq4677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq4677
  have eq6157 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq6098 (τ X1) X0
       grind)
    | exact superpose eq6098 eq17
    | (have j1 := eq6098 (τ X1) X0
       grind)
    | exact resolve eq17 eq6098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq9016 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6118 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6118
    | exact resolve eq6118 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6118
  have eq9112 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9016 X0 X1
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq9016
    | (have j0 := eq9016 X0 X1
       grind)
    | exact resolve eq9016 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9016
  have eq9152 : ∀ X0 X1 X2 : G, (τ (k X2 (k X1 X0))) = (k (τ X2) (τ (M.op X0 X1))) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31 (k X1 X0) X2
       have i₂ := eq9112 X1 X0
       grind)
    | exact superpose eq9112 eq31
    | (have j1 := eq9112 X1 X0
       grind)
    | exact resolve eq31 eq9112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9112
  have eq9173 : ∀ X0 X1 X2 : G, (τ (k X2 (k X1 X0))) = (τ (k X2 (M.op X0 X1))) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9152 X0 X1 X2
       have i₂ := eq31 (M.op X0 X1) X2
       grind)
    | exact superpose eq31 eq9152
    | (have j0 := eq9152 X0 X1 X2
       grind)
    | exact resolve eq9152 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9152
  have eq11416 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6157 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6157
    | exact resolve eq6157 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6157
  have eq11538 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11416 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq11416
    | (have j0 := eq11416 X0 X1
       grind)
    | exact resolve eq11416 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11416
  have eq29701 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4557
       have i₂ := eq6098 y x
       grind)
    | exact superpose eq6098 eq4557
    | (have j1 := eq6098 (σ y) (σ x)
       grind)
    | exact resolve eq4557 eq6098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4557
  have eq29706 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq29701
  have eq29708 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq29706
       grind)
    | exact superpose eq29706 eq16
    | exact resolve eq16 eq29706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29712 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ (M.op x (M.op X0 x)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq618 x X0 (σ y)
       have i₂ := eq29706
       grind)
    | exact superpose eq29706 eq618
    | exact resolve eq618 eq29706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618
  have eq29719 : ∀ X0 : G, (M.op y (M.op X0 y)) = (τ (M.op (σ y) (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1575 y (σ x) X0
       have i₂ := eq29706
       grind)
    | exact superpose eq29706 eq1575
    | exact resolve eq1575 eq29706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29728 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq29706
       grind)
    | exact superpose eq29706 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq29706
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq29706
       grind)
    | exact resolve eq12 eq29706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29706
  have eq29808 : (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq29728
  have eq29836 : (σ (M.op x x)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq29808
       have i₂ := eq151 x
       grind)
    | exact superpose eq151 eq29808
    | exact resolve eq29808 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29808
  have eq29846 : (σ (k y x)) = (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq29836
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq29836
    | exact resolve eq29836 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29836
  have eq29858 : (σ (M.op x y)) = (σ (M.op x x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11538 y x
       have i₂ := eq29846
       grind)
    | exact superpose eq29846 eq11538
    | (have j0 := eq11538 y x
       grind)
    | exact resolve eq11538 eq29846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11538
  have eq29860 : (k y x) = (τ (σ (M.op x x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq29846
       grind)
    | exact superpose eq29846 eq10
    | exact resolve eq10 eq29846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29846
  have eq29906 : (σ (M.op x y)) = (σ (M.op x x)) ∨ x = (M.op x y) := by grind
  clear eq29858
  have eq29927 : (k y x) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq29860
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq29860
    | exact resolve eq29860 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29860
  have eq29932 : (k y x) = (M.op x x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq29927
       have r₂ := eq12 y x
       grind)
    | exact resolve eq29927 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29927
  have eq29933 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq29932
       have i₂ := eq6098 y x
       grind)
    | exact superpose eq6098 eq29932
    | (have j1 := eq6098 y x
       grind)
    | exact resolve eq29932 eq6098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6098
  have eq29937 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4631 x y
       have i₂ := eq29932
       grind)
    | exact superpose eq29932 eq4631
    | (have j0 := eq4631 x y
       grind)
    | exact resolve eq4631 eq29932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4631
  have eq29938 : x ≠ (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6092 y x
       have i₂ := eq29932
       grind)
    | exact superpose eq29932 eq6092
    | (have j0 := eq6092 y x
       grind)
    | exact resolve eq6092 eq29932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6092
  have eq29943 : (σ x) ≠ (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq29708
       have i₂ := eq29933
       grind)
    | exact superpose eq29933 eq29708
    | exact resolve eq29708 eq29933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29708 eq29933
  have eq30027 : (σ x) ≠ (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq29943
       have r₂ := eq29938
       grind)
    | exact resolve eq29943 eq29938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29938 eq29943
  have eq30240 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op (M.op x y) X0) (τ (M.op (σ (M.op x x)) (M.op X1 (σ (M.op x x)))))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq1260 (M.op x y) X1 x
       have i₂ := eq29906
       grind)
    | exact superpose eq29906 eq1260
    | exact resolve eq1260 eq29906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1260
  have eq30242 : ∀ X0 X1 : G, (τ (M.op (σ (M.op x x)) (M.op X1 (σ (M.op x x))))) = (M.op (M.op x y) (M.op X0 (M.op x y))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq1575 (M.op x y) X1 x
       have i₂ := eq29906
       grind)
    | exact superpose eq29906 eq1575
    | exact resolve eq1575 eq29906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1575 eq29906
  have eq30263 : ∀ X0 : G, (τ (σ x)) = (M.op (M.op x y) (M.op X0 (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq30242 X0 x
       have i₂ := eq501 x x
       grind)
    | exact superpose eq501 eq30242
    | exact resolve eq30242 eq501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30242
  have eq30264 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) X0) (τ (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq30240 X0 x
       have i₂ := eq501 x x
       grind)
    | exact superpose eq501 eq30240
    | exact resolve eq30240 eq501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501 eq30240
  have eq30279 : ∀ X0 : G, x = (M.op (M.op x y) (M.op X0 (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq30263 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq30263
    | exact resolve eq30263 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30263
  have eq30280 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) X0) x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq30264 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq30264
    | exact resolve eq30264 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30264
  have eq32009 : ∀ X0 X1 X2 X3 : G, (M.op X0 x) = (M.op (M.op (M.op X0 x) X2) (M.op X3 (M.op X1 (M.op x y)))) ∨ x = (M.op x y) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 (M.op X0 (M.op x y)) X1 (M.op x y) X3 x
       have i₂ := eq30279 X0
       grind)
    | exact superpose eq30279 eq52
    | exact resolve eq52 eq30279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq30279
  have eq32119 : ∀ X0 X2 : G, (M.op X0 x) = (M.op (M.op (M.op X0 x) X2) y) ∨ x = (M.op x y) := by
    intro X0 X2
    first
    | (have i₁ := eq32009 X0 x X2 x
       have i₂ := eq84 y (M.op (M.op X0 x) X2) x x x
       grind)
    | exact superpose eq84 eq32009
    | exact resolve eq32009 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32009
  have eq39321 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (σ (M.op X0 X0)))) = (M.op X2 (σ (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq363 X3 X0 X2 (σ X0) x
       have i₂ := eq927 X0 X1 x
       grind)
    | exact superpose eq927 eq363
    | exact resolve eq363 eq927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363 eq927
  have eq54904 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (σ (τ X0)))) = (M.op X2 (σ (τ (k X0 X1)))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq4603 (τ X0) (τ X1) X2 X3
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq4603
    | (have j0 := eq4603 (τ X0) (τ X1) X2 X3
       grind)
    | exact resolve eq4603 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4603
  have eq55642 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (σ (τ X0)))) = (M.op X2 (k X0 X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq54904 X0 X1 X2 X3
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq54904
    | (have j0 := eq54904 X0 X1 X2 X3
       grind)
    | exact resolve eq54904 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54904
  have eq55701 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op X2 (k X0 X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq55642 X0 X1 X2 X3
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq55642
    | (have j0 := eq55642 X0 X1 X2 X3
       grind)
    | exact resolve eq55642 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55642
  have eq55729 : ∀ X0 X1 X2 X3 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X2 (M.op X3 X0)) = (M.op X2 (k X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq55701 X0 X1 X2 X3
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq55701
    | (have j0 := eq55701 X0 X1 X2 X3
       grind)
    | exact resolve eq55701 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55701
  have eq55732 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op X2 (k X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq55729 X0 X0 X2 X3
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq55729
    | (have j0 := eq55729 X0 X1 X2 X3
       grind)
    | exact resolve eq55729 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55729
  have eq55902 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X0 X1) (k (M.op X3 X0) X4)) = X0 ∨ (M.op X4 (M.op X3 X0)) = X4 := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq55732 (M.op X3 X0) X4 (M.op X0 X1) x
       have i₂ := eq9 X0 X1 x X3
       grind)
    | exact superpose eq9 eq55732
    | (have j0 := eq55732 (M.op X3 X0) X4 x X3
       grind)
    | exact resolve eq55732 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56000 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X1) = (M.op X3 (M.op X4 (M.op X0 (k X1 X2)))) ∨ (M.op X2 X1) = X2 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq51 X3 X1 X4 X0
       have i₂ := eq55732 X1 X2 X0 X3
       grind)
    | exact superpose eq55732 eq51
    | (have j1 := eq55732 X1 X2 X2 X3
       grind)
    | exact resolve eq51 eq55732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq55732
  have eq71364 : ∀ X0 X1 X2 X3 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (M.op X2 (M.op X3 (σ (τ (k X0 X1)))))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq4598 (τ X1) (τ X0) X2 X3
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq4598
    | (have j0 := eq4598 (τ X0) (τ X1) X2 X3
       grind)
    | exact resolve eq4598 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq4598
  have eq71620 : ∀ X0 X1 X2 X3 : G, (k X0 X1) = (M.op (σ (τ X1)) (M.op X2 (M.op X3 (k X0 X1)))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq71364 X0 X1 X2 X3
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq71364
    | (have j0 := eq71364 X0 X1 X2 X3
       grind)
    | exact resolve eq71364 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71364
  have eq71646 : ∀ X0 X1 X2 X3 : G, (k X0 X1) = (M.op X1 (M.op X2 (M.op X3 (k X0 X1)))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq71620 X0 X1 X2 X3
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq71620
    | (have j0 := eq71620 X0 X1 X2 X3
       grind)
    | exact resolve eq71620 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71620
  have eq71656 : ∀ X0 X1 X2 X3 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) = (M.op X1 (M.op X2 (M.op X3 (k X0 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq71646 X0 X1 X2 X3
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq71646
    | (have j0 := eq71646 X0 X1 X2 X3
       grind)
    | exact resolve eq71646 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71646
  have eq71658 : ∀ X0 X1 X2 X3 : G, (k X0 X1) = (M.op X1 (M.op X2 (M.op X3 (k X0 X1)))) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq71656 X0 X0 X2 X3
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq71656
    | (have j0 := eq71656 X0 X1 X2 X3
       grind)
    | exact resolve eq71656 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71656
  have eq74863 : (σ x) = (M.op (σ x) (σ (M.op x (M.op x y)))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq29712 (M.op (M.op x y) x)
       have i₂ := eq30280 x
       grind)
    | exact superpose eq30280 eq29712
    | exact resolve eq29712 eq30280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29712 eq30280
  have eq75013 : (σ x) = (M.op (σ x) (σ (M.op x (M.op x y)))) ∨ x = (M.op x y) := by grind
  clear eq74863
  have eq158435 : ∀ X0 : G, (τ (M.op (σ y) (σ x))) = (M.op y (M.op X0 x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq29719 (M.op (M.op X0 x) x)
       have i₂ := eq32119 X0 x
       grind)
    | exact superpose eq32119 eq29719
    | exact resolve eq29719 eq32119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29719 eq32119
  have eq158840 : ∀ X0 : G, (τ (M.op (σ y) (σ x))) = (M.op y (M.op X0 x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq158435 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158435
  have eq279796 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (k (M.op X1 X0) X2) ∨ (M.op X2 (M.op X1 X0)) = X2 ∨ (M.op X2 (M.op X1 X0)) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq71658 (M.op X1 X0) X2 X3 (M.op X0 x)
       have i₂ := eq55902 X0 x X1 X2
       grind)
    | exact superpose eq55902 eq71658
    | (have j0 := eq71658 (M.op X1 X0) X2 X2 X3
       have j1 := eq55902 X0 X1 X1 X2
       grind)
    | exact resolve eq71658 eq55902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55902 eq71658
  have eq280043 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (k (M.op X1 X0) X2) ∨ (M.op X2 (M.op X1 X0)) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq279796 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279796
  have eq320705 : ∀ X0 X1 X2 : G, (k X0 (k X2 X1)) = (σ (τ (k X0 (M.op X1 X2)))) ∨ (M.op X1 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 (k X0 (k X2 X1))
       have i₂ := eq9173 X1 X2 X0
       grind)
    | exact superpose eq9173 eq11
    | (have j1 := eq9173 X1 X2 X2
       grind)
    | exact resolve eq11 eq9173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9173
  have eq320849 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 X2)) = (k X0 (k X2 X1)) ∨ (M.op X1 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq320705 X0 X1 X2
       have i₂ := eq11 (k X0 (M.op X1 X2))
       grind)
    | exact superpose eq11 eq320705
    | (have j0 := eq320705 X0 X1 X2
       grind)
    | exact resolve eq320705 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320705
  have eq320954 : ∀ X0 : G, (k X0 (M.op x x)) = (k X0 (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq320849 X0 x y
       have i₂ := eq29932
       grind)
    | exact superpose eq29932 eq320849
    | (have j0 := eq320849 X0 x y
       grind)
    | exact resolve eq320849 eq29932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320849
  have eq354679 : ∀ X0 X1 X2 X3 : G, (k (M.op X0 (M.op X1 X2)) (M.op X2 X3)) = X2 ∨ (M.op X2 X3) = (M.op (M.op X2 X3) (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 X3 x X1
       have i₂ := eq280043 (M.op X1 X2) X0 (M.op X2 X3) x
       grind)
    | exact superpose eq280043 eq9
    | (have j1 := eq280043 (M.op X1 X2) X0 (M.op X2 X3) X3
       grind)
    | exact resolve eq9 eq280043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280043
  have eq355221 : ∀ X0 X1 X2 X3 : G, (k (M.op X0 (M.op X1 X2)) (M.op X2 X3)) = X2 ∨ (M.op X2 X3) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq354679 X0 X1 X2 X3
       have i₂ := eq9 X2 X3 X0 X1
       grind)
    | exact superpose eq9 eq354679
    | (have j0 := eq354679 X0 X1 X2 X3
       grind)
    | exact resolve eq354679 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354679
  have eq357081 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k (M.op X1 (M.op X2 (M.op X0 X0))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq355221 X0 X1 (M.op X0 X0) (τ (M.op (σ (M.op X0 X0)) (M.op X1 (σ X0))))
       have i₂ := eq4500 X0 X1
       grind)
    | exact superpose eq4500 eq355221
    | (have j0 := eq355221 X0 X1 X0 X0
       grind)
    | exact resolve eq355221 eq4500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4500
  have eq357271 : ∀ X0 X1 : G, x = (k (M.op X0 (M.op X1 x)) (M.op x x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq320954 (M.op X0 (M.op X1 x))
       have i₂ := eq355221 X0 X1 x y
       grind)
    | exact superpose eq355221 eq320954
    | (have j1 := eq355221 X0 X1 x x
       grind)
    | exact resolve eq320954 eq355221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320954 eq355221
  have eq357317 : ∀ X0 X1 : G, x = (k (M.op X0 (M.op X1 x)) (M.op x x)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq357271 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357271
  have eq357369 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k (M.op X1 (M.op X2 (M.op X0 X0))) X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq357081 X0 X1 X2
       have j1 := eq242 X0 X0 X1 X2 X0
       grind)
    | (have r₁ := eq357081 X1 X1 X2
       have r₂ := eq242 X1 X1 X2 x x
       grind)
    | exact resolve eq357081 eq242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242 eq357081
  have eq357556 : ∀ X0 X1 X2 X3 : G, (k (M.op X2 (M.op X3 X0)) (M.op X0 (M.op X1 X0))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq357369 (M.op X2 (M.op X3 X2)) X1 X2
       have i₂ := eq9 X2 (M.op X3 X2) X2 X3
       grind)
    | exact superpose eq9 eq357369
    | exact resolve eq357369 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq357847 : ∀ X0 X1 X2 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op X1 (M.op X2 (M.op (σ X0) (σ X0))))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 (M.op X1 (M.op X2 (M.op (σ X0) (σ X0)))) X0
       have i₂ := eq357369 (σ X0) X1 X2
       grind)
    | exact superpose eq357369 eq22
    | exact resolve eq22 eq357369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq357369
  have eq357910 : ∀ X0 X1 X2 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op X1 (M.op X2 (σ (M.op X0 X0))))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq357847 X0 X1 X2
       have i₂ := eq168 X0 X2 (σ X0)
       grind)
    | exact superpose eq168 eq357847
    | exact resolve eq357847 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168 eq357847
  have eq358134 : ∀ X0 X1 X2 : G, (τ (σ (M.op X0 X0))) = (k (τ (M.op X1 (M.op X2 (σ (M.op X0 X0))))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq357910 X0 X1 X2
       have i₂ := eq151 X0
       grind)
    | exact superpose eq151 eq357910
    | exact resolve eq357910 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357910
  have eq358242 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k (τ (M.op X1 (M.op X2 (σ (M.op X0 X0))))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq358134 X0 X1 X2
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq358134
    | exact resolve eq358134 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358134
  have eq358696 : ∀ X0 X3 X4 : G, (M.op X3 X0) = (k X0 (M.op (M.op X3 X0) (M.op X4 (M.op X3 X0)))) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq357556 (M.op X3 X0) X4 (M.op X0 x) x
       have i₂ := eq9 X0 x x X3
       grind)
    | exact superpose eq9 eq357556
    | exact resolve eq357556 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357556
  have eq373641 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (τ (M.op X1 (σ X0))) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq358242 (M.op X0 X0) X1 (M.op (σ X0) x)
       have i₂ := eq572 X0 x
       grind)
    | exact superpose eq572 eq358242
    | exact resolve eq358242 eq572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358242
  have eq421845 : x = (k (τ (M.op (σ y) (σ x))) (M.op x x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq357317 y x
       have i₂ := eq158840 x
       grind)
    | exact superpose eq158840 eq357317
    | exact resolve eq357317 eq158840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158840 eq357317
  have eq421911 : x = (k (τ (M.op (σ y) (σ x))) (M.op x x)) ∨ x = (M.op x y) := by grind
  clear eq421845
  have eq597601 : ∀ X0 X1 X2 : G, (M.op X0 (σ y)) = (M.op X0 (M.op X1 (M.op X2 (σ (M.op x x))))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4606 y x X0 X1 X2
       have i₂ := eq29932
       grind)
    | exact superpose eq29932 eq4606
    | (have j0 := eq4606 y x X2 x x
       grind)
    | exact resolve eq4606 eq29932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4606 eq29932
  have eq599200 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq597601 X0 x x
       have i₂ := eq219 x X0 x x
       grind)
    | exact superpose eq219 eq597601
    | exact resolve eq597601 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219 eq597601
  have eq599469 : (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq599200 (σ y)
       have i₂ := eq151 y
       grind)
    | exact superpose eq151 eq599200
    | exact resolve eq599200 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599200
  have eq656018 : x = (M.op (M.op x x) (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq421911
       have i₂ := eq373641 x (σ y)
       grind)
    | exact superpose eq373641 eq421911
    | exact resolve eq421911 eq373641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373641 eq421911
  have eq656027 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq572 x X0
       have i₂ := eq656018
       grind)
    | exact superpose eq656018 eq572
    | exact resolve eq572 eq656018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572 eq656018
  have eq740209 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq656027 (σ (M.op x (M.op x y)))
       have i₂ := eq75013
       grind)
    | exact superpose eq75013 eq656027
    | exact resolve eq656027 eq75013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75013 eq656027
  have eq740949 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq740209
  have eq741201 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq740949
       have i₂ := eq151 x
       grind)
    | exact superpose eq151 eq740949
    | exact resolve eq740949 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151 eq740949
  have eq741356 : x = (M.op x y) := by
    first
    | (have r₁ := eq741201
       have r₂ := eq30027
       grind)
    | exact resolve eq741201 eq30027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30027 eq741201
  have eq741516 : ∀ X0 X1 : G, x = (M.op x (M.op X0 (M.op X1 x))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 x y X0 X1
       have i₂ := eq741356
       grind)
    | exact superpose eq741356 eq9
    | exact resolve eq9 eq741356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq741525 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op X1 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq74 y X0 X1 x
       have i₂ := eq741356
       grind)
    | exact superpose eq741356 eq74
    | exact resolve eq74 eq741356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq741528 : ∀ X0 X1 X2 : G, (M.op X0 y) = (M.op X0 (M.op X1 (M.op X2 x))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq84 y X0 X2 x X1
       have i₂ := eq741356
       grind)
    | exact superpose eq741356 eq84
    | exact resolve eq84 eq741356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq741568 : (σ y) = (M.op (σ (M.op y y)) (σ (M.op y x))) := by
    first
    | (have i₁ := eq975 y x
       have i₂ := eq741356
       grind)
    | exact superpose eq741356 eq975
    | exact resolve eq975 eq741356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq975
  have eq741699 : ∀ X0 X1 : G, (M.op X0 (σ (M.op y x))) = (M.op X0 (M.op X1 (σ (M.op y y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq39321 y x X0 X1
       have i₂ := eq741356
       grind)
    | exact superpose eq741356 eq39321
    | exact resolve eq39321 eq741356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39321
  have eq3357720 : ∀ X0 : G, (σ (M.op y y)) = (k (σ x) (M.op (σ (M.op y y)) (M.op X0 (σ (M.op y y))))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq358696 (σ x) (σ y) x
       have i₂ := eq599469
       grind)
    | exact superpose eq599469 eq358696
    | exact resolve eq358696 eq599469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358696 eq599469
  have eq3357930 : (σ (M.op y y)) = (k (σ x) (M.op (σ (M.op y y)) (σ (M.op y x)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3357720 x
       have i₂ := eq741699 (σ (M.op y y)) x
       grind)
    | exact superpose eq741699 eq3357720
    | exact resolve eq3357720 eq741699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741699 eq3357720
  have eq3358272 : (σ (M.op y y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3357930
       have i₂ := eq741568
       grind)
    | exact superpose eq741568 eq3357930
    | exact resolve eq3357930 eq741568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741568 eq3357930
  have eq3358431 : (σ (k x y)) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3358272
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq3358272
    | exact resolve eq3358272 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3358272
  have eq3363706 : (k x y) = (τ (σ (M.op y y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq3358431
       grind)
    | exact superpose eq3358431 eq10
    | exact resolve eq10 eq3358431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3358431
  have eq3365355 : (σ x) = (M.op (σ x) (σ y)) ∨ (k x y) = (M.op y y) := by
    first
    | (have i₁ := eq3363706
       have i₂ := eq10 (M.op y y)
       grind)
    | exact superpose eq10 eq3363706
    | exact resolve eq3363706 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3363706
  have eq3365489 : (σ (M.op x y)) ≠ (σ x) ∨ (k x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3365355
       grind)
    | exact superpose eq3365355 eq16
    | exact resolve eq16 eq3365355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3365355
  have eq3366640 : (σ x) ≠ (σ x) ∨ (k x y) = (M.op y y) := by
    first
    | (have i₁ := eq3365489
       have i₂ := eq741356
       grind)
    | exact superpose eq741356 eq3365489
    | exact resolve eq3365489 eq741356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3365489
  have eq3366641 : (k x y) = (M.op y y) := by grind
  clear eq3366640
  have eq3367093 : ∀ X0 X1 X2 : G, (M.op X0 x) = (M.op X0 (M.op X1 (M.op X2 (M.op y y)))) ∨ y = (M.op y x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56000 X2 x y X0 X1
       have i₂ := eq3366641
       grind)
    | exact superpose eq3366641 eq56000
    | (have j0 := eq56000 X0 x y x x
       grind)
    | exact resolve eq56000 eq3366641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56000 eq3366641
  have eq3367194 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq3367093 X0 x x
       have i₂ := eq84 y X0 x y x
       grind)
    | exact superpose eq84 eq3367093
    | exact resolve eq3367093 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq3367093
  have eq3372382 : y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq3367194 x
       have i₂ := eq741356
       grind)
    | exact superpose eq741356 eq3367194
    | exact resolve eq3367194 eq741356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741356 eq3367194
  have eq3375722 : ∀ X0 : G, x = (M.op x (M.op X0 y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq741516 X0 y
       have i₂ := eq3372382
       grind)
    | exact superpose eq3372382 eq741516
    | exact resolve eq741516 eq3372382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741516 eq3372382
  have eq3376596 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq3375722 x
       have i₂ := eq741525 x x
       grind)
    | exact superpose eq741525 eq3375722
    | exact resolve eq3375722 eq741525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741525 eq3375722
  have eq3376597 : x = (M.op x x) := by grind
  clear eq3376596
  have eq3376775 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq29937
       have i₂ := eq3376597
       grind)
    | exact superpose eq3376597 eq29937
    | exact resolve eq29937 eq3376597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29937
  have eq3376979 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op X1 (σ (M.op (τ x) (τ x))))) := by
    intro X0 X1
    first
    | (have i₁ := eq782 x X0 X1
       have i₂ := eq3376597
       grind)
    | exact superpose eq3376597 eq782
    | exact resolve eq782 eq3376597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782
  have eq3377851 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3376775
  have eq3378218 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op X1 (M.op x x))) := by
    intro X0 X1
    first
    | (have i₁ := eq3376979 X0 X1
       have i₂ := eq155 x
       grind)
    | exact superpose eq155 eq3376979
    | exact resolve eq3376979 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155 eq3376979
  have eq3378440 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq3378218 X0 x
       have i₂ := eq741528 X0 x x
       grind)
    | exact superpose eq741528 eq3378218
    | exact resolve eq3378218 eq741528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741528 eq3378218
  have eq3408331 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3377851
       grind)
    | exact superpose eq3377851 eq16
    | exact resolve eq16 eq3377851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3377851
  have eq3409554 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq3408331
       have i₂ := eq3378440 x
       grind)
    | exact superpose eq3378440 eq3408331
    | exact resolve eq3408331 eq3378440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3378440 eq3408331
  have eq3409844 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq3409554
       have i₂ := eq3376597
       grind)
    | exact superpose eq3376597 eq3409554
    | exact resolve eq3409554 eq3376597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3376597 eq3409554
  have eq3409845 : False := by grind
  exact eq3409845

/-- `Equation1473`: `x = (x ◇ y) ◇ (z ◇ (w ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pyx_y_pyx_Equation1473 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1473 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1473.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
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
  clear eq37
  have eq77 : x ≠ (M.op x y) ∨ y = (M.op x x) ∨ x = (k y x) := by
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
  have eq78 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq16
    | exact resolve eq16 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq102
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq102
    | exact resolve eq102 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq113
    | exact resolve eq113 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq114
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq114
    | exact resolve eq114 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq866 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq95 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq8752 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq115 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8753 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq8752
    | exact resolve eq8752 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8752
  have eq8764 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq8753
       have r₂ := eq28
       grind)
    | exact resolve eq8753 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8753
  have eq8766 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq8764
    | exact resolve eq8764 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8764
  have eq8778 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq8766
  have eq8799 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq8778
    | exact resolve eq8778 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8778
  have eq8806 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq8799 eq115
    | exact resolve eq115 eq8799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8799
  have eq8815 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8806
  have eq8817 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq8815
       have r₂ := eq28
       grind)
    | exact resolve eq8815 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8815
  have eq8854 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8817
  have eq8877 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8854
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq8854
    | exact resolve eq8854 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8854
  have eq8882 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq74
       have i₂ := eq8877
       grind)
    | exact superpose eq8877 eq74
    | exact resolve eq74 eq8877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8877
  have eq8898 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq8882
    | exact resolve eq8882 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8882
  have eq9067 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8898 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq8898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9070 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq9067
    | exact resolve eq9067 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9067
  have eq9081 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq9070
       have r₂ := eq28
       grind)
    | exact resolve eq9070 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9070
  have eq9083 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq9081
    | exact resolve eq9081 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9081
  have eq9084 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq9083
  have eq9088 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq9084
  have eq9113 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq9088
    | exact resolve eq9088 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9088
  have eq9129 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9113 eq8898
    | exact resolve eq8898 eq9113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8898 eq9113
  have eq9132 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq9129
  have eq9136 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq9132
       have r₂ := eq28
       grind)
    | exact resolve eq9132 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9132
  have eq9138 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9136 eq28
    | exact resolve eq28 eq9136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9141 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9136 eq78
    | (have r₁ := eq78
       have r₂ := eq9136
       grind)
    | exact resolve eq78 eq9136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq9151 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq9141
  have eq12598 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq9151
  have eq12631 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq12598
    | exact resolve eq12598 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12598
  have eq12687 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq115 eq12631
    | exact resolve eq12631 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq12707 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq12631
  have eq12712 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq12687
  have eq12714 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq12707
       have r₂ := eq9136
       grind)
    | exact resolve eq12707 eq9136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9136 eq12707
  have eq12716 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq12712
       have r₂ := eq9138
       grind)
    | exact resolve eq12712 eq9138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9138 eq12712
  have eq12718 : y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq12716
       have r₂ := eq28
       grind)
    | exact resolve eq12716 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12716
  have eq12989 : (τ (σ x)) = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12714 eq84
    | exact resolve eq84 eq12714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq12714
  have eq13027 : x = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq12989
    | exact resolve eq12989 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq12989
  have eq13035 : (M.op x y) = (k y x) ∨ x = (M.op x y) := by grind
  clear eq12718
  have eq13064 : (M.op x y) = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13035
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq13035
    | exact resolve eq13035 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13035
  have eq13382 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13027
       have i₂ := eq13064
       grind)
    | exact superpose eq13064 eq13027
    | exact resolve eq13027 eq13064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13027 eq13064
  have eq13389 : x = (M.op x y) := by grind
  clear eq13382
  have eq14206 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq13389 eq21
    | exact resolve eq21 eq13389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq14213 : x ≠ x ∨ y = (M.op x x) ∨ x = (k y x) := by
    first
    | exact superpose eq13389 eq77
    | (have r₁ := eq77
       have r₂ := eq13389
       grind)
    | exact resolve eq77 eq13389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq14269 : y = (M.op x x) ∨ x = (k y x) := by grind
  clear eq14213
  have eq14320 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq14206
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq14206
    | exact resolve eq14206 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14206
  have eq14321 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq14320 eq27
    | exact resolve eq27 eq14320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18574 : (M.op x y) = (k y x) ∨ x = (k y x) := by grind
  clear eq14269
  have eq18604 : (M.op x y) = (k y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq18574
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq18574
    | exact resolve eq18574 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq18574
  have eq18617 : x = (k y x) ∨ x = (k y x) := by
    first
    | exact superpose eq13389 eq18604
    | exact resolve eq18604 eq13389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13389 eq18604
  have eq18618 : x = (k y x) := by grind
  clear eq18617
  have eq18627 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq74
       have i₂ := eq18618
       grind)
    | exact superpose eq18618 eq74
    | exact resolve eq74 eq18618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq18644 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq866 x y
       have i₂ := eq18618
       grind)
    | exact superpose eq18618 eq866
    | (have j0 := eq866 x y
       grind)
    | exact resolve eq866 eq18618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq866 eq18618
  have eq18645 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq18644
  have eq18652 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq18645
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq18645
    | exact resolve eq18645 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18645
  have eq18667 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq14320 eq18627
    | exact resolve eq18627 eq14320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18627
  have eq18669 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq18652
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq18652
    | exact resolve eq18652 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18652
  have eq18683 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq18667
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq18667
    | exact resolve eq18667 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18667
  have eq18684 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq18669
    | exact resolve eq18669 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq18669
  have eq18697 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq14320 eq18683
    | exact resolve eq18683 eq14320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18683
  have eq18698 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq14320 eq18684
    | exact resolve eq18684 eq14320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18684
  have eq18706 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq18698
       have r₂ := eq28
       grind)
    | exact resolve eq18698 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18698
  have eq18714 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq18706
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq18706
    | exact resolve eq18706 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq18706
  have eq18722 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq14320 eq18714
    | exact resolve eq18714 eq14320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14320 eq18714
  have eq18730 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq18722
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq18722
    | exact resolve eq18722 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq18722
  have eq18812 : (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq18730
  have eq18842 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq14321 eq18812
    | exact resolve eq18812 eq14321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14321 eq18812
  have eq18845 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18697 eq18842
    | exact resolve eq18842 eq18697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18697 eq18842
  have eq18846 : False := by grind
  exact eq18846

/-- `Equation1473`: `x = (x ◇ y) ◇ (z ◇ (w ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = m(X,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pxy_pyx_pyy_pyx_Equation1473 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1473 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1473.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X3 X0))) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq61 : ∀ X0 X1 X4 X5 : G, (M.op X0 X1) = (M.op X0 (M.op X4 (M.op X5 (M.op X0 X1)))) := by
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
  have eq73 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X0)) = (M.op X1 (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq61 X1 (M.op X2 X0) X3 (M.op X0 x)
       have i₂ := eq9 X0 x X1 X2
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X2) = (M.op X3 (M.op X4 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq61 X3 X2 X4 X0
       have i₂ := eq73 X2 X0 X3 X1
       grind)
    | (have i₁ := eq61 X3 X2 X4 X0
       have i₂ := eq73 X2 X0 X1 X3
       grind)
    | exact superpose eq73 eq61
    | exact resolve eq61 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq73
  have eq1450 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
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
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1518 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X0) = (M.op X2 (M.op X3 (M.op X4 (M.op X0 X1)))) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq114 X4 X0 X0 X2 X3
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq114 X0 X0 X1 X3 X4
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq114
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq114 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1619 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1450 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1450
  have eq1620 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1619 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1619
  have eq1676 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X0) = (M.op X2 (M.op X3 (M.op X4 (M.op X0 X1)))) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have j0 := eq1518 X0 X1 X2 X3 X4
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq1518 X0 X1 X2 X3 X4
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq1518 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1518
  have eq1735 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1620 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq1620 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq1620 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1620
  have eq1820 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op X2 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1676 X0 X1 X2 x x
       have i₂ := eq114 x X0 X1 X2 x
       grind)
    | exact superpose eq114 eq1676
    | (have j0 := eq1676 X0 X1 X2 x x
       grind)
    | exact resolve eq1676 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq1676
  have eq1974 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1735 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1735
  have eq1977 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1974 X0 X1
       have j1 := eq1820 X0 X1 x
       grind)
    | (have r₁ := eq1974 X1 X0
       have r₂ := eq1820 X0 X1 X0
       grind)
    | (have r₁ := eq1974 X0 X1
       have r₂ := eq1820 X0 X1 X1
       grind)
    | exact resolve eq1974 eq1820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1820 eq1974
  have eq2099 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq1977 (σ X1) (σ X0)
       grind)
    | exact superpose eq1977 eq15
    | exact resolve eq15 eq1977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2126 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2099 X0 X1
       have i₂ := eq1977 X1 X0
       grind)
    | exact superpose eq1977 eq2099
    | exact resolve eq2099 eq1977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1977 eq2099
  have eq2365 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2126 x y
       grind)
    | exact superpose eq2126 eq16
    | (have r₁ := eq16
       have r₂ := eq2126 x y
       grind)
    | exact resolve eq16 eq2126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2126
  have eq2397 : False := by grind
  exact eq2397

/-- `Equation1473`: `x = (x ◇ y) ◇ (z ◇ (w ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pyx_pyy_pyx_Equation1473 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1473 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1473.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
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
  have eq25 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq25 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq25 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq25 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq32 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X0
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
  have eq39 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
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
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq46 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq47 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq48 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq44 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq44 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq52 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq46 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq46 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq58 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq47 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq47 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq47 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq63 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq58 X0 X1
       have j1 := eq48 X0 X1
       grind)
    | (have r₁ := eq58 X0 X1
       have r₂ := eq48 X0 X1
       grind)
    | exact resolve eq58 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq58
  have eq65 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X0 X1
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq63
    | (have j0 := eq63 X0 X1
       grind)
    | exact resolve eq63 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq63
  have eq155 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq52 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq159 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq155 X0 X1
       have j1 := eq65 X1 X0
       grind)
    | (have r₁ := eq155 X1 X1
       have r₂ := eq65 X1 X1
       grind)
    | (have r₁ := eq155 X1 X0
       have r₂ := eq65 X0 X1
       grind)
    | exact resolve eq155 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq155
  have eq286 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq159 (σ X1) (σ X0)
       grind)
    | exact superpose eq159 eq15
    | exact resolve eq15 eq159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq289 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq286 X0 X1
       have i₂ := eq159 X1 X0
       grind)
    | exact superpose eq159 eq286
    | exact resolve eq286 eq159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159 eq286
  have eq292 : False := by grind
  exact eq292

/-- `Equation1480`: `x = (y ◇ x) ◇ (x ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pyx_pxx_pyx_Equation1480 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1480 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1480.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X2))) = X0 := by
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq62 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) (M.op (M.op X2 X0) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X2 X0) X1 (M.op X0 (M.op X0 x))
       have i₂ := eq9 X0 X2 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq276 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq277 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq276 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq279 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq277 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq277 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq277 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq290 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq279 (σ X0)
       grind)
    | exact superpose eq279 eq15
    | exact resolve eq15 eq279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq309 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq290 X0
       have i₂ := eq279 X0
       grind)
    | exact superpose eq279 eq290
    | exact resolve eq290 eq279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279 eq290
  have eq354 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (M.op (σ X0) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1 (σ X0)
       have i₂ := eq309 X0
       grind)
    | exact superpose eq309 eq9
    | exact resolve eq9 eq309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq356 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq309 X0
       grind)
    | exact superpose eq309 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq357 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq309 X0
       grind)
    | exact superpose eq309 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq358 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq356 X0 X1
       have j1 := eq357 X0 X1
       grind)
    | (have r₁ := eq356 X0 X1
       have r₂ := eq357 X0 X1
       grind)
    | exact resolve eq356 eq357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356
  have eq519 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq358 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq358
    | exact resolve eq358 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq530 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq358 X0 (σ X1)
       grind)
    | exact superpose eq358 eq15
    | (have j1 := eq358 X0 (σ X1)
       grind)
    | exact resolve eq15 eq358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358
  have eq570 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq519 X0 (τ X1)
       grind)
    | exact superpose eq519 eq17
    | (have j1 := eq519 X0 (τ X1)
       grind)
    | exact resolve eq17 eq519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq519
  have eq701 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq570 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq570
    | exact resolve eq570 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570
  have eq750 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq701 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq701
    | (have j0 := eq701 X0 X1
       grind)
    | exact resolve eq701 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701
  have eq1001 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
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
  have eq1058 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1001
       have i₂ := eq750 y x
       grind)
    | exact superpose eq750 eq1001
    | (have j1 := eq750 (σ y) (σ x)
       grind)
    | (have r₁ := eq1001
       have r₂ := eq750 y x
       grind)
    | exact resolve eq1001 eq750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1001
  have eq1059 : x = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq1058
  have eq1067 : ∀ X0 : G, x = (M.op x (M.op x (M.op x X0))) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq9 x y X0
       have i₂ := eq1059
       grind)
    | exact superpose eq1059 eq9
    | exact resolve eq9 eq1059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1059
  have eq1111 : x = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq1067 (M.op x x)
       have i₂ := eq1067 x
       grind)
    | exact superpose eq1067 eq1067
    | exact resolve eq1067 eq1067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1067
  have eq1121 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq1111
  have eq1132 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ x))) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq62 (σ x) x (σ y)
       have i₂ := eq1121
       grind)
    | exact superpose eq1121 eq62
    | exact resolve eq62 eq1121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1136 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ (M.op x x))) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq1132 X0
       have i₂ := eq309 x
       grind)
    | exact superpose eq309 eq1132
    | exact resolve eq1132 eq309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1132
  have eq1205 : (σ x) = (M.op (σ x) (σ (M.op x x))) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1136 (σ y)
       have i₂ := eq1121
       grind)
    | exact superpose eq1121 eq1136
    | exact resolve eq1136 eq1121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1136
  have eq1215 : (σ x) = (M.op (σ x) (σ (M.op x x))) ∨ x = (M.op x x) := by grind
  clear eq1205
  have eq1221 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq354 x X0
       have i₂ := eq1215
       grind)
    | exact superpose eq1215 eq354
    | exact resolve eq354 eq1215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354 eq1215
  have eq1270 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1221 (σ y)
       have i₂ := eq1121
       grind)
    | exact superpose eq1121 eq1221
    | exact resolve eq1221 eq1121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1121 eq1221
  have eq1285 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq1270
  have eq1294 : x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq1285
       have i₂ := eq309 x
       grind)
    | exact superpose eq309 eq1285
    | exact resolve eq1285 eq309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309 eq1285
  have eq1305 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) X0) = (k X0 (σ x)) ∨ (σ x) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq357 x X0
       have i₂ := eq1294
       grind)
    | exact superpose eq1294 eq357
    | (have j0 := eq357 x X0
       grind)
    | (have r₁ := eq357 x x
       have r₂ := eq1294
       grind)
    | exact resolve eq357 eq1294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1294
  have eq1317 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (σ x)) ∨ (σ x) = (σ (M.op x x)) := by
    intro X0
    first
    | (have j0 := eq1305 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1305
  have eq1322 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq1317 X0
       have j1 := eq357 x X0
       grind)
    | (have r₁ := eq1317 X0
       have r₂ := eq357 x x
       grind)
    | exact resolve eq1317 eq357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357 eq1317
  have eq1332 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (k X0 x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq1322 (σ X0)
       grind)
    | exact superpose eq1322 eq15
    | exact resolve eq15 eq1322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1322
  have eq1410 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1332 y
       grind)
    | exact superpose eq1332 eq16
    | exact resolve eq16 eq1332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1332
  have eq1471 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1410
       have i₂ := eq750 y x
       grind)
    | exact superpose eq750 eq1410
    | (have j1 := eq750 y x
       grind)
    | (have r₁ := eq1410
       have r₂ := eq750 y x
       grind)
    | exact resolve eq1410 eq750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750
  have eq1472 : x = (M.op y x) := by grind
  clear eq1471
  have eq1480 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq62 x x y
       have i₂ := eq1472
       grind)
    | exact superpose eq1472 eq62
    | exact resolve eq62 eq1472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq1576 : x = (M.op x (M.op x x)) := by
    first
    | (have i₁ := eq1480 y
       have i₂ := eq1472
       grind)
    | exact superpose eq1472 eq1480
    | exact resolve eq1480 eq1472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1480
  have eq1608 : ∀ X0 : G, x = (M.op (M.op X0 x) x) := by
    intro X0
    first
    | (have i₁ := eq9 x X0 x
       have i₂ := eq1576
       grind)
    | exact superpose eq1576 eq9
    | exact resolve eq9 eq1576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1576
  have eq1624 : x = (M.op x x) := by
    first
    | (have i₁ := eq1608 y
       have i₂ := eq1472
       grind)
    | exact superpose eq1472 eq1608
    | exact resolve eq1608 eq1472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1472 eq1608
  have eq1648 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq1624
       grind)
    | exact superpose eq1624 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq1624
       grind)
    | exact resolve eq12 eq1624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1624
  have eq1665 : ∀ X0 : G, (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq1648 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1648
  have eq1684 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1410
       have i₂ := eq1665 y
       grind)
    | exact superpose eq1665 eq1410
    | exact resolve eq1410 eq1665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1410 eq1665
  have eq1687 : False := by grind
  exact eq1687

/-- `Equation1480`: `x = (y ◇ x) ◇ (x ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_y_pyx_Equation1480 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1480 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1480.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X2))) = X0 := by
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq62 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) (M.op (M.op X2 X0) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X2 X0) X1 (M.op X0 (M.op X0 x))
       have i₂ := eq9 X0 X2 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq276 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq277 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq276 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq279 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq277 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq277 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq277 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq290 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq279 (σ X0)
       grind)
    | exact superpose eq279 eq15
    | exact resolve eq15 eq279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq309 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq290 X0
       have i₂ := eq279 X0
       grind)
    | exact superpose eq279 eq290
    | exact resolve eq290 eq279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279 eq290
  have eq356 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq309 X0
       grind)
    | exact superpose eq309 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq357 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq309 X0
       grind)
    | exact superpose eq309 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq358 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq356 X0 X1
       have j1 := eq357 X0 X1
       grind)
    | (have r₁ := eq356 X0 X1
       have r₂ := eq357 X0 X1
       grind)
    | exact resolve eq356 eq357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356
  have eq519 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq358 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq358
    | exact resolve eq358 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq530 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq358 X0 (σ X1)
       grind)
    | exact superpose eq358 eq15
    | (have j1 := eq358 X0 (σ X1)
       grind)
    | exact resolve eq15 eq358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358
  have eq570 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq519 X0 (τ X1)
       grind)
    | exact superpose eq519 eq17
    | (have j1 := eq519 X0 (τ X1)
       grind)
    | exact resolve eq17 eq519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq519
  have eq701 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq570 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq570
    | exact resolve eq570 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570
  have eq752 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq701 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq701
    | (have j0 := eq701 X0 X1
       grind)
    | exact resolve eq701 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701
  have eq1003 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
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
  have eq1169 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1003
       have i₂ := eq752 y x
       grind)
    | exact superpose eq752 eq1003
    | (have j1 := eq752 (σ y) (σ x)
       grind)
    | (have r₁ := eq1003
       have r₂ := eq752 y x
       grind)
    | exact resolve eq1003 eq752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1003
  have eq1170 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1169
  have eq1175 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq62 y x x
       have i₂ := eq1170
       grind)
    | exact superpose eq1170 eq62
    | exact resolve eq62 eq1170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1181 : ∀ X0 : G, x = (M.op (M.op X0 x) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1175 X0
       have i₂ := eq1170
       grind)
    | exact superpose eq1170 eq1175
    | exact resolve eq1175 eq1170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1170 eq1175
  have eq1189 : ∀ X0 : G, x = (M.op (M.op X0 x) x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq1181 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1181
  have eq1191 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1189 (M.op x x)
       have i₂ := eq1189 x
       grind)
    | exact superpose eq1189 eq1189
    | exact resolve eq1189 eq1189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1189
  have eq1202 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq1191
  have eq1204 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1202
       grind)
    | exact superpose eq1202 eq16
    | exact resolve eq16 eq1202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1209 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq62 (σ y) x (σ x)
       have i₂ := eq1202
       grind)
    | exact superpose eq1202 eq62
    | exact resolve eq62 eq1202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq2643 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq1209 X0
       have i₂ := eq1202
       grind)
    | exact superpose eq1202 eq1209
    | exact resolve eq1209 eq1202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1202 eq1209
  have eq2653 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq2643 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2643
  have eq2655 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2653 (M.op x (σ x))
       have i₂ := eq2653 x
       grind)
    | exact superpose eq2653 eq2653
    | exact resolve eq2653 eq2653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2653
  have eq2673 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq2655
  have eq2678 : x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2673
       have i₂ := eq309 x
       grind)
    | exact superpose eq309 eq2673
    | exact resolve eq2673 eq309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309 eq2673
  have eq2684 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) X0) = (k X0 (σ x)) ∨ (σ x) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq357 x X0
       have i₂ := eq2678
       grind)
    | exact superpose eq2678 eq357
    | (have j0 := eq357 x X0
       grind)
    | (have r₁ := eq357 x x
       have r₂ := eq2678
       grind)
    | exact resolve eq357 eq2678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2678
  have eq2697 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (σ x)) ∨ (σ x) = (σ (M.op x x)) := by
    intro X0
    first
    | (have j0 := eq2684 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2684
  have eq2702 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq2697 X0
       have j1 := eq357 x X0
       grind)
    | (have r₁ := eq2697 X0
       have r₂ := eq357 x x
       grind)
    | exact resolve eq2697 eq357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357 eq2697
  have eq2720 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq2702 (σ X0)
       grind)
    | exact superpose eq2702 eq15
    | exact resolve eq15 eq2702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2702
  have eq2850 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2720 y
       grind)
    | exact superpose eq2720 eq16
    | exact resolve eq16 eq2720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2720
  have eq2918 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2850
       have i₂ := eq752 y x
       grind)
    | exact superpose eq752 eq2850
    | (have j1 := eq752 y x
       grind)
    | (have r₁ := eq2850
       have r₂ := eq752 y x
       grind)
    | exact resolve eq2850 eq752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq752
  have eq2919 : x = (M.op x y) := by grind
  clear eq2918
  have eq2924 : (σ x) ≠ (σ x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1204
       have i₂ := eq2919
       grind)
    | exact superpose eq2919 eq1204
    | exact resolve eq1204 eq2919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1204 eq2919
  have eq2937 : x = (M.op x x) := by grind
  clear eq2924
  have eq2943 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq2937
       grind)
    | exact superpose eq2937 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq2937
       grind)
    | exact resolve eq12 eq2937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2937
  have eq2960 : ∀ X0 : G, (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq2943 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2943
  have eq3010 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq2850
       have i₂ := eq2960 y
       grind)
    | exact superpose eq2960 eq2850
    | exact resolve eq2850 eq2960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2850 eq2960
  have eq3014 : False := by grind
  exact eq3014

/-- `Equation1481`: `x = (y ◇ x) ◇ (x ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxy_pxx_pyx_Equation1481 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1481 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1481.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0))) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ X0 = X1 := by
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
  have eq36 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (k (σ X0) X1) (σ X2)) := by
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
  have eq37 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq43 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X0
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 : G, (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (k X1 (τ X0))
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq22
    | exact resolve eq22 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq10
    | exact resolve eq10 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq95 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq97 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = (M.op (τ X1) (τ X1)) ∨ (τ X1) = X0 := by
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
  have eq98 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = (τ (M.op X1 X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq97 X0 X1
       have i₂ := eq68 X1
       grind)
    | exact superpose eq68 eq97
    | (have j0 := eq97 X0 X1
       grind)
    | exact resolve eq97 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq100 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq95 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq95
    | (have j0 := eq95 X0 X1
       grind)
    | exact resolve eq95 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq131 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 (M.op X1 (M.op X0 X1))) ∨ (M.op X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X1 (M.op X0 X1))
       have i₂ := eq43 X1 X0
       grind)
    | exact superpose eq43 eq13
    | (have j0 := eq13 X1 (M.op X1 (M.op X0 X1))
       grind)
    | (have r₁ := eq13 X1 (M.op X1 (M.op X1 X1))
       have r₂ := eq43 X1 X1
       grind)
    | exact resolve eq13 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq100 X0 (k X1 (τ X0))
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq100
    | exact resolve eq100 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq206 : ∀ X0 X1 X2 : G, (M.op (k (σ X0) X1) (k (σ X0) X1)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq196 X0 X1 X2
       have i₂ := eq46 X0 X1
       grind)
    | exact superpose eq46 eq196
    | (have j0 := eq196 X0 X1 X2
       grind)
    | exact resolve eq196 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq196
  have eq958 : ∀ X0 X1 : G, (τ X1) = (M.op (τ X1) (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = (τ (M.op X1 X1)) ∨ (σ (M.op X0 (τ X1))) = (k X1 (σ (M.op (τ X1) (M.op X0 (τ X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq98 (M.op (τ X1) (M.op X1 (τ X1))) X1
       have i₂ := eq43 (τ X1) X1
       grind)
    | exact superpose eq43 eq98
    | (have j0 := eq98 X0 X1
       grind)
    | exact resolve eq98 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq3116 : ∀ X0 X1 X2 X3 : G, (M.op (σ X0) (k (σ X1) X2)) ≠ (M.op X3 (k (σ X1) X2)) ∨ (k (k (σ X1) X2) X3) = (M.op (σ X0) (k (σ X1) X2)) ∨ (k (σ X1) X2) = X3 ∨ (M.op (σ X0) (k (σ X1) X2)) = (σ (k (k X1 (τ X2)) X0)) ∨ (σ X0) = (k (σ X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 (k (σ X0) X1) X1
       have i₂ := eq206 X0 X1 X2
       grind)
    | exact superpose eq206 eq13
    | (have j0 := eq13 (k (k (σ X1) X2) X3) (M.op (σ X0) (k (σ X1) X2))
       have j1 := eq206 X1 X2 X0
       grind)
    | (have r₁ := eq13 (k (σ X0) X1) (σ X2)
       have r₂ := eq206 X0 X1 X2
       grind)
    | exact resolve eq13 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq71820 : ∀ X0 X1 : G, (M.op (τ X0) (τ X0)) = (M.op X1 (τ X0)) ∨ (τ (M.op X0 X0)) = (M.op X1 (τ X0)) ∨ (σ (M.op X1 (τ X0))) = (k X0 (σ (M.op (τ X0) (M.op X1 (τ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq43 (τ X0) X1
       have i₂ := eq958 X1 X0
       grind)
    | exact superpose eq958 eq43
    | (have j1 := eq958 X1 X0
       grind)
    | exact resolve eq43 eq958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq958
  have eq71836 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op X1 (τ X0)) ∨ (τ (M.op X0 X0)) = (M.op X1 (τ X0)) ∨ (σ (M.op X1 (τ X0))) = (k X0 (σ (M.op (τ X0) (M.op X1 (τ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq71820 X0 X1
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq71820
    | (have j0 := eq71820 X0 X1
       grind)
    | exact resolve eq71820 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq71820
  have eq71837 : ∀ X0 X1 : G, (σ (M.op X1 (τ X0))) = (k X0 (σ (M.op (τ X0) (M.op X1 (τ X0))))) ∨ (τ (M.op X0 X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq71836 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71836
  have eq72144 : ∀ X0 X1 : G, (k X1 (τ (σ (M.op (τ (σ X1)) (M.op X0 (τ (σ X1))))))) = (τ (σ (M.op X0 (τ (σ X1))))) ∨ (τ (M.op (σ X1) (σ X1))) = (M.op X0 (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X1 (σ (M.op (τ (σ X1)) (M.op X0 (τ (σ X1)))))
       have i₂ := eq71837 (σ X1) X0
       grind)
    | exact superpose eq71837 eq37
    | (have j1 := eq71837 (σ X1) X0
       grind)
    | exact resolve eq37 eq71837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq71837
  have eq72387 : ∀ X0 X1 : G, (M.op X0 (τ (σ X1))) = (k X1 (τ (σ (M.op (τ (σ X1)) (M.op X0 (τ (σ X1))))))) ∨ (τ (M.op (σ X1) (σ X1))) = (M.op X0 (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq72144 X0 X1
       have i₂ := eq10 (M.op X0 (τ (σ X1)))
       grind)
    | exact superpose eq10 eq72144
    | (have j0 := eq72144 X0 X1
       grind)
    | exact resolve eq72144 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72144
  have eq72573 : ∀ X0 X1 : G, (M.op X0 (τ (σ X1))) = (k X1 (M.op (τ (σ X1)) (M.op X0 (τ (σ X1))))) ∨ (τ (M.op (σ X1) (σ X1))) = (M.op X0 (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq72387 X0 X1
       have i₂ := eq10 (M.op (τ (σ X1)) (M.op X0 (τ (σ X1))))
       grind)
    | exact superpose eq10 eq72387
    | (have j0 := eq72387 X0 X1
       grind)
    | exact resolve eq72387 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72387
  have eq72695 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (M.op X1 (M.op X0 X1))) ∨ (τ (M.op (σ X1) (σ X1))) = (M.op X0 (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq72573 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq72573
    | (have j0 := eq72573 X0 X1
       grind)
    | exact resolve eq72573 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72573
  have eq72779 : ∀ X0 X1 : G, (M.op X0 X1) = (τ (M.op (σ X1) (σ X1))) ∨ (M.op X0 X1) = (k X1 (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq72695 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq72695
    | (have j0 := eq72695 X0 X1
       grind)
    | exact resolve eq72695 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72695
  have eq72850 : ∀ X0 X1 : G, (M.op X0 X1) = (τ (σ (M.op X1 X1))) ∨ (M.op X0 X1) = (k X1 (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq72779 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq72779
    | (have j0 := eq72779 X0 X1
       grind)
    | exact resolve eq72779 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72779
  have eq72907 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (M.op X1 (M.op X0 X1))) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq72850 X0 X1
       have i₂ := eq10 (M.op X1 X1)
       grind)
    | exact superpose eq10 eq72850
    | (have j0 := eq72850 X0 X1
       grind)
    | exact resolve eq72850 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72850
  have eq72992 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X0) (M.op X1 X0)) ∨ (M.op X0 (M.op X1 X0)) = (k (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq72907 X0 (M.op X1 X0)
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq72907
    | (have j0 := eq72907 X0 (M.op X1 X0)
       grind)
    | exact resolve eq72907 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72907
  have eq82803 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) ≠ (M.op X0 (M.op X1 X0)) ∨ (M.op X0 (M.op X1 X0)) = (k (M.op X1 X0) (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0)))) ∨ (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0))) ∨ (M.op X0 (M.op X1 X0)) = (k (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq131 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq72992 X0 X1
       grind)
    | exact superpose eq72992 eq131
    | (have j0 := eq131 X0 (M.op X1 X0)
       have j1 := eq72992 X0 X1
       grind)
    | (have r₁ := eq131 X0 (M.op X1 X0)
       have r₂ := eq72992 X0 X1
       grind)
    | exact resolve eq131 eq72992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq72992
  have eq82804 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (k (M.op X1 X0) (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0)))) ∨ (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0))) ∨ (M.op X0 (M.op X1 X0)) = (k (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have j0 := eq82803 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82803
  have eq82805 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (k (M.op X1 X0) X0) ∨ (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0))) ∨ (M.op X0 (M.op X1 X0)) = (k (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq82804 X0 X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq82804
    | (have j0 := eq82804 X0 X1
       grind)
    | exact resolve eq82804 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82804
  have eq82806 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (k (M.op X1 X0) X0) ∨ (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq82805 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82805
  have eq82851 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (k (M.op X1 X0) X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq82806 X0 X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq82806
    | (have j0 := eq82806 X0 X1
       grind)
    | exact resolve eq82806 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82806
  have eq83458 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X0)) X0) = (k X0 (M.op X0 (M.op X1 X0))) ∨ (M.op X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq82851 (M.op X0 (M.op X1 X0)) (M.op X1 X0)
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq82851
    | exact resolve eq82851 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82851
  have eq83731 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 ∨ (M.op X1 X0) = (k X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq83458 X0 X1
       have i₂ := eq43 X0 X1
       grind)
    | exact superpose eq43 eq83458
    | (have j0 := eq83458 X0 X1
       grind)
    | exact resolve eq83458 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83458
  have eq83768 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 (M.op X1 X0)) X0) ∨ (k (M.op X0 (M.op X1 X0)) (M.op (M.op X0 (M.op X1 X0)) X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq83731 (M.op X0 (M.op X1 X0)) (M.op X1 X0)
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq83731
    | exact resolve eq83731 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83731
  have eq83952 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op X1 X0)) ∨ (k (M.op X0 (M.op X1 X0)) (M.op (M.op X0 (M.op X1 X0)) X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq83768 X0 X1
       have i₂ := eq43 X0 X1
       grind)
    | exact superpose eq43 eq83768
    | (have j0 := eq83768 X0 X1
       grind)
    | exact resolve eq83768 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83768
  have eq83980 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op X1 X0)) ∨ (k (M.op X0 (M.op X1 X0)) (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq83952 X0 X1
       have i₂ := eq43 X0 X1
       grind)
    | exact superpose eq43 eq83952
    | (have j0 := eq83952 X0 X1
       grind)
    | exact resolve eq83952 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq83952
  have eq85748 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = X1 ∨ (k (M.op X1 (M.op X0 X1)) (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0
       have i₂ := eq83980 X1 X0
       grind)
    | exact superpose eq83980 eq9
    | (have j1 := eq83980 X1 X0
       grind)
    | exact resolve eq9 eq83980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83980
  have eq168475 : ∀ X0 X1 X2 : G, (k (k (σ X0) X1) (σ X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq3116 X2 X0 X1 (σ X2)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3116
  have eq168476 : ∀ X0 X1 X2 : G, (k (k (σ X0) X1) (σ X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq168475 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168475
  have eq168491 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq168476 X0 X1 X2
       have i₂ := eq36 X0 X1 X2
       grind)
    | exact superpose eq36 eq168476
    | (have j0 := eq168476 X0 X1 X2
       grind)
    | exact resolve eq168476 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq168476
  have eq168492 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq168491 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168491
  have eq218843 : ∀ X0 X1 X2 : G, (k (σ (k X1 (τ X2))) X0) = (M.op (σ (τ X0)) (k (σ X1) X2)) ∨ (σ (τ X0)) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X0 (k X1 (τ X2))
       have i₂ := eq168492 X1 X2 (τ X0)
       grind)
    | exact superpose eq168492 eq19
    | (have j1 := eq168492 X1 X2 (τ X0)
       grind)
    | exact resolve eq19 eq168492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168492
  have eq219159 : ∀ X0 X1 X2 : G, (k (σ (k X1 (τ X2))) X0) = (M.op X0 (k (σ X1) X2)) ∨ (σ (τ X0)) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq218843 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq218843
    | (have j0 := eq218843 X0 X1 X2
       grind)
    | exact resolve eq218843 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218843
  have eq219291 : ∀ X0 X1 X2 : G, (k (k (σ X1) X2) X0) = (M.op X0 (k (σ X1) X2)) ∨ (σ (τ X0)) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq219159 X0 X1 X2
       have i₂ := eq19 X2 X1
       grind)
    | exact superpose eq19 eq219159
    | (have j0 := eq219159 X0 X1 X2
       grind)
    | exact resolve eq219159 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219159
  have eq219406 : ∀ X0 X1 X2 : G, (k (k (σ X1) X2) X0) = (M.op X0 (k (σ X1) X2)) ∨ (k (σ X1) X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq219291 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq219291
    | (have j0 := eq219291 X0 X1 X2
       grind)
    | exact resolve eq219291 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219291
  have eq220563 : ∀ X0 X1 X2 : G, (k (k X0 X1) X2) = (M.op X2 (k X0 X1)) ∨ (k X0 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq219406 X0 (τ X0) X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq219406
    | exact resolve eq219406 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219406
  have eq221260 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = (M.op X1 (M.op X0 X0)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq223340 : ∀ X0 X1 X2 : G, (k (M.op X0 (M.op X1 X0)) (M.op X1 X0)) = X0 ∨ X0 = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq221260 (M.op X0 X1) X1
       have i₂ := eq85748 X0 X1
       grind)
    | exact superpose eq85748 eq221260
    | (have j1 := eq85748 X1 X0
       grind)
    | exact resolve eq221260 eq85748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85748 eq221260
  have eq262775 : ∀ X0 X2 X3 : G, (k X0 X2) = (M.op X2 X0) ∨ X0 = X2 ∨ X0 = X3 ∨ (k X0 X3) = (M.op X3 X0) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq220563 (M.op X0 (M.op x X0)) (M.op x X0) X2
       have i₂ := eq223340 X0 x X2
       grind)
    | exact superpose eq223340 eq220563
    | (have j0 := eq220563 X0 X2 (M.op X2 X0)
       have j1 := eq223340 X0 x X2
       grind)
    | exact resolve eq220563 eq223340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220563 eq223340
  have eq264530 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq262775 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262775
  have eq264531 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq264530 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264530
  have eq264532 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq264531 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264531
  have eq264796 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq264532 X1 (τ X0)
       grind)
    | exact superpose eq264532 eq19
    | (have j1 := eq264532 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq264532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq265072 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq264532 (σ X1) (σ X0)
       grind)
    | exact superpose eq264532 eq15
    | (have j1 := eq264532 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq264532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264532
  have eq268833 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq264796 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq264796
    | exact resolve eq264796 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264796
  have eq269397 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq268833 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq268833
    | (have j0 := eq268833 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq268833 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268833
  have eq273813 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq265072 x y
       grind)
    | exact superpose eq265072 eq16
    | (have j1 := eq265072 x y
       grind)
    | exact resolve eq16 eq265072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265072
  have eq274153 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq273813
       have i₂ := eq269397 x y
       grind)
    | exact superpose eq269397 eq273813
    | (have j1 := eq269397 (σ x) (σ y)
       grind)
    | (have r₁ := eq273813
       have r₂ := eq269397 x y
       grind)
    | (have r₁ := eq273813
       have r₂ := eq269397 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq273813
       have r₂ := eq269397 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq273813 eq269397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269397 eq273813
  have eq274156 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq274153
  have eq275173 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq274156
       grind)
    | exact superpose eq274156 eq16
    | exact resolve eq16 eq274156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274156
  have eq275174 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq275173
       have r₂ := eq22 x
       grind)
    | exact resolve eq275173 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275173
  have eq275175 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq275174
       grind)
    | exact superpose eq275174 eq16
    | exact resolve eq16 eq275174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq275176 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq275174
       grind)
    | exact superpose eq275174 eq10
    | exact resolve eq10 eq275174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275174
  have eq275554 : x = y := by
    first
    | (have i₁ := eq275176
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq275176
    | exact resolve eq275176 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275176
  have eq275555 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq275175
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq275175
    | exact resolve eq275175 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq275175
  have eq275569 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq275555
       have i₂ := eq275554
       grind)
    | exact superpose eq275554 eq275555
    | exact resolve eq275555 eq275554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275554 eq275555
  have eq275570 : False := by grind
  exact eq275570

/-- `Equation1483`: `x = (y ◇ x) ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_x_y_pxy_pxx_pxy_Equation1483 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1483 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1483.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
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
  have eq100 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq112 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq114 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (M.op (τ X0) X1) = X1 := by
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
  have eq534 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq100 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq100
    | exact resolve eq100 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq556 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq534 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq534
    | (have j0 := eq534 X0
       grind)
    | exact resolve eq534 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq534
  have eq559 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq556 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq556
    | (have j0 := eq556 X0
       grind)
    | exact resolve eq556 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556
  have eq560 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq559 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq559 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq559 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559
  have eq571 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq560 (σ X0)
       grind)
    | exact superpose eq560 eq15
    | exact resolve eq15 eq560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq590 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq571 X0
       have i₂ := eq560 X0
       grind)
    | exact superpose eq560 eq571
    | exact resolve eq571 eq560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560 eq571
  have eq2820 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq112 x y
       grind)
    | exact superpose eq112 eq16
    | (have j1 := eq112 x y
       grind)
    | exact resolve eq16 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2861 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq112 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq4340 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq114 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq114
    | exact resolve eq114 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq4418 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4340 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq4340
    | (have j0 := eq4340 X0 X1
       grind)
    | exact resolve eq4340 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4340
  have eq4508 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2861 (τ X0) (τ X1)
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq2861
    | (have j0 := eq2861 (τ X0) (τ X1)
       grind)
    | exact resolve eq2861 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq4516 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq4508 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq4508
    | (have j0 := eq4508 X0 X1
       grind)
    | exact resolve eq4508 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4508
  have eq4519 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq4516 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq4516
    | (have j0 := eq4516 X0 X1
       grind)
    | exact resolve eq4516 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4516
  have eq4521 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq4519 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq4519
    | (have j0 := eq4519 X0 X1
       grind)
    | exact resolve eq4519 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4519
  have eq4522 : ∀ X0 X1 : G, X0 = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq4521 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4521
    | (have j0 := eq4521 X0 X1
       grind)
    | exact resolve eq4521 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4521
  have eq4523 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ X0 = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4522 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4522
    | (have j0 := eq4522 X0 X1
       grind)
    | exact resolve eq4522 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4522
  have eq4524 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4523 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4523
    | (have j0 := eq4523 X0 X1
       grind)
    | exact resolve eq4523 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4523
  have eq14780 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2820
       have i₂ := eq4418 x y
       grind)
    | exact superpose eq4418 eq2820
    | (have j1 := eq4418 (σ x) (σ y)
       grind)
    | (have r₁ := eq2820
       have r₂ := eq4418 x y
       grind)
    | (have r₁ := eq2820
       have r₂ := eq4418 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq2820
       have r₂ := eq4418 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq2820 eq4418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2820 eq4418
  have eq14781 : x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq14780
  have eq14783 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14781
       grind)
    | exact superpose eq14781 eq16
    | exact resolve eq16 eq14781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14781
  have eq14784 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq14783
       have r₂ := eq590 x
       grind)
    | exact resolve eq14783 eq590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14783
  have eq14787 : y ≠ y ∨ y = (k x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq14784
       grind)
    | exact superpose eq14784 eq12
    | (have r₁ := eq12 x y
       have r₂ := eq14784
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq14784
       grind)
    | exact resolve eq12 eq14784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14784
  have eq14818 : y = (k x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq14787
  have eq15082 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2861 x y
       have i₂ := eq14818
       grind)
    | exact superpose eq14818 eq2861
    | (have j0 := eq2861 x y
       grind)
    | exact resolve eq2861 eq14818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2861 eq14818
  have eq15103 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq15082
  have eq15104 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq15103
  have eq15110 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15104
       grind)
    | exact superpose eq15104 eq16
    | exact resolve eq16 eq15104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15123 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq15104
       grind)
    | exact superpose eq15104 eq12
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq15104
       grind)
    | exact resolve eq12 eq15104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15104
  have eq15154 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq15123
  have eq15161 : (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq15154
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq15154
    | exact resolve eq15154 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15154
  have eq15173 : y = (τ (σ x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq15161
       grind)
    | exact superpose eq15161 eq10
    | exact resolve eq10 eq15161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15161
  have eq15261 : x = y ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq15173
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq15173
    | exact resolve eq15173 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15173
  have eq15267 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15261
       grind)
    | exact superpose eq15261 eq16
    | exact resolve eq16 eq15261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15261
  have eq15268 : (σ y) = (σ (k x y)) := by
    first
    | (have r₁ := eq15267
       have r₂ := eq590 x
       grind)
    | exact resolve eq15267 eq590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15267
  have eq15278 : (k x y) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq15268
       grind)
    | exact superpose eq15268 eq10
    | exact resolve eq10 eq15268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15268
  have eq15367 : y = (k x y) := by
    first
    | (have i₁ := eq15278
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq15278
    | exact resolve eq15278 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15278
  have eq15382 : y ≠ y ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4524 x y
       have i₂ := eq15367
       grind)
    | exact superpose eq15367 eq4524
    | (have j0 := eq4524 x y
       grind)
    | (have r₁ := eq4524 x y
       have r₂ := eq15367
       grind)
    | exact resolve eq4524 eq15367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4524 eq15367
  have eq15396 : x = y ∨ y = (M.op x y) := by grind
  clear eq15382
  have eq15400 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15396
       grind)
    | exact superpose eq15396 eq16
    | exact resolve eq16 eq15396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15396
  have eq15405 : y = (M.op x y) := by
    first
    | (have r₁ := eq15400
       have r₂ := eq590 x
       grind)
    | exact resolve eq15400 eq590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15400
  have eq15409 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq15110
       have i₂ := eq15405
       grind)
    | exact superpose eq15405 eq15110
    | exact resolve eq15110 eq15405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15110 eq15405
  have eq15444 : (σ x) = (σ y) := by grind
  clear eq15409
  have eq15446 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq15444
       grind)
    | exact superpose eq15444 eq10
    | exact resolve eq10 eq15444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15444
  have eq15536 : x = y := by
    first
    | (have i₁ := eq15446
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq15446
    | exact resolve eq15446 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15446
  have eq15545 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15536
       grind)
    | exact superpose eq15536 eq16
    | exact resolve eq16 eq15536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15536
  have eq15551 : False := by grind
  exact eq15551
