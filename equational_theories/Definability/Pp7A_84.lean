import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,Y) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyy_x_pxy_pxx_pxy_Equation434 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law434 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X1 := by
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
  have eq20 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 (M.op x x))
       have i₂ := eq9 X0 (M.op X0 (M.op x x)) x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq9 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq20 (M.op X1 X1) X0
       have i₂ := eq21 X1 X0
       grind)
    | exact superpose eq21 eq20
    | exact resolve eq20 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 (M.op X0 X0)) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq21 X0 (M.op X0 X0)
       grind)
    | exact superpose eq21 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq21 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq34 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq33 X0 X1
       have i₂ := eq21 X0 X1
       grind)
    | exact superpose eq21 eq33
    | exact resolve eq33 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq45 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq60 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (M.op X1 X1)
       have i₂ := eq34 X1 (τ X0)
       grind)
    | exact superpose eq34 eq18
    | exact resolve eq18 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq65 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq60 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq60
    | exact resolve eq60 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq70 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    grind
  have eq88 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (σ (M.op X1 X1))
       have i₂ := eq65 (τ X0) X1
       grind)
    | exact superpose eq65 eq18
    | exact resolve eq18 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 : G, (k X0 (σ (σ (M.op X1 X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq88 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq88
    | exact resolve eq88 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq97 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (M.op X1 X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (σ (σ (M.op X1 X1)))
       have i₂ := eq89 (τ X0) X1
       grind)
    | exact superpose eq89 eq18
    | exact resolve eq18 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq98 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (M.op X1 X1))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq97 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq97
    | exact resolve eq97 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq104 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (k (σ X0) X1) (σ X2)) := by
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
  have eq105 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq108 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq64 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq64
    | exact resolve eq64 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq64 X0 X1
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq64
    | (have j1 := eq14 (σ X1) (σ X1)
       grind)
    | exact resolve eq64 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq105 X0 (M.op X1 X1)
       have i₂ := eq34 X1 (σ X0)
       grind)
    | exact superpose eq34 eq105
    | exact resolve eq105 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq123 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq123
    | exact resolve eq123 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq162 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (τ (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq105 X0 (τ (M.op X1 X1))
       have i₂ := eq136 (σ X0) X1
       grind)
    | exact superpose eq136 eq105
    | exact resolve eq105 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq165 : ∀ X0 X1 : G, (k X0 (τ (τ (M.op X1 X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq162 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq162
    | exact resolve eq162 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162
  have eq183 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ X2) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq45 X0 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq45
    | exact resolve eq45 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq45 X0 X0
       grind)
    | exact superpose eq45 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq45 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq45 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq45 X0 X1
       grind)
    | exact resolve eq12 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : ∀ X0 X1 : G, (M.op X1 (σ (k X0 X0))) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq21 (σ X0) X1
       have i₂ := eq45 X0 X0
       grind)
    | exact superpose eq45 eq21
    | (have j1 := eq45 X0 X0
       grind)
    | exact resolve eq21 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq200 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq45 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq201 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq200 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq210 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X1 (σ (k X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq189 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq212 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq187 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq218 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq212 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq212 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq212 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq250 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (M.op X1 X1)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (σ (σ (σ (M.op X1 X1))))
       have i₂ := eq98 (τ X0) X1
       grind)
    | exact superpose eq98 eq18
    | exact resolve eq18 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq252 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (σ (M.op X1 X1)))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq250 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq250
    | exact resolve eq250 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq256 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq70 (σ x)
       have i₂ := eq45 x x
       grind)
    | exact superpose eq45 eq70
    | (have j0 := eq70 (σ X0)
       have j1 := eq45 X0 X0
       grind)
    | exact resolve eq70 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq261 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq256 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256
  have eq262 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq261 X0
       have j1 := eq201 X0
       grind)
    | (have r₁ := eq261 X0
       have r₂ := eq201 X0
       grind)
    | exact resolve eq261 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261
  have eq263 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq262 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq262
    | (have j0 := eq262 X0
       grind)
    | exact resolve eq262 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262
  have eq292 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (σ (M.op X1 X1))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (σ (σ (σ (σ (M.op X1 X1)))))
       have i₂ := eq252 (τ X0) X1
       grind)
    | exact superpose eq252 eq18
    | exact resolve eq18 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252
  have eq294 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (σ (σ (M.op X1 X1))))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq292 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq292
    | exact resolve eq292 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292
  have eq361 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (σ (σ (M.op X1 X1)))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (σ (σ (σ (σ (σ (M.op X1 X1))))))
       have i₂ := eq294 (τ X0) X1
       grind)
    | exact superpose eq294 eq18
    | exact resolve eq18 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294
  have eq363 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (σ (σ (σ (M.op X1 X1)))))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq361 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq361
    | exact resolve eq361 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361
  have eq426 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (σ (σ (σ (M.op X1 X1))))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (σ (σ (σ (σ (σ (σ (M.op X1 X1)))))))
       have i₂ := eq363 (τ X0) X1
       grind)
    | exact superpose eq363 eq18
    | exact resolve eq18 eq363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363
  have eq428 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (σ (σ (σ (σ (M.op X1 X1))))))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq426 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq426
    | exact resolve eq426 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426
  have eq653 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (M.op (σ X0) X1) (σ X2)) ∨ (σ X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq104 X0 X1 X2
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq104
    | (have j1 := eq14 (σ X0) X1
       grind)
    | exact resolve eq104 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq834 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ X0) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (M.op X2 (σ (k X0 X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq210 X0 X2
       grind)
    | exact superpose eq210 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq210 X0 X2
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq210 X0 X1
       grind)
    | (have r₁ := eq12 X0 (σ (k X0 X0))
       have r₂ := eq210 X0 (σ (k X0 X0))
       grind)
    | exact resolve eq12 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq854 : ∀ X0 X1 X2 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (M.op X2 (σ (k X0 X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq834 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834
  have eq957 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ (M.op X0 X0))) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq218 (M.op X0 X0) X1
       have i₂ := eq34 X0 (M.op X0 X0)
       grind)
    | exact superpose eq34 eq218
    | (have j0 := eq218 (M.op X0 X0) X1
       grind)
    | exact resolve eq218 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq966 : ∀ X0 X1 : G, (σ (τ (τ (M.op X0 X0)))) ≠ (σ (τ (τ (M.op X0 X0)))) ∨ (k X1 (σ (τ (τ (M.op X0 X0))))) = (M.op X1 (σ (τ (τ (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq218 (τ (τ (M.op X0 X0))) X1
       have i₂ := eq165 (τ (τ (M.op X0 X0))) X0
       grind)
    | exact superpose eq165 eq218
    | (have j0 := eq218 (τ (τ (M.op X0 X0))) X1
       grind)
    | exact resolve eq218 eq165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165
  have eq977 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (k X1 (σ (τ X0))) = (M.op X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq218 (τ X0) X1
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq218
    | (have j0 := eq218 (τ X0) X1
       grind)
    | exact resolve eq218 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq985 : ∀ X0 X1 : G, (k X1 (σ (τ (τ (M.op X0 X0))))) = (M.op X1 (σ (τ (τ (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have j0 := eq966 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq966
  have eq994 : ∀ X0 X1 : G, (k X1 (σ (M.op X0 X0))) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq957 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq957
  have eq996 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = (M.op X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq977 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq977
    | (have j0 := eq977 X0 X1
       grind)
    | exact resolve eq977 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq977
  have eq1004 : ∀ X0 X1 : G, (k X1 (τ (M.op X0 X0))) = (M.op X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq985 X0 X1
       have i₂ := eq11 (τ (M.op X0 X0))
       grind)
    | exact superpose eq11 eq985
    | exact resolve eq985 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq985
  have eq1013 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq994 X0 X1
       have i₂ := eq65 X1 X0
       grind)
    | exact superpose eq65 eq994
    | exact resolve eq994 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq994
  have eq1014 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq996 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq996
    | (have j0 := eq996 X0 X1
       grind)
    | exact resolve eq996 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq996
  have eq1022 : ∀ X0 X1 : G, (M.op X1 (τ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1004 X0 X1
       have i₂ := eq136 X1 X0
       grind)
    | exact superpose eq136 eq1004
    | exact resolve eq1004 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1004
  have eq1055 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (M.op (σ (M.op X1 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq20 (σ (M.op X1 X1)) X0
       have i₂ := eq1013 X1 X0
       grind)
    | exact superpose eq1013 eq20
    | exact resolve eq20 eq1013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1013
  have eq2124 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1014 (τ X0) X1
       have i₂ := eq108 X0 X0
       grind)
    | exact superpose eq108 eq1014
    | (have j0 := eq1014 (τ X0) X1
       grind)
    | exact resolve eq1014 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq3422 : ∀ X0 X1 X2 : G, (k X0 (σ (k (τ X1) X2))) = (M.op (σ (τ X0)) (k X1 (σ X2))) ∨ (σ (τ X0)) = (M.op (k X1 (σ X2)) (k X1 (σ X2))) ∨ (k X1 (σ X2)) = (M.op (k X1 (σ X2)) (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X0 (k (τ X1) X2)
       have i₂ := eq183 X1 X2 (τ X0)
       grind)
    | exact superpose eq183 eq18
    | (have j1 := eq183 X1 X2 (τ X0)
       grind)
    | exact resolve eq18 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq3445 : ∀ X0 X1 X2 : G, (k X0 (σ (k (τ X1) X2))) = (M.op X0 (k X1 (σ X2))) ∨ (σ (τ X0)) = (M.op (k X1 (σ X2)) (k X1 (σ X2))) ∨ (k X1 (σ X2)) = (M.op (k X1 (σ X2)) (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3422 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3422
    | (have j0 := eq3422 X0 X1 X2
       grind)
    | exact resolve eq3422 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3422
  have eq3486 : ∀ X0 X1 X2 : G, (k X0 (k X1 (σ X2))) = (M.op X0 (k X1 (σ X2))) ∨ (σ (τ X0)) = (M.op (k X1 (σ X2)) (k X1 (σ X2))) ∨ (k X1 (σ X2)) = (M.op (k X1 (σ X2)) (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3445 X0 X1 X2
       have i₂ := eq18 X1 X2
       grind)
    | exact superpose eq18 eq3445
    | (have j0 := eq3445 X0 X1 X2
       grind)
    | exact resolve eq3445 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3445
  have eq3510 : ∀ X0 X1 X2 : G, (k X0 (k X1 (σ X2))) = (M.op X0 (k X1 (σ X2))) ∨ (σ (τ X0)) = (M.op (k X1 (σ X2)) (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq3486 X0 X1 X2
       have j1 := eq12 X0 (k X1 (σ X2))
       grind)
    | (have r₁ := eq3486 X0 X1 X2
       have r₂ := eq12 X0 (k X1 (σ X2))
       grind)
    | exact resolve eq3486 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3486
  have eq3535 : ∀ X0 X1 X2 : G, (k X0 (k X1 (σ X2))) = (M.op X0 (k X1 (σ X2))) ∨ (M.op (k X1 (σ X2)) (k X1 (σ X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3510 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3510
    | (have j0 := eq3510 X0 X1 X2
       grind)
    | exact resolve eq3510 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3510
  have eq6262 : ∀ X0 X1 X2 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X2 (σ (k X1 X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 X0 X1
       have i₂ := eq854 X1 X0 X2
       grind)
    | exact superpose eq854 eq64
    | (have j1 := eq854 X1 X1 X2
       grind)
    | exact resolve eq64 eq854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq854
  have eq7939 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = X1 ∨ (σ (k X0 X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq136 X1 (σ X0)
       have i₂ := eq263 X0
       grind)
    | exact superpose eq263 eq136
    | (have j1 := eq263 X0
       grind)
    | exact resolve eq136 eq263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263
  have eq7983 : ∀ X0 X1 : G, (σ (k X0 X0)) = (σ (k (k X0 X0) X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7939 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7939
    | (have j0 := eq7939 X0 X1
       grind)
    | exact resolve eq7939 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7939
  have eq23106 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3535 X0 X0 (σ (σ (σ (σ (σ (σ (M.op X1 X1)))))))
       have i₂ := eq428 X0 X1
       grind)
    | exact superpose eq428 eq3535
    | exact resolve eq3535 eq428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428 eq3535
  have eq24401 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X0)) ∨ (σ (k X0 X0)) = X1 ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq114 X0 X1
       have i₂ := eq45 X1 X1
       grind)
    | exact superpose eq45 eq114
    | (have j0 := eq114 (σ X0) X0
       have j1 := eq45 X0 X0
       grind)
    | exact resolve eq114 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq114
  have eq24448 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X0)) ∨ (σ (k X0 X0)) = X1 ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq24401 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24401
  have eq24449 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op X1 (σ X0))) ∨ (σ (k X0 X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq24448 X0 X1
       have j1 := eq201 X0
       grind)
    | (have r₁ := eq24448 X0 X1
       have r₂ := eq201 X0
       grind)
    | (have r₁ := eq24448 X0 (σ (k (k X0 X0) (k X0 X0)))
       have r₂ := eq201 (k X0 X0)
       grind)
    | (have r₁ := eq24448 X0 (σ X0)
       have r₂ := eq201 X0
       grind)
    | exact resolve eq24448 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201 eq24448
  have eq25702 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 (τ (σ X0))) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq70 (σ X0)
       have i₂ := eq653 X0 (σ X0) X0
       grind)
    | exact superpose eq653 eq70
    | (have j0 := eq70 (σ X0)
       have j1 := eq653 (k (k X0 (τ (σ X0))) X0) (σ X0) x
       grind)
    | exact resolve eq70 eq653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq653
  have eq25741 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 (τ (σ X0))) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq25702 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25702
  have eq25764 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq25741 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq25741
    | (have j0 := eq25741 X0
       grind)
    | exact resolve eq25741 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25741
  have eq127747 : ∀ X0 X1 : G, (τ (σ (k X0 X0))) = (k (k X0 X0) X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (k X0 X0) X0)
       have i₂ := eq7983 X0 X1
       grind)
    | exact superpose eq7983 eq10
    | (have j1 := eq7983 X0 X1
       grind)
    | exact resolve eq10 eq7983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7983
  have eq127980 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq127747 X0 X1
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq127747
    | (have j0 := eq127747 X0 (k X0 X0)
       grind)
    | exact resolve eq127747 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127747
  have eq128689 : ∀ X0 : G, (k X0 X0) ≠ (k X0 X0) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq127980 X0 (k X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127980
  have eq128690 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq128689 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128689
  have eq167911 : ∀ X0 X1 X2 : G, (k X1 (k (τ (σ X0)) X0)) = X1 ∨ (M.op X2 (σ (k X0 X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq136 X1 (σ X0)
       have i₂ := eq6262 (σ X0) X0 X2
       grind)
    | exact superpose eq6262 eq136
    | (have j1 := eq6262 X0 X0 X2
       grind)
    | exact resolve eq136 eq6262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6262
  have eq168133 : ∀ X0 X1 X2 : G, (M.op X2 (σ (k X0 X0))) = X2 ∨ (k X1 (k X0 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq167911 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq167911
    | (have j0 := eq167911 X0 X1 X2
       grind)
    | exact resolve eq167911 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167911
  have eq168349 : ∀ X0 X1 X2 : G, (k X1 (τ (σ (k X0 X0)))) = X1 ∨ (k X2 (k X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq136 X1 (σ (k X0 X0))
       have i₂ := eq168133 X0 X2 (σ (k X0 X0))
       grind)
    | exact superpose eq168133 eq136
    | (have j1 := eq168133 X0 X2 X2
       grind)
    | exact resolve eq136 eq168133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168133
  have eq168461 : ∀ X0 X1 X2 : G, (k X1 (k X0 X0)) = X1 ∨ (k X2 (k X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq168349 X0 X1 X2
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq168349
    | (have j0 := eq168349 X0 X1 X1
       grind)
    | exact resolve eq168349 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168349
  have eq169974 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (k X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq168461 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168461
  have eq169975 : ∀ X0 X1 : G, (k X0 (k X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq169974 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169974
  have eq170161 : ∀ X0 X1 : G, (σ (k X0 X0)) ≠ (σ (k X0 X0)) ∨ (M.op X1 (σ (k X0 X0))) = (k X1 (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq218 (k X0 X0) X1
       have i₂ := eq169975 (k X0 X0) X0
       grind)
    | exact superpose eq169975 eq218
    | (have j0 := eq218 (k X0 X0) X1
       grind)
    | exact resolve eq218 eq169975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq170178 : ∀ X0 X1 : G, (k X0 X0) ≠ (k X0 X0) ∨ (k X1 (k X0 X0)) = (M.op X1 (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1014 (k X0 X0) X1
       have i₂ := eq169975 (k X0 X0) X0
       grind)
    | exact superpose eq169975 eq1014
    | (have j0 := eq1014 (k X0 X0) X1
       grind)
    | (have r₁ := eq1014 (k X1 X1) X1
       have r₂ := eq169975 (k X1 X1) X1
       grind)
    | exact resolve eq1014 eq169975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1014
  have eq170189 : ∀ X0 X1 : G, (τ (k X0 X0)) ≠ (τ (k X0 X0)) ∨ (k X1 (τ (k X0 X0))) = (M.op X1 (τ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2124 (k X0 X0) X1
       have i₂ := eq169975 (k X0 X0) X0
       grind)
    | exact superpose eq169975 eq2124
    | (have j0 := eq2124 (k X0 X0) X1
       grind)
    | exact resolve eq2124 eq169975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2124
  have eq170478 : ∀ X0 X1 X2 : G, (k (σ X0) (σ X2)) = (σ (k (k X0 (τ (k X1 X1))) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq104 X0 (k X1 X1) X2
       have i₂ := eq169975 (σ X0) X1
       grind)
    | exact superpose eq169975 eq104
    | exact resolve eq104 eq169975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq170595 : ∀ X0 X1 : G, (k X1 (τ (k X0 X0))) = (M.op X1 (τ (k X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq170189 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170189
  have eq170596 : ∀ X0 X1 : G, (k X1 (k X0 X0)) = (M.op X1 (k X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq170178 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170178
  have eq170601 : ∀ X0 X1 : G, (M.op X1 (σ (k X0 X0))) = (k X1 (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq170161 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170161
  have eq170644 : ∀ X0 X1 X2 : G, (σ (k X0 X2)) = (σ (k (k X0 (τ (k X1 X1))) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq170478 X0 X1 X2
       have i₂ := eq15 X0 X2
       grind)
    | exact superpose eq15 eq170478
    | exact resolve eq170478 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170478
  have eq170661 : ∀ X0 X1 : G, (M.op X1 (k X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq170596 X0 X1
       have i₂ := eq169975 X1 X0
       grind)
    | exact superpose eq169975 eq170596
    | exact resolve eq170596 eq169975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169975 eq170596
  have eq170697 : ∀ X0 X1 X2 : G, (σ (k X0 X2)) = (σ (k (M.op X0 (τ (k X1 X1))) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq170644 X0 X1 X2
       have i₂ := eq170595 X1 X0
       grind)
    | exact superpose eq170595 eq170644
    | exact resolve eq170644 eq170595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170595 eq170644
  have eq171653 : ∀ X0 X1 : G, (M.op X1 (τ (k X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1022 (k X0 X0) X1
       have i₂ := eq170661 X0 (k X0 X0)
       grind)
    | exact superpose eq170661 eq1022
    | exact resolve eq1022 eq170661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1022 eq170661
  have eq206120 : ∀ X0 X1 X2 : G, (σ (k X0 X2)) = (σ (M.op (M.op X0 (τ (k X1 X1))) X2)) ∨ (M.op X2 X2) = (M.op X0 (τ (k X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq170697 X0 X1 X2
       have i₂ := eq23106 X2 (M.op X0 (τ (k X1 X1)))
       grind)
    | exact superpose eq23106 eq170697
    | (have j1 := eq23106 X2 (M.op X0 (τ (k X1 X1)))
       grind)
    | exact resolve eq170697 eq23106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23106 eq170697
  have eq207134 : ∀ X0 X1 X2 : G, (σ (k X0 X2)) = (σ (M.op X0 X2)) ∨ (M.op X2 X2) = (M.op X0 (τ (k X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq206120 X0 X1 X2
       have i₂ := eq171653 X1 X0
       grind)
    | exact superpose eq171653 eq206120
    | (have j0 := eq206120 X0 X1 X2
       grind)
    | exact resolve eq206120 eq171653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206120
  have eq207302 : ∀ X0 X2 : G, (σ (k X0 X2)) = (σ (M.op X0 X2)) ∨ (M.op X2 X2) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq207134 X0 x X2
       have i₂ := eq171653 x X0
       grind)
    | exact superpose eq171653 eq207134
    | (have j0 := eq207134 X0 x X2
       grind)
    | exact resolve eq207134 eq171653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171653 eq207134
  have eq286640 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = X1 ∨ (M.op (σ X0) (σ X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq136 X1 (σ X0)
       have i₂ := eq25764 X0
       grind)
    | exact superpose eq25764 eq136
    | (have j1 := eq25764 X0
       grind)
    | exact resolve eq136 eq25764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136 eq25764
  have eq286770 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op (σ X0) (σ X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq286640 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq286640
    | (have j0 := eq286640 X0 X1
       grind)
    | exact resolve eq286640 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286640
  have eq286844 : ∀ X0 X1 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq286770 X0 X1
       have i₂ := eq128690 X0
       grind)
    | exact superpose eq128690 eq286770
    | (have j0 := eq286770 X0 X1
       grind)
    | exact resolve eq286770 eq128690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128690 eq286770
  have eq286875 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq286844 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq286844
    | (have j0 := eq286844 (τ X0) X1
       grind)
    | exact resolve eq286844 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286844
  have eq287604 : ∀ X0 X1 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq286875 X0 X1
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq286875
    | (have j0 := eq286875 X0 X1
       grind)
    | exact resolve eq286875 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq286875
  have eq287666 : ∀ X0 X1 : G, (k X1 (τ X0)) = X1 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq287604 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq287604
    | (have j0 := eq287604 X0 X1
       grind)
    | exact resolve eq287604 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287604
  have eq288114 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X1 (σ (τ X0))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq170601 (τ X0) X1
       have i₂ := eq287666 X0 (τ X0)
       grind)
    | exact superpose eq287666 eq170601
    | (have j1 := eq287666 X0 X1
       grind)
    | exact resolve eq170601 eq287666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170601 eq287666
  have eq288423 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq288114 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq288114
    | (have j0 := eq288114 X0 X1
       grind)
    | exact resolve eq288114 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288114
  have eq299994 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq288423 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288423
  have eq299995 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq299994 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299994
  have eq479440 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 (σ X1))
       have i₂ := eq24449 X1 X0
       grind)
    | exact superpose eq24449 eq11
    | (have j1 := eq24449 X1 X0
       grind)
    | exact resolve eq11 eq24449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24449
  have eq479856 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq479440 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq479440
    | (have j0 := eq479440 X0 X1
       grind)
    | exact resolve eq479440 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq479440
  have eq480133 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq479856 X0 X1
       have j1 := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq479856 (M.op (σ (k X1 X1)) (σ (k X1 X1))) X1
       have r₂ := eq12 X0 (σ (k X1 X1))
       grind)
    | (have r₁ := eq479856 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq479856 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479856
  have eq480301 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq480133 X0 X1
       have i₂ := eq299995 X1
       grind)
    | exact superpose eq299995 eq480133
    | (have j0 := eq480133 X0 X1
       grind)
    | exact resolve eq480133 eq299995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299995 eq480133
  have eq481515 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq480301 (σ X0) X1
       grind)
    | exact superpose eq480301 eq15
    | (have j1 := eq480301 (σ X0) X1
       grind)
    | exact resolve eq15 eq480301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480301
  have eq907826 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq481515 x y
       grind)
    | exact superpose eq481515 eq16
    | (have j1 := eq481515 x y
       grind)
    | exact resolve eq16 eq481515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481515
  have eq911368 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq907826
       have i₂ := eq207302 x y
       grind)
    | exact superpose eq207302 eq907826
    | (have j1 := eq207302 x y
       grind)
    | (have r₁ := eq907826
       have r₂ := eq207302 x y
       grind)
    | exact resolve eq907826 eq207302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207302 eq907826
  have eq911370 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq911368
  have eq911471 : ∀ X0 : G, (σ x) = (σ (M.op y y)) ∨ x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq31 X0 y
       have i₂ := eq911370
       grind)
    | exact superpose eq911370 eq31
    | exact resolve eq31 eq911370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq911370
  have eq914010 : ∀ X0 : G, (M.op y y) = (τ (σ x)) ∨ x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq911471 X0
       grind)
    | exact superpose eq911471 eq10
    | (have j1 := eq911471 X0
       grind)
    | exact resolve eq10 eq911471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq911471
  have eq914801 : ∀ X0 : G, x = (M.op y y) ∨ x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq914010 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq914010
    | (have j0 := eq914010 X0
       grind)
    | exact resolve eq914010 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq914010
  have eq917148 : ∀ X0 X1 : G, (M.op X0 x) = X0 ∨ x = (M.op x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq21 y X0
       have i₂ := eq914801 X1
       grind)
    | exact superpose eq914801 eq21
    | (have j1 := eq914801 X1
       grind)
    | exact resolve eq21 eq914801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq914801
  have eq917567 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have j0 := eq917148 x x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917148
  have eq917568 : x = (M.op x x) := by grind
  clear eq917567
  have eq919596 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq31 X0 x
       have i₂ := eq917568
       grind)
    | exact superpose eq917568 eq31
    | exact resolve eq31 eq917568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq919632 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq1055 X0 x
       have i₂ := eq917568
       grind)
    | exact superpose eq917568 eq1055
    | exact resolve eq1055 eq917568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1055 eq917568
  have eq933254 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq919632 (σ y)
       grind)
    | exact superpose eq919632 eq16
    | exact resolve eq16 eq919632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq919632
  have eq933619 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq933254
       have i₂ := eq919596 y
       grind)
    | exact superpose eq919596 eq933254
    | exact resolve eq933254 eq919596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq919596 eq933254
  have eq933620 : False := by grind
  exact eq933620

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxx_pyx_pxy_Equation434 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law434 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
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
  have eq42 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 (M.op x x))
       have i₂ := eq9 X0 (M.op X0 (M.op x x)) x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq9 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq42 (M.op X1 X0) X0
       have i₂ := eq42 X0 X1
       grind)
    | exact superpose eq42 eq42
    | exact resolve eq42 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq42 (M.op X1 X1) X0
       have i₂ := eq43 X1 X0
       grind)
    | exact superpose eq43 eq42
    | exact resolve eq42 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq43
  have eq76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq81 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq53
    | exact resolve eq53 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq76 x y
       grind)
    | exact superpose eq76 eq16
    | (have j1 := eq76 x y
       grind)
    | exact resolve eq16 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq1574 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq105
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq105
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq105
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq105
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq105 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq1575 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq1574
  have eq15132 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1575
       grind)
    | exact superpose eq1575 eq16
    | exact resolve eq16 eq1575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1575
  have eq15133 : x = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq15132
       have r₂ := eq22 x
       grind)
    | exact resolve eq15132 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15132
  have eq43692 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq45 x y
       have i₂ := eq15133
       grind)
    | exact superpose eq15133 eq45
    | exact resolve eq45 eq15133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15133
  have eq52748 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq45 (σ x) (σ y)
       have i₂ := eq43692
       grind)
    | exact superpose eq43692 eq45
    | exact resolve eq45 eq43692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq43692
  have eq52758 : (σ x) = (σ y) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq52748
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq52748
    | exact resolve eq52748 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52748
  have eq53285 : y = (τ (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq52758
       grind)
    | exact superpose eq52758 eq10
    | exact resolve eq10 eq52758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52758
  have eq53377 : x = y ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq53285
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq53285
    | exact resolve eq53285 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53285
  have eq53379 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq53377
       grind)
    | exact superpose eq53377 eq16
    | exact resolve eq16 eq53377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53377
  have eq53380 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq53379
       have r₂ := eq22 x
       grind)
    | exact resolve eq53379 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq53379
  have eq54084 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq53380
       grind)
    | exact superpose eq53380 eq10
    | exact resolve eq10 eq53380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53380
  have eq54176 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq54084
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq54084
    | exact resolve eq54084 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54084
  have eq54177 : x = (M.op x x) := by grind
  clear eq54176
  have eq54182 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq53 X0 x
       have i₂ := eq54177
       grind)
    | exact superpose eq54177 eq53
    | exact resolve eq53 eq54177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq54183 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq81 x x
       have i₂ := eq54177
       grind)
    | exact superpose eq54177 eq81
    | exact resolve eq81 eq54177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq54177
  have eq57930 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq54183 (σ y)
       grind)
    | exact superpose eq54183 eq16
    | exact resolve eq16 eq54183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54183
  have eq58228 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq57930
       have i₂ := eq54182 y
       grind)
    | exact superpose eq54182 eq57930
    | exact resolve eq57930 eq54182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54182 eq57930
  have eq58229 : False := by grind
  exact eq58229

/-- `Equation4393`: `x ◇ (x ◇ x) = (y ◇ z) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else if m(Y,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_y_pxx_pxx_pyx_Equation4393 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4393 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4393.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X2) X2) := by
    intro X0 X1 X2
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
  have eq50 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op x y) y) := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq88 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq88
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq88
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq88 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq93
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq93
    | exact resolve eq93 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq99
    | exact resolve eq99 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq210 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq50 x
       have i₂ := eq14 x X0 X1
       grind)
    | exact superpose eq14 eq50
    | exact resolve eq50 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq51 x
       have i₂ := eq50 x
       grind)
    | exact superpose eq50 eq51
    | exact resolve eq51 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq350 : ∀ X1 : G, (M.op (M.op x y) y) = (M.op (M.op (M.op x y) y) X1) := by
    intro X1
    first
    | (have i₁ := eq210 (M.op x X1) X1
       have i₂ := eq210 x X1
       grind)
    | (have i₁ := eq210 (M.op x y) y
       have i₂ := eq210 x X1
       grind)
    | exact superpose eq210 eq210
    | exact resolve eq210 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq780 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq65 X0 X1
       grind)
    | exact superpose eq65 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq65 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq65 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X1)
       have r₂ := eq65 X1 X1
       grind)
    | exact resolve eq12 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq785 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq780 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780
  have eq790 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq785 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq785 X1 X1
       have r₂ := eq12 (σ X1) (σ X1)
       grind)
    | (have r₁ := eq785 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq785 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq785
  have eq802 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq790 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq790
    | (have j0 := eq790 X0 X1
       grind)
    | exact resolve eq790 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq790
  have eq6445 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq802
  have eq6560 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq6445 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6445
  have eq6561 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq6560 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6560
  have eq7004 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq6561 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq6561
    | (have j0 := eq6561 y
       grind)
    | exact resolve eq6561 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7010 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq50 (σ X0)
       have i₂ := eq6561 X0
       grind)
    | exact superpose eq6561 eq50
    | exact resolve eq50 eq6561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq7013 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq210 (σ X0) (σ X0)
       have i₂ := eq6561 X0
       grind)
    | exact superpose eq6561 eq210
    | exact resolve eq210 eq6561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7063 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq7004
       grind)
    | exact superpose eq7004 eq16
    | exact resolve eq16 eq7004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7004
  have eq7531 : (M.op (M.op x y) y) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by
    first
    | exact superpose eq350 eq7010
    | exact resolve eq7010 eq350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7010
  have eq7563 : (M.op (M.op x y) y) = (σ (M.op (M.op (M.op x y) y) (M.op (M.op x y) y))) := by
    first
    | (have i₁ := eq7531
       have i₂ := eq6561 (M.op sF0 y)
       grind)
    | exact superpose eq6561 eq7531
    | exact resolve eq7531 eq6561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6561 eq7531
  have eq7579 : (M.op (M.op x y) y) = (σ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq350 eq7563
    | exact resolve eq7563 eq350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7563
  have eq7587 : (M.op (M.op x y) y) = (τ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq7579 eq16
    | exact resolve eq16 eq7579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12249 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq101 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq12250 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq12249
    | exact resolve eq12249 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12249
  have eq12263 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq12250
       have r₂ := eq28
       grind)
    | exact resolve eq12250 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12250
  have eq12266 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq12263
    | exact resolve eq12263 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12263
  have eq12268 : (τ (σ x)) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq12266 eq7063
    | exact resolve eq7063 eq12266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7063 eq12266
  have eq12282 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq12268
    | exact resolve eq12268 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12268
  have eq12283 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq12282
  have eq12296 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7013 y
       have i₂ := eq12283
       grind)
    | exact superpose eq12283 eq7013
    | exact resolve eq7013 eq12283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7013
  have eq12299 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq210 y y
       have i₂ := eq12283
       grind)
    | exact superpose eq12283 eq210
    | exact resolve eq210 eq12283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210 eq12283
  have eq12303 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12299
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12299
    | exact resolve eq12299 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12299
  have eq12304 : (M.op (M.op x y) y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12296
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq12296
    | exact resolve eq12296 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq12296
  have eq12312 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12304
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq12304
    | exact resolve eq12304 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12304
  have eq12314 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq12312
    | exact resolve eq12312 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12312
  have eq12523 : (M.op x y) = (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12303 eq7579
    | exact resolve eq7579 eq12303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12531 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq12523
    | exact resolve eq12523 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12523
  have eq12533 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12531 eq215
    | exact resolve eq215 eq12531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12536 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq12533
    | exact resolve eq12533 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12533
  have eq12756 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12314 eq12303
    | exact resolve eq12303 eq12314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12303 eq12314
  have eq12762 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq12756
  have eq12768 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12762 eq215
    | exact resolve eq215 eq12762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq12770 : (M.op x y) ≠ (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  have eq12772 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq12768
    | exact resolve eq12768 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12768
  have eq13807 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq12536 eq350
    | exact resolve eq350 eq12536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13815 : (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12536 eq7587
    | exact resolve eq7587 eq12536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12536
  have eq14039 : (σ x) = (τ (σ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12531 eq13815
    | exact resolve eq13815 eq12531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13815
  have eq14073 : (σ x) = (τ (σ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq14039
  have eq14075 : (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq14073
    | exact resolve eq14073 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14073
  have eq14545 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq12772 eq350
    | exact resolve eq350 eq12772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14553 : (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12772 eq7587
    | exact resolve eq7587 eq12772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7587 eq12772
  have eq14634 : (σ x) = (τ (σ x)) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12762 eq14553
    | exact resolve eq14553 eq12762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14553
  have eq14670 : (σ x) = (τ (σ x)) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq14634
  have eq14672 : (σ x) = (τ (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq14670
       have r₂ := eq12770
       grind)
    | exact resolve eq14670 eq12770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14670
  have eq14673 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (σ x) := by
    first
    | exact superpose eq29 eq14672
    | exact resolve eq14672 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq14672
  have eq14677 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = (σ x) := by
    first
    | exact superpose eq14673 eq28
    | exact resolve eq28 eq14673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14673
  have eq14697 : x = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq14677
       have r₂ := eq14075
       grind)
    | exact resolve eq14677 eq14075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14075 eq14677
  have eq15103 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq12531 eq13807
    | exact resolve eq13807 eq12531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12531 eq13807
  have eq15119 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq15103 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15103
  have eq15166 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq12762 eq14545
    | exact resolve eq14545 eq12762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12762 eq14545
  have eq15184 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq15166 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15166
  have eq15191 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq15184 X0
       grind)
    | (have r₁ := eq15184 X0
       have r₂ := eq12770
       grind)
    | exact resolve eq15184 eq12770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12770 eq15184
  have eq15229 : ∀ X0 : G, x = (M.op x X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq14697 eq15119
    | exact resolve eq15119 eq14697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15119
  have eq15251 : ∀ X0 : G, x = (M.op x X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq15229 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15229
  have eq15324 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq14697 eq15191
    | exact resolve eq15191 eq14697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14697 eq15191
  have eq15346 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq15324 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15324
  have eq16086 : x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19
       have i₂ := eq15251 y
       grind)
    | exact superpose eq15251 eq19
    | (have j1 := eq15251 y
       grind)
    | exact resolve eq19 eq15251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15251
  have eq16101 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq16086
  have eq17334 : x = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19
       have i₂ := eq15346 y
       grind)
    | exact superpose eq15346 eq19
    | (have j1 := eq15346 y
       grind)
    | exact resolve eq19 eq15346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15346
  have eq17349 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq17334
  have eq17368 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17349 eq28
    | exact resolve eq28 eq17349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17349
  have eq17392 : x = (M.op x y) := by
    first
    | (have r₁ := eq17368
       have r₂ := eq16101
       grind)
    | exact resolve eq17368 eq16101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16101 eq17368
  have eq17393 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq17392 eq21
    | exact resolve eq21 eq17392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17446 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq17392 eq350
    | exact resolve eq350 eq17392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350
  have eq17460 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq17392 eq7579
    | exact resolve eq7579 eq17392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7579
  have eq17464 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq17460
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq17460
    | exact resolve eq17460 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17460
  have eq17478 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq17446 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq17446
    | (have j0 := eq17446 X0
       grind)
    | exact resolve eq17446 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq17446
  have eq17530 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq17393
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq17393
    | exact resolve eq17393 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq17393
  have eq17532 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq21 eq17464
    | exact resolve eq17464 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq17464
  have eq17540 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq17392 eq17478
    | exact resolve eq17478 eq17392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17478
  have eq17543 : x = (σ (M.op x y)) := by
    first
    | exact superpose eq17392 eq17532
    | exact resolve eq17532 eq17392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17392 eq17532
  have eq17553 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq17530 eq27
    | exact resolve eq27 eq17530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq17530
  have eq18258 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq17543 eq17553
    | exact resolve eq17553 eq17543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17553
  have eq18259 : x = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18258
       have i₂ := eq17540 sF3
       grind)
    | exact superpose eq17540 eq18258
    | exact resolve eq18258 eq17540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17540 eq18258
  have eq18264 : x ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq18259 eq28
    | exact resolve eq28 eq18259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq18259
  have eq18294 : False := by grind
  exact eq18294

/-- `Equation4401`: `x ◇ (x ◇ y) = (x ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(X,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_y_pyx_pxx_pyx_Equation4401 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4401 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4401.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X2) X0) := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X0
       have r₂ := eq13 X0 X1
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
  have eq73 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 y)
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq15
    | exact resolve eq15 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq73 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq73
    | exact resolve eq73 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq177 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 X3) X0) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq16 X0 x X3
       have i₂ := eq16 X0 x X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) X0 (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 x
       have i₂ := eq16 X0 X2 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 X2 : G, (M.op X0 X2) ≠ (M.op (M.op X0 X1) X0) ∨ (M.op (M.op X0 X1) X0) = (k (M.op X0 X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X0 X1) X0
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq13
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) ≠ X0 ∨ (M.op X0 (M.op X0 X1)) = (k X0 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op X0 X2)
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq13
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : y ≠ (M.op x y) ∨ (M.op x y) = (k y x) := by
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
  have eq186 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq201 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq181
    | (have j0 := eq181 (σ y)
       grind)
    | exact resolve eq181 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq837 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (M.op (k X0 X1) X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X2 X0
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq856 : (M.op x y) = (k y x) ∨ x = (M.op y x) := by
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
  have eq868 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
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
  have eq872 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq916 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq28 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq28 X0 X1
       grind)
    | exact resolve eq12 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq935 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq916 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq916
  have eq965 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq856
       grind)
    | exact superpose eq856 eq40
    | exact resolve eq40 eq856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856
  have eq966 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq965
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq965
    | exact resolve eq965 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq965
  have eq968 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq966
    | exact resolve eq966 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq966
  have eq978 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq968 eq868
    | exact resolve eq868 eq968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq985 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq978
       have r₂ := eq27
       grind)
    | exact resolve eq978 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq978
  have eq990 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq985 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq985
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq985
       grind)
    | exact resolve eq12 eq985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq991 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq985 eq13
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq985
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq985
       grind)
    | exact resolve eq13 eq985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq992 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ y) X0)) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq985 eq16
    | exact resolve eq16 eq985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq997 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (σ y) (M.op (σ y) X0)) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq985 eq182
    | exact resolve eq182 eq985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq998 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq991
  have eq999 : (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq990
  have eq1000 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op (σ y) X0)) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq985 eq997
    | exact resolve eq997 eq985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq985 eq997
  have eq1005 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ y) X0)) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq26 eq992
    | (have j0 := eq992 X0
       grind)
    | exact resolve eq992 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq992
  have eq1006 : (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq999
    | exact resolve eq999 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq999
  have eq1007 : x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1000 eq1005
    | exact resolve eq1005 eq1000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1005
  have eq1008 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq968 eq1006
    | exact resolve eq1006 eq968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq968 eq1006
  have eq1009 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1007 eq1008
    | exact resolve eq1008 eq1007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1008
  have eq1011 : x ≠ x ∨ y = (M.op x y) ∨ (k y x) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq1007
       grind)
    | exact superpose eq1007 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq1007
       grind)
    | exact resolve eq12 eq1007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1012 : x ≠ x ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq1007
       grind)
    | exact superpose eq1007 eq13
    | (have r₁ := eq13 x y
       have r₂ := eq1007
       grind)
    | exact resolve eq13 eq1007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1013 : ∀ X0 : G, (M.op x y) = (M.op y (M.op y X0)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16 y X0 x
       have i₂ := eq1007
       grind)
    | exact superpose eq1007 eq16
    | exact resolve eq16 eq1007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1016 : ∀ X0 : G, (M.op x y) = (M.op (M.op y X0) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq177 y X0 x
       have i₂ := eq1007
       grind)
    | exact superpose eq1007 eq177
    | exact resolve eq177 eq1007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1018 : ∀ X0 : G, (M.op y x) = (M.op y (M.op y X0)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq182 y X0 x
       have i₂ := eq1007
       grind)
    | exact superpose eq1007 eq182
    | exact resolve eq182 eq1007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1019 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1012
  have eq1020 : y = (M.op x y) ∨ (k y x) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1011
  have eq1021 : ∀ X0 : G, x = (M.op y (M.op y X0)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1007 eq1018
    | exact resolve eq1018 eq1007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1007 eq1018
  have eq1023 : ∀ X0 : G, (M.op x y) = (M.op (M.op y X0) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1016 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1016
    | (have j0 := eq1016 X0
       grind)
    | exact resolve eq1016 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1016
  have eq1026 : ∀ X0 : G, (M.op x y) = (M.op y (M.op y X0)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1013 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1013
    | (have j0 := eq1013 X0
       grind)
    | exact resolve eq1013 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1013
  have eq1027 : (k y x) = (M.op y y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1020
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1020
    | exact resolve eq1020 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1020
  have eq1029 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq1019
       grind)
    | exact superpose eq1019 eq41
    | exact resolve eq41 eq1019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1019
  have eq1030 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1029
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1029
    | exact resolve eq1029 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1029
  have eq1042 : (τ (σ x)) = (k (τ (σ x)) y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq998 eq153
    | exact resolve eq153 eq998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq998
  have eq1043 : x = (k x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq30 eq1042
    | exact resolve eq1042 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1042
  have eq1051 : ∀ X0 : G, x = (M.op y (M.op (M.op y X0) y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1021 (M.op y x)
       have i₂ := eq16 y x X0
       grind)
    | exact superpose eq16 eq1021
    | exact resolve eq1021 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1059 : ∀ X1 : G, x = (M.op (M.op y X1) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | (have i₁ := eq16 y x X1
       have i₂ := eq1021 x
       grind)
    | exact superpose eq1021 eq16
    | exact resolve eq16 eq1021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1064 : ∀ X0 : G, x = (k (M.op y X0) y) ∨ y = (M.op (M.op y X0) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq28 (M.op y X0) y
       have i₂ := eq1021 X0
       grind)
    | exact superpose eq1021 eq28
    | (have j0 := eq28 (M.op y X0) y
       grind)
    | exact resolve eq28 eq1021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1075 : ∀ X0 : G, x = (k (M.op y X0) y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1023 eq1064
    | (have j0 := eq1064 X0
       grind)
    | exact resolve eq1064 eq1023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1064
  have eq1079 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1023 eq1059
    | exact resolve eq1059 eq1023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1059
  have eq1082 : x = (M.op y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1023 eq1051
    | exact resolve eq1051 eq1023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1051
  have eq1085 : (M.op x y) = (M.op y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1079 eq1082
    | exact resolve eq1082 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1082
  have eq1091 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1079 eq27
    | exact resolve eq27 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1101 : ∀ X0 : G, (M.op (M.op y X0) y) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1085 eq177
    | exact resolve eq177 eq1085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq1085
  have eq1109 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1023 eq1101
    | exact resolve eq1101 eq1023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1101
  have eq1192 : ∀ X0 : G, (M.op x y) = (k (M.op y X0) y) ∨ y = (M.op (M.op y X0) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq28 (M.op y X0) y
       have i₂ := eq1026 X0
       grind)
    | exact superpose eq1026 eq28
    | (have j0 := eq28 (M.op y X0) y
       grind)
    | exact resolve eq28 eq1026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1026
  have eq1209 : ∀ X0 : G, (M.op x y) = (k (M.op y X0) y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1023 eq1192
    | (have j0 := eq1192 X0
       grind)
    | exact resolve eq1192 eq1023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1023 eq1192
  have eq1239 : ∀ X1 : G, (σ x) = (M.op (M.op (σ y) X1) (σ y)) ∨ x = (M.op y x) := by
    intro X1
    first
    | exact superpose eq1000 eq16
    | exact resolve eq16 eq1000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1388 : (σ x) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op y x) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1009 eq1239
    | exact resolve eq1239 eq1009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1239
  have eq1390 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op y x) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1009 eq1000
    | exact resolve eq1000 eq1009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1000 eq1009
  have eq1399 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq1390
  have eq1401 : (σ x) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq1388
  have eq1909 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1399 eq28
    | (have j0 := eq28 (σ (M.op x y)) (σ y)
       grind)
    | exact resolve eq28 eq1399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1399
  have eq1925 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1401 eq1909
    | exact resolve eq1909 eq1401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1401 eq1909
  have eq1926 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by grind
  clear eq1925
  have eq1951 : x = (k (k y x) y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1075 y
       have i₂ := eq1027
       grind)
    | exact superpose eq1027 eq1075
    | exact resolve eq1075 eq1027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1027
  have eq1959 : ∀ X0 : G, (σ x) = (k (σ (M.op y X0)) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq41 (M.op y X0)
       have i₂ := eq1075 X0
       grind)
    | exact superpose eq1075 eq41
    | exact resolve eq41 eq1075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1075
  have eq1961 : x = (k (k y x) y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1951
  have eq1965 : ∀ X0 : G, (σ x) = (k (σ (M.op y X0)) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1959 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1959
    | (have j0 := eq1959 X0
       grind)
    | exact resolve eq1959 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1959
  have eq1971 : (M.op x y) = (k (k y (M.op x y)) y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1079 eq1961
    | exact resolve eq1961 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1961
  have eq1990 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op y X0)) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq41 (M.op y X0)
       have i₂ := eq1209 X0
       grind)
    | exact superpose eq1209 eq41
    | exact resolve eq41 eq1209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1209
  have eq1998 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op y X0)) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq20 eq1990
    | (have j0 := eq1990 X0
       grind)
    | exact resolve eq1990 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1990
  have eq2005 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1965 eq1998
    | exact resolve eq1998 eq1965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1965 eq1998
  have eq2124 : (σ (M.op x y)) = (k (σ (k y (M.op x y))) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1971 eq41
    | exact resolve eq41 eq1971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1971
  have eq2125 : (σ (M.op x y)) = (k (k (σ y) (σ (M.op x y))) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq42 eq2124
    | exact resolve eq2124 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2124
  have eq2126 : (σ (M.op x y)) = (k (k (σ y) (σ (M.op x y))) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2125
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2125
    | exact resolve eq2125 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2125
  have eq2127 : (σ (M.op x y)) = (k (k (σ y) (σ (M.op x y))) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq2126
    | exact resolve eq2126 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2126
  have eq2128 : (σ x) = (k (k (σ y) (σ x)) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2005 eq2127
    | exact resolve eq2127 eq2005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2005 eq2127
  have eq2154 : (σ x) = (k (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq868 eq2128
    | exact resolve eq2128 eq868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2128
  have eq3533 : ∀ X0 : G, (M.op x y) = (M.op y (M.op y X0)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq837 x y X0
       have i₂ := eq1043
       grind)
    | exact superpose eq1043 eq837
    | (have j0 := eq837 x y x
       grind)
    | exact resolve eq837 eq1043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3548 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1030 eq837
    | (have j0 := eq837 (σ x) (σ y) x
       grind)
    | exact resolve eq837 eq1030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq837 eq1030
  have eq3671 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq3548
    | (have j0 := eq3548 X0
       grind)
    | exact resolve eq3548 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3548
  have eq3682 : ∀ X0 : G, (M.op x y) = (M.op y (M.op y X0)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq3533 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3533
    | (have j0 := eq3533 X0
       grind)
    | exact resolve eq3533 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3533
  have eq3721 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq3671
    | (have j0 := eq3671 X0
       grind)
    | exact resolve eq3671 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3671
  have eq3729 : ∀ X0 : G, (M.op x y) = (M.op y (M.op y X0)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq3682 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3682
    | (have j0 := eq3682 X0
       grind)
    | exact resolve eq3682 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3682
  have eq3759 : x ≠ x ∨ y = (M.op x y) ∨ (k y x) = (M.op y y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq935 x y
       have i₂ := eq1043
       grind)
    | exact superpose eq1043 eq935
    | (have j0 := eq935 x y
       grind)
    | (have r₁ := eq935 x y
       have r₂ := eq1043
       grind)
    | exact resolve eq935 eq1043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3796 : y = (M.op x y) ∨ (k y x) = (M.op y y) ∨ x = (M.op y x) := by grind
  clear eq3759
  have eq3808 : y = (M.op x y) ∨ (k y x) = (M.op y y) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq3796
       have r₂ := eq12 x y
       grind)
    | (have r₁ := eq3796
       have r₂ := eq12 y x
       grind)
    | exact resolve eq3796 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3796
  have eq3820 : (k y x) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3808
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3808
    | exact resolve eq3808 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3808
  have eq3851 : y ≠ (k y x) ∨ (k y x) = (k y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq3820
       grind)
    | exact superpose eq3820 eq13
    | (have r₁ := eq13 y x
       have r₂ := eq3820
       grind)
    | exact resolve eq13 eq3820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3853 : (k y x) = (k y y) ∨ y = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq28 y y
       have i₂ := eq3820
       grind)
    | exact superpose eq3820 eq28
    | (have j0 := eq28 x y
       grind)
    | exact resolve eq28 eq3820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq3859 : ∀ X0 : G, (M.op y (M.op y X0)) = (M.op y (k y x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq182 y X0 y
       have i₂ := eq3820
       grind)
    | exact superpose eq3820 eq182
    | exact resolve eq182 eq3820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3820
  have eq3867 : (k y x) = (k y y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq3851
       have r₂ := eq3853
       grind)
    | exact resolve eq3851 eq3853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3851 eq3853
  have eq3896 : (σ (k y x)) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq3867
       grind)
    | exact superpose eq3867 eq41
    | exact resolve eq41 eq3867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3867
  have eq3903 : (σ (k y x)) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3896
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3896
    | exact resolve eq3896 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3896
  have eq3908 : (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3903
       have i₂ := eq40 y
       grind)
    | exact superpose eq40 eq3903
    | exact resolve eq3903 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3903
  have eq3913 : (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3908
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3908
    | exact resolve eq3908 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3908
  have eq3938 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3721 eq3721
    | exact resolve eq3721 eq3721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3988 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3938
  have eq4012 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3988 eq13
    | (have r₁ := eq13 (M.op (σ x) (σ y)) (σ y)
       have r₂ := eq3988
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq3988
       grind)
    | exact resolve eq13 eq3988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3988
  have eq4022 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4012
  have eq4051 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4022 eq2154
    | exact resolve eq2154 eq4022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4022
  have eq4058 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq4051
  have eq4477 : ∀ X1 : G, (M.op (M.op y X1) y) = (M.op y (k y x)) ∨ y = (M.op x y) := by
    intro X1
    first
    | (have i₁ := eq16 y x X1
       have i₂ := eq3859 x
       grind)
    | exact superpose eq3859 eq16
    | exact resolve eq16 eq3859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4647 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4058 eq3721
    | exact resolve eq3721 eq4058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3721
  have eq4663 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq4647
  have eq4673 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4058 eq4663
    | exact resolve eq4663 eq4058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4058 eq4663
  have eq4674 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq4673
  have eq4681 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4674 eq186
    | (have r₁ := eq186
       have r₂ := eq4674
       grind)
    | exact resolve eq186 eq4674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq4682 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4674 eq201
    | exact resolve eq201 eq4674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq4688 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4674 eq2154
    | exact resolve eq2154 eq4674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2154
  have eq4689 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  have eq4690 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4688
  have eq4693 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq4681
  have eq4694 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq4690
       have r₂ := eq4689
       grind)
    | exact resolve eq4690 eq4689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4690
  have eq4698 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq4682
    | exact resolve eq4682 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4682
  have eq4700 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3913 eq4694
    | exact resolve eq4694 eq3913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3913 eq4694
  have eq4702 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4674 eq4698
    | exact resolve eq4698 eq4674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4674 eq4698
  have eq4703 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4693 eq4700
    | exact resolve eq4700 eq4693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4693 eq4700
  have eq4704 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq4703
       have r₂ := eq4689
       grind)
    | exact resolve eq4703 eq4689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4703
  have eq4777 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4704 eq4702
    | exact resolve eq4702 eq4704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4702 eq4704
  have eq4800 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq4777
  have eq4811 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq4800
       have r₂ := eq4689
       grind)
    | exact resolve eq4800 eq4689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4689 eq4800
  have eq4904 : ∀ X1 : G, x ≠ y ∨ x = (k y (M.op y X1)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | (have i₁ := eq184 y x x
       have i₂ := eq1021 x
       grind)
    | exact superpose eq1021 eq184
    | exact resolve eq184 eq1021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184 eq1021
  have eq4917 : ∀ X1 : G, y ≠ (M.op x y) ∨ x = (k y (M.op y X1)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | exact superpose eq1079 eq4904
    | (have j0 := eq4904 X1
       grind)
    | exact resolve eq4904 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4904
  have eq4963 : ∀ X1 : G, x = (k y (M.op y X1)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | (have j0 := eq4917 X1
       grind)
    | (have r₁ := eq4917 X1
       have r₂ := eq4811
       grind)
    | exact resolve eq4917 eq4811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4917
  have eq4994 : ∀ X1 : G, (M.op x y) = (k y (M.op y X1)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | exact superpose eq1079 eq4963
    | exact resolve eq4963 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4963
  have eq5017 : ∀ X1 : G, (M.op x y) = (k (M.op x y) (M.op (M.op x y) X1)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | exact superpose eq4811 eq4994
    | exact resolve eq4994 eq4811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4994
  have eq5402 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4811 eq27
    | exact resolve eq27 eq4811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4811
  have eq5410 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1109 eq5017
    | exact resolve eq5017 eq1109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1109 eq5017
  have eq5425 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq5410
  have eq5437 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5425 eq42
    | exact resolve eq42 eq5425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq5425
  have eq5444 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq5437
    | exact resolve eq5437 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5437
  have eq5471 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5444 eq935
    | (have j0 := eq935 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq935 (σ (M.op x y)) (σ (M.op x y))
       have r₂ := eq5444
       grind)
    | exact resolve eq935 eq5444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq935 eq5444
  have eq5473 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq5471
  have eq5474 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq5473
  have eq7274 : ∀ X1 : G, (M.op x y) = (M.op (M.op y X1) y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    intro X1
    first
    | (have i₁ := eq16 y x X1
       have i₂ := eq3729 x
       grind)
    | exact superpose eq3729 eq16
    | exact resolve eq16 eq3729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7999 : ∀ X1 : G, (M.op x y) ≠ (M.op (M.op y X1) y) ∨ (k (M.op x y) y) = (M.op (M.op y X1) y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    intro X1
    first
    | (have i₁ := eq183 y X1 (M.op y x)
       have i₂ := eq3729 x
       grind)
    | exact superpose eq3729 eq183
    | exact resolve eq183 eq3729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq3729
  have eq8192 : ∀ X1 : G, (k (M.op x y) y) = (M.op (M.op y X1) y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    intro X1
    first
    | (have j0 := eq7999 X1
       grind)
    | (have r₁ := eq7999 X1
       have r₂ := eq7274 X1
       grind)
    | exact resolve eq7999 eq7274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7999
  have eq8249 : (M.op x y) = (k (M.op x y) y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq7274 eq8192
    | exact resolve eq8192 eq7274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7274 eq8192
  have eq8406 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq8249 eq41
    | exact resolve eq41 eq8249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq8249
  have eq8413 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq8406
    | exact resolve eq8406 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8406
  have eq8417 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq8413 eq1926
    | exact resolve eq1926 eq8413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1926 eq8413
  have eq8428 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq8417
  have eq8436 : x = (M.op y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq8428
       have r₂ := eq5402
       grind)
    | exact resolve eq8428 eq5402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8428
  have eq8452 : (M.op y x) = (M.op y (k y x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3859 x
       have i₂ := eq8436
       grind)
    | exact superpose eq8436 eq3859
    | exact resolve eq3859 eq8436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3859
  have eq8453 : (M.op x y) = (M.op y (k y x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4477 x
       have i₂ := eq8436
       grind)
    | exact superpose eq8436 eq4477
    | exact resolve eq4477 eq8436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4477
  have eq8473 : (M.op x y) = (M.op y (k y x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq8453
  have eq8474 : (M.op y x) = (M.op y (k y x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq8452
  have eq8496 : (M.op x y) = (M.op y (k y x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq8473
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq8473
    | exact resolve eq8473 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8473
  have eq8497 : x = (M.op y (k y x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq8436 eq8474
    | exact resolve eq8474 eq8436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8436 eq8474
  have eq8507 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8496 eq8497
    | exact resolve eq8497 eq8496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8496 eq8497
  have eq8510 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8507 eq32
    | exact resolve eq32 eq8507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq8507
  have eq8617 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq8510
    | exact resolve eq8510 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq8510
  have eq8631 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq8617
       grind)
    | exact superpose eq8617 eq24
    | exact resolve eq24 eq8617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8634 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq185
       have i₂ := eq8617
       grind)
    | exact superpose eq8617 eq185
    | (have r₁ := eq185
       have r₂ := eq8617
       grind)
    | exact resolve eq185 eq8617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185 eq8617
  have eq8670 : (M.op x y) = (k (M.op x y) x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq8634
  have eq8682 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq8631
    | exact resolve eq8631 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8631
  have eq8698 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq8682 eq1091
    | exact resolve eq1091 eq8682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1091
  have eq8727 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq8698
  have eq9091 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq8670 eq40
    | exact resolve eq40 eq8670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq8670
  have eq9096 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq9091
    | exact resolve eq9091 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9091
  have eq9098 : (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq8682 eq9096
    | exact resolve eq9096 eq8682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8682 eq9096
  have eq9233 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq9098 eq868
    | exact resolve eq868 eq9098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq868
  have eq9252 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq1079 eq9233
    | exact resolve eq9233 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9233
  have eq9258 : (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq9252
       have r₂ := eq8727
       grind)
    | exact resolve eq9252 eq8727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9252
  have eq9288 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq9258 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq9258
       grind)
    | exact resolve eq12 eq9258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9300 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (σ y) (M.op (σ y) X0)) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq9258 eq182
    | exact resolve eq182 eq9258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9306 : (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq9288
  have eq9313 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op (σ y) X0)) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq9258 eq9300
    | exact resolve eq9300 eq9258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9258 eq9300
  have eq9324 : (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq9306
    | exact resolve eq9306 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9306
  have eq9337 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq9098 eq9324
    | exact resolve eq9324 eq9098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9098 eq9324
  have eq9343 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq1079 eq9337
    | exact resolve eq9337 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1079 eq9337
  have eq9347 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq9343
       have r₂ := eq8727
       grind)
    | exact resolve eq9343 eq8727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9343
  have eq10435 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ y) X0)) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq9347 eq182
    | exact resolve eq182 eq9347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq10450 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq9313 eq10435
    | exact resolve eq10435 eq9313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9313 eq10435
  have eq10513 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq10450 eq9347
    | exact resolve eq9347 eq10450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9347 eq10450
  have eq10545 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq10513
  have eq10567 : x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq10545
       have r₂ := eq8727
       grind)
    | exact resolve eq10545 eq8727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8727 eq10545
  have eq10585 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq22
       have i₂ := eq10567
       grind)
    | exact superpose eq10567 eq22
    | exact resolve eq22 eq10567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10604 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq20 eq10585
    | exact resolve eq10585 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10585
  have eq10630 : (σ x) ≠ (σ x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq10604 eq5402
    | (have r₁ := eq5402
       have r₂ := eq10604
       grind)
    | exact resolve eq5402 eq10604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5402 eq10604
  have eq10646 : y = (M.op x y) ∨ x = y := by grind
  clear eq10630
  have eq10729 : x ≠ (M.op x y) ∨ x = y := by grind
  clear eq10646
  have eq10735 : x = y := by
    first
    | (have r₁ := eq10729
       have r₂ := eq10567
       grind)
    | exact resolve eq10729 eq10567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10567 eq10729
  have eq10760 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq10735
       grind)
    | exact superpose eq10735 eq18
    | exact resolve eq18 eq10735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq10761 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq10735
       grind)
    | exact superpose eq10735 eq24
    | exact resolve eq24 eq10735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq10773 : x = (k x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1043
       have i₂ := eq10735
       grind)
    | exact superpose eq10735 eq1043
    | exact resolve eq1043 eq10735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1043 eq10735
  have eq10854 : x = (M.op x x) := by
    first
    | (have j1 := eq872 x
       grind)
    | (have r₁ := eq10773
       have r₂ := eq872 x
       grind)
    | exact resolve eq10773 eq872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq872 eq10773
  have eq10862 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq10761
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10761
    | exact resolve eq10761 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10761
  have eq10880 : x = (M.op x y) := by
    first
    | (have i₁ := eq10854
       have i₂ := eq10760
       grind)
    | exact superpose eq10760 eq10854
    | exact resolve eq10854 eq10760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10760 eq10854
  have eq10887 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq10862 eq26
    | exact resolve eq26 eq10862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq10862
  have eq11066 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq10880
       grind)
    | exact superpose eq10880 eq22
    | exact resolve eq22 eq10880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq10880
  have eq11105 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq11066 eq20
    | exact resolve eq20 eq11066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq11066
  have eq11159 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11105 eq5474
    | exact resolve eq5474 eq11105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5474
  have eq11178 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10887 eq11159
    | exact resolve eq11159 eq10887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10887 eq11159
  have eq11179 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq11178
  have eq11254 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq11179 eq27
    | exact resolve eq27 eq11179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq11179
  have eq11263 : False := by grind
  exact eq11263

/-- `Equation4410`: `x ◇ (x ◇ y) = (y ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_y_x_x_pyx_Equation4410 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4410 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4410.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X1) X2) := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X1 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X1
       have r₂ := eq13 X0 (k (M.op X0 X0) X1)
       grind)
    | exact resolve eq12 eq13
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
  have eq35 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq39 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq10
    | exact resolve eq10 eq14
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
  have eq43 : ∀ X0 X1 : G, (σ (k X1 (k x X0))) = (k (σ X1) (k (σ x) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (k x X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq10
    | exact resolve eq10 eq36
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
  have eq91 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq45 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq45
    | exact resolve eq45 eq14
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
  clear eq48
  have eq175 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : (τ (σ x)) = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq91 (M.op sF2 sF2)
       have i₂ := eq175 sF2
       grind)
    | exact superpose eq175 eq91
    | exact resolve eq91 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq200 : x = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | exact superpose eq30 eq189
    | exact resolve eq189 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq207 : (τ (σ y)) = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | (have i₁ := eq108 (M.op sF3 sF3)
       have i₂ := eq175 sF3
       grind)
    | exact superpose eq175 eq108
    | exact resolve eq108 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq218 : y = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq32 eq207
    | exact resolve eq207 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq690 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X0) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq16 x X0 X3
       have i₂ := eq16 x X0 X1
       grind)
    | (have i₁ := eq16 (M.op X1 X1) X1 x
       have i₂ := eq16 X0 X1 (M.op (M.op X1 X1) X1)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq693 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 x
       have i₂ := eq16 X2 X1 x
       grind)
    | (have i₁ := eq16 X0 X1 (M.op (M.op X1 X1) X1)
       have i₂ := eq16 (M.op X1 X1) X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq743 : ∀ X0 : G, (M.op X0 (M.op X0 y)) = (M.op x (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq693 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq693
    | (have j0 := eq693 X0 y x
       grind)
    | exact resolve eq693 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq744 : ∀ X0 : G, (M.op X0 (M.op X0 (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq693
    | (have j0 := eq693 X0 (σ y) (σ x)
       grind)
    | exact resolve eq693 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693
  have eq775 : ∀ X0 X1 : G, (M.op X0 (M.op x (M.op x y))) = (M.op (M.op (M.op X0 y) (M.op X0 y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 (M.op X0 y) X1
       have i₂ := eq743 X0
       grind)
    | (have i₁ := eq16 x (M.op x y) x
       have i₂ := eq743 X0
       grind)
    | exact superpose eq743 eq16
    | exact resolve eq16 eq743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq777 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq690 X0 (M.op (M.op X0 X0) y) X1
       have i₂ := eq743 (M.op X0 X0)
       grind)
    | exact superpose eq743 eq690
    | exact resolve eq690 eq743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq778 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 (M.op (M.op X1 X1) y)
       have i₂ := eq743 (M.op X1 X1)
       grind)
    | exact superpose eq743 eq16
    | exact resolve eq16 eq743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743
  have eq779 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq775 X0 x
       have i₂ := eq777 (M.op X0 y) x
       grind)
    | exact superpose eq777 eq775
    | exact resolve eq775 eq777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775
  have eq798 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq744 eq690
    | exact resolve eq690 eq744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq799 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq744 eq16
    | exact resolve eq16 eq744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq828 : (M.op x (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq744 (M.op x x)
       have i₂ := eq777 x (M.op (M.op x x) sF3)
       grind)
    | exact superpose eq777 eq744
    | exact resolve eq744 eq777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744
  have eq854 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X0) X1)) = (M.op x (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq778 X2 (M.op X2 X0)
       have i₂ := eq16 X2 X0 X1
       grind)
    | (have i₁ := eq778 (M.op X1 X1) X2
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq778
    | exact resolve eq778 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq884 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X0) X1)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0 X1 X2
    first
    | exact superpose eq828 eq854
    | exact resolve eq854 eq828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854
  have eq887 : ∀ X2 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X2 (M.op x (M.op x y))) := by
    intro X2
    first
    | (have i₁ := eq884 x x X2
       have i₂ := eq777 x x
       grind)
    | exact superpose eq777 eq884
    | exact resolve eq884 eq777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777 eq884
  have eq890 : ∀ X2 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X2 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X2
    first
    | exact superpose eq828 eq887
    | exact resolve eq887 eq828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq887
  have eq910 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq28
    | (have j0 := eq28 X1 X0
       have j1 := eq11 X0 X0
       grind)
    | (have r₁ := eq28 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq28 X0 X1
       have r₂ := eq11 X1 X1
       grind)
    | (have r₁ := eq28 X0 (M.op X0 X0)
       have r₂ := eq11 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq930 : (M.op x y) = (k y x) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
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
  have eq936 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
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
  have eq940 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq941 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq940 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq940
  have eq952 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq910 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq910
  have eq979 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq952 X0 X1
       have j1 := eq28 X1 X0
       grind)
    | (have r₁ := eq952 X1 X1
       have r₂ := eq28 X1 X1
       grind)
    | (have r₁ := eq952 X1 X1
       have r₂ := eq28 X0 X1
       grind)
    | exact resolve eq952 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq952
  have eq1044 : ∀ X0 : G, (M.op x (M.op x y)) ≠ (M.op x (M.op x y)) ∨ (k X0 (M.op x (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq779 eq28
    | (have j0 := eq28 X0 (M.op x (M.op x y))
       grind)
    | (have r₁ := eq28 X0 (M.op x (M.op x y))
       have r₂ := eq779 (M.op x (M.op x y))
       grind)
    | exact resolve eq28 eq779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1046 : ∀ X0 : G, (M.op x (M.op x y)) = (k (M.op x (M.op x y)) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op (M.op x (M.op x y)) (M.op x (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq779 eq11
    | (have j0 := eq11 X0 X0
       grind)
    | exact resolve eq11 eq779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779
  have eq1054 : ∀ X0 : G, (k X0 (M.op x (M.op x y))) = X0 := by
    intro X0
    first
    | (have j0 := eq1044 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1044
  have eq1058 : ∀ X0 : G, (M.op x (M.op x y)) = (k (M.op x (M.op x y)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1046 X0
       have j1 := eq13 (M.op x (M.op x y)) X0
       grind)
    | (have r₁ := eq1046 x
       have r₂ := eq13 x x
       grind)
    | (have r₁ := eq1046 (M.op X0 X0)
       have r₂ := eq13 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | (have r₁ := eq1046 x
       have r₂ := eq13 (M.op x (M.op x y)) x
       grind)
    | exact resolve eq1046 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1046
  have eq1060 : ∀ X0 : G, (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) = X0 := by
    intro X0
    first
    | exact superpose eq828 eq1054
    | exact resolve eq1054 eq828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1054
  have eq1066 : ∀ X0 : G, (M.op x (M.op x y)) = (k (M.op x (M.op x y)) X0) := by
    intro X0
    first
    | (have j0 := eq1058 X0
       have j1 := eq28 (M.op x (M.op x y)) X0
       grind)
    | (have r₁ := eq1058 x
       have r₂ := eq28 X0 x
       grind)
    | exact resolve eq1058 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1058
  have eq1070 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (M.op (σ x) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq828 eq1066
    | exact resolve eq1066 eq828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1066
  have eq1075 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq1060 eq35
    | exact resolve eq35 eq1060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq1089 : ∀ X0 : G, (k X0 (σ (M.op (σ x) (M.op (σ x) (σ y))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1075 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq1075
    | exact resolve eq1075 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1075
  have eq1133 : (σ (M.op (σ x) (M.op (σ x) (σ y)))) ≠ (σ (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op (σ (M.op (σ x) (M.op (σ x) (σ y)))) (σ (M.op (σ x) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq1089 eq941
    | (have j0 := eq941 (σ (M.op (σ x) (M.op (σ x) (σ y))))
       grind)
    | (have r₁ := eq941 (σ (M.op (σ x) (M.op (σ x) (σ y))))
       have r₂ := eq1089 (σ (M.op (σ x) (M.op (σ x) (σ y))))
       grind)
    | exact resolve eq941 eq1089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1089
  have eq1146 : (σ (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op (σ (M.op (σ x) (M.op (σ x) (σ y)))) (σ (M.op (σ x) (M.op (σ x) (σ y))))) := by grind
  clear eq1133
  have eq1420 : ∀ X0 : G, (σ (M.op (σ x) (M.op (σ x) (σ y)))) = (k (σ (M.op (σ x) (M.op (σ x) (σ y)))) X0) := by
    intro X0
    first
    | exact superpose eq1070 eq39
    | exact resolve eq39 eq1070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq1070
  have eq1532 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq979 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq979
    | (have j0 := eq979 (σ X0) X1
       grind)
    | exact resolve eq979 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3809 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq930
       grind)
    | exact superpose eq930 eq40
    | exact resolve eq40 eq930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3810 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq3809
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3809
    | exact resolve eq3809 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3809
  have eq3812 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq3810
    | exact resolve eq3810 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3810
  have eq9548 : ∀ X0 X1 : G, (σ (k (k y X0) (k x X1))) = (k (k (σ y) (σ X0)) (k (σ x) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq43 X1 (k y X0)
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq43
    | exact resolve eq43 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq43
  have eq23275 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ (M.op (σ x) (M.op (σ x) (σ y)))) X0) := by
    intro X0
    first
    | exact superpose eq1146 eq798
    | exact resolve eq798 eq1146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23278 : ∀ X0 : G, (M.op (σ (M.op (σ x) (M.op (σ x) (σ y)))) (σ (M.op (σ x) (M.op (σ x) (σ y))))) = (M.op (σ (M.op (σ x) (M.op (σ x) (σ y)))) X0) := by
    intro X0
    first
    | exact superpose eq1146 eq16
    | exact resolve eq16 eq1146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23291 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ (M.op (σ x) (M.op (σ x) (σ y)))) (σ (M.op (σ x) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq1146 eq799
    | exact resolve eq799 eq1146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23300 : ∀ X0 : G, (σ (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op (σ (M.op (σ x) (M.op (σ x) (σ y)))) X0) := by
    intro X0
    first
    | exact superpose eq1146 eq23278
    | exact resolve eq23278 eq1146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23278
  have eq23316 : (M.op (σ x) (M.op (σ x) (σ y))) = (σ (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq23275 eq23300
    | exact resolve eq23300 eq23275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23300
  have eq23359 : (M.op (σ x) (M.op (σ x) (σ y))) = (τ (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq23316 eq15
    | exact resolve eq15 eq23316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30687 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq3812 eq936
    | exact resolve eq936 eq3812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30694 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq30687
       have r₂ := eq27
       grind)
    | exact resolve eq30687 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30687
  have eq30701 : y = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30694 eq218
    | exact resolve eq218 eq30694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218 eq30694
  have eq30772 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30 eq30701
    | exact resolve eq30701 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30701
  have eq30791 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq30772
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq30772
       have r₂ := eq13 x x
       grind)
    | (have r₁ := eq30772
       have r₂ := eq13 y x
       grind)
    | exact resolve eq30772 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30772
  have eq30795 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (k y x) := by
    first
    | (have j1 := eq28 y x
       grind)
    | (have r₁ := eq30791
       have r₂ := eq28 x (σ x)
       grind)
    | (have r₁ := eq30791
       have r₂ := eq28 x x
       grind)
    | exact resolve eq30791 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq30791
  have eq30797 : x = (k x (τ (σ x))) ∨ y = (k y x) := by
    first
    | exact superpose eq30795 eq200
    | exact resolve eq200 eq30795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200 eq30795
  have eq30858 : x = (k x x) ∨ y = (k y x) := by
    first
    | exact superpose eq30 eq30797
    | exact resolve eq30797 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30797
  have eq30877 : y = (k y x) := by
    first
    | (have j1 := eq979 x y
       grind)
    | (have r₁ := eq30858
       have r₂ := eq979 x x
       grind)
    | exact resolve eq30858 eq979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq979 eq30858
  have eq30886 : x = (M.op y y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq930
       have i₂ := eq30877
       grind)
    | exact superpose eq30877 eq930
    | exact resolve eq930 eq30877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq930
  have eq30888 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq30877
       grind)
    | exact superpose eq30877 eq40
    | exact resolve eq40 eq30877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq30877
  have eq30889 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq30888
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq30888
    | exact resolve eq30888 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30888
  have eq31343 : x = (M.op y y) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq30889 eq3812
    | exact resolve eq3812 eq30889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3812
  have eq31346 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30889 eq936
    | exact resolve eq936 eq30889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936
  have eq32291 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op x X0) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq798 y X0
       have i₂ := eq30886
       grind)
    | exact superpose eq30886 eq798
    | exact resolve eq798 eq30886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30886
  have eq32401 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op x X0) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq798 y X0
       have i₂ := eq31343
       grind)
    | exact superpose eq31343 eq798
    | exact resolve eq798 eq31343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798 eq31343
  have eq32498 : ∀ X0 X1 : G, (M.op (σ x) X1) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq31346 eq690
    | exact resolve eq690 eq31346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690 eq31346
  have eq36705 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq32291 y
       grind)
    | (have i₁ := eq18
       have i₂ := eq32291 x
       grind)
    | exact superpose eq32291 eq18
    | (have j1 := eq32291 y
       grind)
    | exact resolve eq18 eq32291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32291
  have eq36862 : ∀ X0 : G, x = (M.op x x) ∨ (k X0 (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq36705 eq1060
    | exact resolve eq1060 eq36705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36935 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq36705 eq23316
    | exact resolve eq23316 eq36705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36936 : x = (M.op x x) ∨ (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq36705 eq23359
    | exact resolve eq23359 eq36705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36705
  have eq36986 : x = (M.op x x) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq36935
    | exact resolve eq36935 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36935
  have eq37725 : ∀ X0 : G, (M.op x x) = (M.op x X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16 x x x
       have i₂ := eq36986
       grind)
    | exact superpose eq36986 eq16
    | exact resolve eq16 eq36986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37742 : (M.op x x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq799 x x
       have i₂ := eq36986
       grind)
    | exact superpose eq36986 eq799
    | exact resolve eq799 eq36986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37749 : x = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq36986 eq37742
    | exact resolve eq37742 eq36986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37742
  have eq37758 : ∀ X0 : G, x = (M.op x X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq36986 eq37725
    | exact resolve eq37725 eq36986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36986 eq37725
  have eq38062 : ∀ X0 : G, x = (M.op (σ x) X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq37749 eq23275
    | exact resolve eq23275 eq37749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38064 : x = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq37749 eq23316
    | exact resolve eq23316 eq37749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37749
  have eq38117 : (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq38064
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq38064
    | exact resolve eq38064 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38064
  have eq38119 : ∀ X0 : G, x = (M.op (σ x) X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq38062 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq38062
    | (have j0 := eq38062 X0
       grind)
    | exact resolve eq38062 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38062
  have eq38195 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq38117 eq38119
    | exact resolve eq38119 eq38117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38119
  have eq38243 : (M.op x y) = (τ (M.op x y)) ∨ x = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq38117 eq29
    | exact resolve eq29 eq38117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38574 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq37758 y
       grind)
    | exact superpose eq37758 eq18
    | (have j1 := eq37758 y
       grind)
    | exact resolve eq18 eq37758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37758
  have eq38754 : (M.op x y) = (τ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq38574 eq29
    | exact resolve eq29 eq38574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38574
  have eq39944 : (σ x) = (σ (σ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq38195 eq23316
    | exact resolve eq23316 eq38195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38195
  have eq41223 : x = (k x x) ∨ (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq175 x
       have i₂ := eq36936
       grind)
    | exact superpose eq36936 eq175
    | exact resolve eq175 eq36936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41259 : (M.op x x) = (M.op x (M.op x y)) ∨ (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq778 x x
       have i₂ := eq36936
       grind)
    | exact superpose eq36936 eq778
    | exact resolve eq778 eq36936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778
  have eq41260 : (M.op x x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq799 x x
       have i₂ := eq36936
       grind)
    | exact superpose eq36936 eq799
    | exact resolve eq799 eq36936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41267 : (M.op (M.op x y) (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq38754 eq41260
    | exact resolve eq41260 eq38754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41260
  have eq41268 : (M.op x x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq828 eq41259
    | exact resolve eq41259 eq828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41259
  have eq41293 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq38754 eq41223
    | exact resolve eq41223 eq38754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38754 eq41223
  have eq41301 : (M.op x x) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq41267 eq41268
    | exact resolve eq41268 eq41267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41267 eq41268
  have eq41322 : x = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq36936 eq41301
    | exact resolve eq41301 eq36936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36936 eq41301
  have eq41338 : (σ x) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq38243 eq41322
    | exact resolve eq41322 eq38243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38243 eq41322
  have eq42564 : (σ x) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq41338 eq11
    | exact resolve eq11 eq41338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41338
  have eq42583 : (σ x) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq42564
  have eq42600 : (M.op x y) = (σ x) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq41293 eq42583
    | exact resolve eq42583 eq41293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41293 eq42583
  have eq42601 : (M.op x y) = (τ (M.op x y)) ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq42600
  have eq42672 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq42601 eq14
    | exact resolve eq14 eq42601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42601
  have eq42721 : (M.op x y) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq42672
    | exact resolve eq42672 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42672
  have eq42900 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq42721 eq39944
    | exact resolve eq39944 eq42721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39944 eq42721
  have eq42909 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq42900
  have eq42926 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq42909
    | exact resolve eq42909 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42909
  have eq42927 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq42926
  have eq46546 : ∀ X0 : G, (M.op x x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (k X0 (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq799 x x
       have i₂ := eq36862 X0
       grind)
    | exact superpose eq36862 eq799
    | (have j1 := eq36862 X0
       grind)
    | exact resolve eq799 eq36862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46553 : ∀ X0 : G, x = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (k X0 (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq36862 eq46546
    | (have j0 := eq46546 X0
       have j1 := eq36862 X0
       grind)
    | exact resolve eq46546 eq36862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36862 eq46546
  have eq47320 : ∀ X0 X1 : G, x = (M.op (σ x) X0) ∨ (k X1 (M.op x y)) = X1 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq23275 X0
       have i₂ := eq46553 (M.op sF2 sF4)
       grind)
    | exact superpose eq46553 eq23275
    | (have j1 := eq46553 X1
       grind)
    | exact resolve eq23275 eq46553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47322 : ∀ X0 : G, x = (σ x) ∨ (k X0 (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq23316
       have i₂ := eq46553 (M.op sF2 sF4)
       grind)
    | exact superpose eq46553 eq23316
    | (have j1 := eq46553 X0
       grind)
    | exact resolve eq23316 eq46553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46553
  have eq47388 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ x = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq47322 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq47322
    | (have j0 := eq47322 X0
       grind)
    | exact resolve eq47322 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47322
  have eq47390 : ∀ X0 X1 : G, x = (M.op (σ x) X0) ∨ (k X1 (M.op x y)) = X1 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq47320 X0 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq47320
    | (have j0 := eq47320 X0 X1
       grind)
    | exact resolve eq47320 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47320
  have eq47462 : ∀ X0 X1 : G, (σ x) = (M.op (σ x) X0) ∨ (k X1 (M.op x y)) = X1 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq47388 eq47390
    | (have j0 := eq47390 X0 X1
       have j1 := eq47388 X1
       grind)
    | exact resolve eq47390 eq47388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47388 eq47390
  have eq54360 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq26
       have i₂ := eq47462 X0 (M.op sF2 sF3)
       grind)
    | exact superpose eq47462 eq26
    | (have j1 := eq47462 (σ y) X0
       grind)
    | exact resolve eq26 eq47462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47462
  have eq54816 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq54360 eq941
    | (have j0 := eq941 (M.op x y)
       grind)
    | (have r₁ := eq941 (M.op x y)
       have r₂ := eq54360 (M.op x y)
       grind)
    | exact resolve eq941 eq54360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54360
  have eq54887 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq54816
  have eq55080 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq54887 eq16
    | exact resolve eq16 eq54887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55115 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq54887 eq55080
    | exact resolve eq55080 eq54887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54887 eq55080
  have eq72190 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq32401 y
       grind)
    | exact superpose eq32401 eq18
    | (have j1 := eq32401 y
       grind)
    | exact resolve eq18 eq32401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32401
  have eq72385 : ∀ X0 : G, x = (M.op x x) ∨ (k X0 (M.op x y)) = X0 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq72190 eq1060
    | exact resolve eq1060 eq72190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72459 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq72190 eq23316
    | exact resolve eq23316 eq72190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72190
  have eq72527 : x = (M.op x x) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq72459
    | exact resolve eq72459 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72459
  have eq72908 : x = (k x x) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq175 x
       have i₂ := eq72527
       grind)
    | exact superpose eq72527 eq175
    | exact resolve eq175 eq72527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq72945 : (M.op x x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq799 x x
       have i₂ := eq72527
       grind)
    | exact superpose eq72527 eq799
    | exact resolve eq799 eq72527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72954 : x = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq72527 eq72945
    | exact resolve eq72945 eq72527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72527 eq72945
  have eq73013 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq1532 x X0
       have i₂ := eq72908
       grind)
    | exact superpose eq72908 eq1532
    | (have j0 := eq1532 x X0
       grind)
    | exact resolve eq1532 eq72908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1532 eq72908
  have eq73024 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq73013 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73013
  have eq73030 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq73024 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq73024
    | (have j0 := eq73024 X0
       grind)
    | exact resolve eq73024 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73024
  have eq73257 : ∀ X0 : G, (σ x) = (k (σ x) X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq72954 eq1420
    | exact resolve eq1420 eq72954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1420
  have eq73307 : ∀ X0 : G, x = (M.op (σ x) X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq72954 eq23275
    | exact resolve eq23275 eq72954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23275
  have eq73309 : x = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq72954 eq23316
    | exact resolve eq23316 eq72954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72954
  have eq73388 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) := by
    first
    | (have i₁ := eq73309
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq73309
    | exact resolve eq73309 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73309
  have eq73390 : ∀ X0 : G, x = (M.op (σ x) X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq73307 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq73307
    | (have j0 := eq73307 X0
       grind)
    | exact resolve eq73307 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73307
  have eq73435 : ∀ X0 : G, (σ x) = (k (σ x) X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq73257 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq73257
    | (have j0 := eq73257 X0
       grind)
    | exact resolve eq73257 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73257
  have eq73466 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq73388 eq73390
    | exact resolve eq73390 eq73388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73388 eq73390
  have eq75930 : (σ x) = (σ (σ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq73466 eq23316
    | exact resolve eq23316 eq73466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73466
  have eq76698 : ∀ X0 : G, (k (k (σ y) (σ x)) (k (σ x) (σ X0))) = (σ (k (k y (σ x)) (k x X0))) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq75930 eq9548
    | exact resolve eq9548 eq75930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9548 eq75930
  have eq76718 : ∀ X0 : G, (k (σ y) (k (σ x) (σ X0))) = (σ (k (k y (σ x)) (k x X0))) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq30889 eq76698
    | exact resolve eq76698 eq30889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76698
  have eq76807 : ∀ X0 : G, (k (σ y) (k (σ x) (σ X0))) = (σ (k (k (M.op x y) (σ x)) (k x X0))) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq42927 eq76718
    | exact resolve eq76718 eq42927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76718
  have eq76894 : ∀ X0 : G, (k (σ y) (k (σ x) (σ X0))) = (σ (k (M.op x y) (k x X0))) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq73030 eq76807
    | exact resolve eq76807 eq73030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76807
  have eq76963 : ∀ X0 : G, (k (σ y) (k (σ x) (σ X0))) = (k (σ (M.op x y)) (σ (k x X0))) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq38 eq76894
    | exact resolve eq76894 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq76894
  have eq77016 : ∀ X0 : G, (k (σ y) (k (σ x) (σ X0))) = (k (σ (M.op x y)) (k (σ x) (σ X0))) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq76963 X0
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq76963
    | exact resolve eq76963 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq76963
  have eq77045 : (k (σ (M.op x y)) (σ x)) = (k (σ y) (σ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq73435 eq77016
    | exact resolve eq77016 eq73435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73435 eq77016
  have eq77063 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq30889 eq77045
    | exact resolve eq77045 eq30889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30889 eq77045
  have eq77498 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq77063 eq73030
    | exact resolve eq73030 eq77063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73030 eq77063
  have eq77506 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq77498
  have eq77589 : (M.op x y) ≠ (σ y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq77506
  have eq84027 : ∀ X0 X1 : G, (M.op x x) = (M.op x X0) ∨ (k X1 (M.op x y)) = X1 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 x x x
       have i₂ := eq72385 X0
       grind)
    | exact superpose eq72385 eq16
    | (have j1 := eq72385 X1
       grind)
    | exact resolve eq16 eq72385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84044 : ∀ X0 : G, (M.op x x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (k X0 (M.op x y)) = X0 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq799 x x
       have i₂ := eq72385 X0
       grind)
    | exact superpose eq72385 eq799
    | (have j1 := eq72385 X0
       grind)
    | exact resolve eq799 eq72385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84051 : ∀ X0 : G, x = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (k X0 (M.op x y)) = X0 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq72385 eq84044
    | (have j0 := eq84044 X0
       have j1 := eq72385 X0
       grind)
    | exact resolve eq84044 eq72385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84044
  have eq84060 : ∀ X0 X1 : G, x = (M.op x X0) ∨ (k X1 (M.op x y)) = X1 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq72385 eq84027
    | (have j0 := eq84027 X0 X1
       have j1 := eq72385 X1
       grind)
    | exact resolve eq84027 eq72385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72385 eq84027
  have eq84932 : ∀ X0 : G, x = (σ x) ∨ (k X0 (M.op x y)) = X0 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq23316
       have i₂ := eq84051 (M.op sF2 sF4)
       grind)
    | exact superpose eq84051 eq23316
    | (have j1 := eq84051 X0
       grind)
    | exact resolve eq23316 eq84051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84051
  have eq85017 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ x = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq84932 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq84932
    | (have j0 := eq84932 X0
       grind)
    | exact resolve eq84932 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84932
  have eq85147 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq85017 eq941
    | (have j0 := eq941 (M.op x y)
       grind)
    | (have r₁ := eq941 (M.op x y)
       have r₂ := eq85017 (M.op x y)
       grind)
    | exact resolve eq941 eq85017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85017
  have eq85221 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq85147
  have eq85461 : (M.op (M.op x y) (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq85221 eq799
    | exact resolve eq799 eq85221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85471 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq85221 eq85461
    | exact resolve eq85461 eq85221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85221 eq85461
  have eq87133 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq84060 y X0
       grind)
    | exact superpose eq84060 eq18
    | (have j1 := eq84060 y X0
       grind)
    | exact resolve eq18 eq84060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84060
  have eq87347 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq87133 eq941
    | (have j0 := eq941 (M.op x y)
       grind)
    | (have r₁ := eq941 (M.op x y)
       have r₂ := eq87133 (M.op x y)
       grind)
    | exact resolve eq941 eq87133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87133
  have eq87421 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq87347
  have eq87668 : (M.op (M.op x y) (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq87421 eq799
    | exact resolve eq799 eq87421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87678 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq87421 eq87668
    | exact resolve eq87668 eq87421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87421 eq87668
  have eq117806 : ∀ X0 : G, (σ (M.op (σ x) X0)) = (M.op (σ (M.op (σ x) X0)) (σ (M.op (σ x) X0))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq32498 eq1146
    | exact resolve eq1146 eq32498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117868 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ (M.op (σ x) X0)) (σ (M.op (σ x) X0))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq32498 eq23291
    | exact resolve eq23291 eq32498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118033 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq32498 eq26
    | (have j1 := eq32498 X0 (σ y)
       grind)
    | exact resolve eq26 eq32498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32498
  have eq118483 : (M.op (σ x) (σ y)) = (M.op (σ (M.op (σ x) (σ y))) (σ (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq118033 eq117868
    | (have j0 := eq117868 (σ y)
       grind)
    | exact resolve eq117868 eq118033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117868
  have eq118544 : (σ (M.op (σ x) (σ y))) = (M.op (σ (M.op (σ x) (σ y))) (σ (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq118033 eq117806
    | (have j0 := eq117806 (σ y)
       grind)
    | exact resolve eq117806 eq118033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117806
  have eq118778 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq118483 eq118544
    | exact resolve eq118544 eq118483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118483 eq118544
  have eq118898 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq118778 eq16
    | exact resolve eq16 eq118778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118931 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq118778 eq118898
    | exact resolve eq118898 eq118778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118778 eq118898
  have eq122144 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (k X0 (M.op (σ x) (σ y))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq118033 eq1060
    | exact resolve eq1060 eq118033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1060
  have eq126437 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (k X0 (M.op (σ x) (σ y))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq799 X0 x
       have i₂ := eq122144 (M.op X0 x)
       grind)
    | exact superpose eq122144 eq799
    | (have j1 := eq122144 X0
       grind)
    | exact resolve eq799 eq122144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126445 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (k X0 (M.op (σ x) (σ y))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq122144 eq126437
    | (have j0 := eq126437 X0
       have j1 := eq122144 X0
       grind)
    | exact resolve eq126437 eq122144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122144 eq126437
  have eq127237 : ∀ X0 : G, (σ x) = (τ (σ x)) ∨ (k X0 (M.op (σ x) (σ y))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq23359
       have i₂ := eq126445 (M.op sF2 sF4)
       grind)
    | exact superpose eq126445 eq23359
    | (have j1 := eq126445 X0
       grind)
    | exact resolve eq23359 eq126445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23359 eq126445
  have eq127347 : ∀ X0 : G, (k X0 (M.op (σ x) (σ y))) = X0 ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq30 eq127237
    | (have j0 := eq127237 X0
       grind)
    | exact resolve eq127237 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq127237
  have eq127579 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq127347 eq941
    | (have j0 := eq941 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq941 (M.op (σ x) (σ y))
       have r₂ := eq127347 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq941 eq127347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq941 eq127347
  have eq127641 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq127579
  have eq128443 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq127641 eq799
    | exact resolve eq799 eq127641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq799
  have eq128446 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq127641 eq128443
    | exact resolve eq128443 eq127641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127641 eq128443
  have eq128658 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq128446 eq85471
    | exact resolve eq85471 eq128446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128446
  have eq128714 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq128658
  have eq132298 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq128714 eq85471
    | exact resolve eq85471 eq128714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85471 eq128714
  have eq132314 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq132298
  have eq132338 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq132314
    | exact resolve eq132314 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132314
  have eq132339 : (σ (M.op x y)) = (σ y) ∨ x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq132338
  have eq132441 : (M.op x y) = (τ (σ y)) ∨ x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq132339 eq29
    | exact resolve eq29 eq132339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq132339
  have eq132589 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32 eq132441
    | exact resolve eq132441 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq132441
  have eq132611 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq132589 eq27
    | exact resolve eq27 eq132589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132589
  have eq132895 : y = (M.op x y) ∨ x = (σ x) := by
    first
    | (have r₁ := eq132611
       have r₂ := eq38117
       grind)
    | exact resolve eq132611 eq38117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38117 eq132611
  have eq132962 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (σ x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq132895
       grind)
    | exact superpose eq132895 eq18
    | exact resolve eq18 eq132895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132963 : (σ (M.op x y)) = (σ y) ∨ x = (σ x) := by
    first
    | (have i₁ := eq24
       have i₂ := eq132895
       grind)
    | exact superpose eq132895 eq24
    | exact resolve eq24 eq132895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132895
  have eq133036 : (σ (M.op x y)) = (σ y) ∨ x = (σ x) := by
    first
    | exact superpose eq20 eq132963
    | exact resolve eq132963 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132963
  have eq133037 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (σ x) := by
    first
    | exact superpose eq828 eq132962
    | exact resolve eq132962 eq828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828 eq132962
  have eq133277 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ x = (σ x) := by
    intro X0
    first
    | exact superpose eq133037 eq890
    | exact resolve eq890 eq133037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq890
  have eq133289 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (σ x) := by
    first
    | exact superpose eq133037 eq1146
    | exact resolve eq1146 eq133037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1146
  have eq133351 : (M.op x y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (σ x) := by
    first
    | exact superpose eq133037 eq23291
    | exact resolve eq23291 eq133037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23291
  have eq133352 : (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) := by
    first
    | exact superpose eq133037 eq23316
    | exact resolve eq23316 eq133037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23316 eq133037
  have eq133448 : (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) := by
    first
    | exact superpose eq20 eq133352
    | exact resolve eq133352 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133352
  have eq133449 : (M.op x y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (σ x) := by
    first
    | exact superpose eq20 eq133351
    | exact resolve eq133351 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133351
  have eq133510 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (σ x) := by
    first
    | exact superpose eq20 eq133289
    | exact resolve eq133289 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133289
  have eq133533 : (M.op x y) = (M.op (σ y) (σ y)) ∨ x = (σ x) := by
    first
    | exact superpose eq133036 eq133449
    | exact resolve eq133449 eq133036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133449
  have eq133577 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (σ x) := by
    first
    | exact superpose eq133036 eq133510
    | exact resolve eq133510 eq133036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133036 eq133510
  have eq133598 : (M.op x y) = (σ y) ∨ x = (σ x) := by
    first
    | exact superpose eq133533 eq133577
    | exact resolve eq133577 eq133533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133533 eq133577
  have eq133941 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ x = (σ x) := by
    first
    | exact superpose eq133598 eq26
    | exact resolve eq26 eq133598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133598
  have eq134138 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    first
    | exact superpose eq133277 eq133941
    | exact resolve eq133941 eq133277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133277 eq133941
  have eq134402 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (σ x) := by
    first
    | exact superpose eq134138 eq27
    | exact resolve eq27 eq134138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134138
  have eq134642 : x = (σ x) := by
    first
    | (have r₁ := eq134402
       have r₂ := eq133448
       grind)
    | exact resolve eq134402 eq133448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133448 eq134402
  have eq134685 : (M.op x y) = (M.op (σ x) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq134642
       grind)
    | exact superpose eq134642 eq18
    | exact resolve eq18 eq134642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq134686 : (σ x) = (σ (σ x)) := by
    first
    | (have i₁ := eq22
       have i₂ := eq134642
       grind)
    | exact superpose eq134642 eq22
    | exact resolve eq22 eq134642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq135385 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq134685 eq118033
    | exact resolve eq118033 eq134685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118033
  have eq135387 : (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq134685 eq118931
    | exact resolve eq118931 eq134685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118931
  have eq147806 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq135385 eq16
    | exact resolve eq16 eq135385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq147842 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq135385 eq147806
    | exact resolve eq147806 eq135385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135385 eq147806
  have eq150395 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq147842 eq134685
    | exact resolve eq134685 eq147842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147842
  have eq151074 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq150395 eq27
    | exact resolve eq27 eq150395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq151188 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq150395 eq87678
    | exact resolve eq87678 eq150395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87678 eq150395
  have eq151208 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq26 eq151188
    | exact resolve eq151188 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151188
  have eq151209 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (σ x) := by grind
  clear eq151208
  have eq151314 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ x) := by
    first
    | (have r₁ := eq151209
       have r₂ := eq151074
       grind)
    | exact resolve eq151209 eq151074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151074 eq151209
  have eq151411 : (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ x) := by
    first
    | (have i₁ := eq151314
       have i₂ := eq134642
       grind)
    | exact superpose eq134642 eq151314
    | exact resolve eq151314 eq134642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134642 eq151314
  have eq151412 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ x) := by grind
  clear eq151411
  have eq151506 : (M.op x y) ≠ (σ (M.op x y)) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq151412 eq27
    | exact resolve eq27 eq151412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq151665 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq151412 eq135387
    | exact resolve eq135387 eq151412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135387 eq151412
  have eq151668 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (σ y) := by grind
  clear eq151665
  have eq151680 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq20 eq151668
    | exact resolve eq151668 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151668
  have eq151766 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ x) := by
    first
    | (have r₁ := eq151680
       have r₂ := eq77589
       grind)
    | exact resolve eq151680 eq77589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77589 eq151680
  have eq151827 : (M.op x y) = (σ x) := by
    first
    | (have r₁ := eq151766
       have r₂ := eq151506
       grind)
    | exact resolve eq151766 eq151506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151506 eq151766
  have eq151865 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq151827 eq26
    | exact resolve eq26 eq151827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq152220 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq151827 eq134685
    | exact resolve eq134685 eq151827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134685
  have eq152221 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq151827 eq134686
    | exact resolve eq134686 eq151827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134686
  have eq153162 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq152221 eq20
    | exact resolve eq20 eq152221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq154050 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq151865 eq55115
    | exact resolve eq55115 eq151865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55115
  have eq154139 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq151827 eq154050
    | exact resolve eq154050 eq151827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151827 eq154050
  have eq154140 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq154139
  have eq156691 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq154140 eq27
    | exact resolve eq27 eq154140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154140
  have eq156952 : y = (M.op x y) := by
    first
    | (have r₁ := eq156691
       have r₂ := eq42927
       grind)
    | exact resolve eq156691 eq42927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42927 eq156691
  have eq157007 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq156952
       grind)
    | exact superpose eq156952 eq24
    | exact resolve eq24 eq156952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq157064 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq152220
       have i₂ := eq156952
       grind)
    | exact superpose eq156952 eq152220
    | exact resolve eq152220 eq156952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152220 eq156952
  have eq157100 : (M.op x y) = (σ y) := by
    first
    | exact superpose eq152221 eq157007
    | exact resolve eq157007 eq152221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152221 eq157007
  have eq157284 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq157100 eq151865
    | exact resolve eq151865 eq157100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151865 eq157100
  have eq157291 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq157064 eq157284
    | exact resolve eq157284 eq157064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157064 eq157284
  have eq157512 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq157291 eq27
    | exact resolve eq27 eq157291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq157291
  have eq157746 : False := by grind
  exact eq157746

/-- `Equation4417`: `x ◇ (x ◇ y) = (z ◇ x) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then Y else if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_y_y_pxx_pxy_Equation4417 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4417 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4417.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X0) X2) := by
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
  have eq90 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq44 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq44
    | exact resolve eq44 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq107 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq47 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq47
    | exact resolve eq47 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq174 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 X1 X3 : G, (M.op (M.op X3 X1) X3) = (M.op X1 (M.op (M.op X0 X1) X0)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq16 X1 (M.op X1 x) X3
       have i₂ := eq16 X1 x X0
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X3 X1) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq16 X1 x X3
       have i₂ := eq16 X1 x X0
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) (M.op (M.op X1 X2) X3)) = (M.op (M.op (M.op X0 X1) X0) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op X1 X2) X3 X1
       have i₂ := eq16 X1 X2 X0
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op X0 (M.op X0 X1)) (M.op X2 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X2 X3 (M.op X2 X0)
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 : G, (M.op y (M.op y X0)) = (M.op (M.op x y) x) := by
    intro X0
    first
    | (have i₁ := eq16 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 y X0 x
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) X0)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) X0 (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 x
       have i₂ := eq16 X0 X2 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : (M.op (M.op x y) x) = (M.op y (M.op (M.op x y) x)) := by
    first
    | (have i₁ := eq180 (M.op y x)
       have i₂ := eq180 x
       grind)
    | exact superpose eq180 eq180
    | exact resolve eq180 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : ∀ X1 : G, (M.op (M.op x y) x) = (M.op (M.op X1 y) X1) := by
    intro X1
    first
    | (have i₁ := eq16 y x X1
       have i₂ := eq180 x
       grind)
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op X1 (σ y)) X1) := by
    intro X1
    first
    | exact superpose eq181 eq16
    | exact resolve eq16 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq200 : ∀ X0 X1 : G, (M.op (M.op x y) x) = (M.op (M.op X0 (M.op X0 X1)) (M.op y X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq189 (M.op y X0)
       have i₂ := eq16 X0 X1 y
       grind)
    | exact superpose eq16 eq189
    | exact resolve eq189 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq201 : (M.op (M.op x y) x) = (M.op (M.op (M.op x y) x) (M.op y y)) := by
    first
    | (have i₁ := eq189 (M.op y y)
       have i₂ := eq189 y
       grind)
    | exact superpose eq189 eq189
    | exact resolve eq189 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq204 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (M.op x y) x) (M.op X0 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 (M.op X0 y)
       have i₂ := eq189 X0
       grind)
    | (have i₁ := eq16 x X1 (M.op x y)
       have i₂ := eq189 X1
       grind)
    | exact superpose eq189 eq16
    | exact resolve eq16 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq216 : (τ (M.op (σ x) (σ x))) = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq90 (M.op sF2 sF2)
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq90
    | exact resolve eq90 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq227 : (τ (M.op (σ y) (σ y))) = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | (have i₁ := eq107 (M.op sF3 sF3)
       have i₂ := eq174 sF3
       grind)
    | exact superpose eq174 eq107
    | exact resolve eq107 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq334 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq174 (τ X0)
       grind)
    | exact superpose eq174 eq34
    | exact resolve eq34 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq174
  have eq594 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op X1 (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq195 eq177
    | exact resolve eq177 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq596 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) x) y) = (M.op (M.op X0 (M.op y X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq177 X0 (M.op y X1) y
       have i₂ := eq180 X1
       grind)
    | exact superpose eq180 eq177
    | exact resolve eq177 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq641 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (M.op X1 (M.op (M.op X0 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq182 X1 X2 (M.op X1 x)
       have i₂ := eq16 X1 x X0
       grind)
    | exact superpose eq16 eq182
    | exact resolve eq182 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq645 : ∀ X0 X1 : G, (M.op (M.op X0 y) (M.op (M.op x y) x)) = (M.op (M.op X0 y) (M.op (M.op X0 y) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq182 (M.op X0 y) X1 X0
       have i₂ := eq189 X0
       grind)
    | (have i₁ := eq182 (M.op x y) X1 x
       have i₂ := eq189 X1
       grind)
    | exact superpose eq189 eq182
    | exact resolve eq182 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq647 : ∀ X0 : G, (M.op x (M.op x X0)) = (M.op x (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq182 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq182
    | (have j0 := eq182 x X0 y
       grind)
    | exact resolve eq182 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq650 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq182
    | (have j0 := eq182 (σ x) X0 (σ y)
       grind)
    | exact resolve eq182 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq693 : ∀ X1 : G, (M.op x (M.op x y)) = (M.op (M.op X1 x) X1) := by
    intro X1
    first
    | (have i₁ := eq16 x x X1
       have i₂ := eq647 x
       grind)
    | (have i₁ := eq16 x y x
       have i₂ := eq647 x
       grind)
    | exact superpose eq647 eq16
    | (have j0 := eq16 x y X1
       grind)
    | exact resolve eq16 eq647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq697 : ∀ X0 X1 : G, (M.op (M.op x (M.op x y)) x) = (M.op (M.op X1 (M.op x X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq177 x (M.op x X0) X1
       have i₂ := eq647 X0
       grind)
    | (have i₁ := eq177 x (M.op x y) x
       have i₂ := eq647 X0
       grind)
    | exact superpose eq647 eq177
    | exact resolve eq177 eq647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq709 : ∀ X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op X1 (σ x)) X1) := by
    intro X1
    first
    | exact superpose eq650 eq16
    | (have j0 := eq16 (σ x) (σ y) X1
       grind)
    | exact resolve eq16 eq650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq713 : ∀ X0 X1 : G, (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) = (M.op (M.op X1 (M.op (σ x) X0)) X1) := by
    intro X0 X1
    first
    | exact superpose eq650 eq177
    | exact resolve eq177 eq650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq721 : (M.op x (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op x (σ y))) := by
    first
    | exact superpose eq195 eq693
    | exact resolve eq693 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq729 : ∀ X0 X1 : G, (M.op (M.op X0 x) (M.op (M.op X0 x) X1)) = (M.op (M.op X0 x) (M.op x (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq182 (M.op X0 x) X0 X1
       have i₂ := eq693 X0
       grind)
    | exact superpose eq693 eq182
    | exact resolve eq182 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq733 : ∀ X0 X1 : G, (M.op (M.op X0 x) (M.op x (M.op x y))) = (M.op (M.op X1 (M.op X0 x)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op X0 x) X0 X1
       have i₂ := eq693 X0
       grind)
    | exact superpose eq693 eq16
    | exact resolve eq16 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq734 : (M.op (M.op x y) x) = (M.op (M.op x (M.op x y)) (M.op y x)) := by
    first
    | (have i₁ := eq189 (M.op y x)
       have i₂ := eq693 y
       grind)
    | exact superpose eq693 eq189
    | exact resolve eq189 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq740 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op x (M.op x y)) (M.op (σ x) x)) := by
    first
    | (have i₁ := eq709 (M.op sF2 x)
       have i₂ := eq693 sF2
       grind)
    | exact superpose eq693 eq709
    | exact resolve eq709 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq741 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (M.op x y) x) (M.op (σ x) y)) := by
    first
    | (have i₁ := eq709 (M.op sF2 y)
       have i₂ := eq189 sF2
       grind)
    | exact superpose eq189 eq709
    | exact resolve eq709 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq742 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq709 eq709
    | exact resolve eq709 eq709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq751 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) (M.op (M.op X0 (σ x)) X1)) = (M.op (M.op X0 (σ x)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq709 eq182
    | exact resolve eq182 eq709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq755 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op (M.op X1 (M.op X0 (σ x))) X1) := by
    intro X0 X1
    first
    | exact superpose eq709 eq16
    | exact resolve eq16 eq709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq756 : (M.op x (M.op x y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op x (σ x))) := by
    first
    | exact superpose eq709 eq693
    | exact resolve eq693 eq709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq757 : (M.op (M.op x y) x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op y (σ x))) := by
    first
    | exact superpose eq709 eq189
    | exact resolve eq189 eq709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq866 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (k (M.op X0 X1) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X2 X0
       have i₂ := eq11 (M.op X0 X1) X0
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq875 : (M.op x y) = (k x y) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq18
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq882 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11 sF2 sF3
       grind)
    | exact superpose eq11 eq26
    | (have j1 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq890 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq891 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq890 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq890
  have eq914 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq891 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq891
    | (have j0 := eq891 (σ X0)
       grind)
    | exact resolve eq891 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq985 : ∀ X0 : G, (M.op (M.op (M.op x y) x) (M.op (M.op (M.op x y) x) X0)) = (M.op (M.op (M.op x y) x) (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq201 eq182
    | exact resolve eq182 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq987 : (M.op (M.op (M.op x y) x) (M.op (M.op x y) x)) = (M.op (M.op (M.op x y) x) (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq985 x
       have i₂ := eq729 sF0 x
       grind)
    | exact superpose eq729 eq985
    | exact resolve eq985 eq729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq985
  have eq1164 : ∀ X0 : G, (M.op (M.op X0 (M.op x (M.op x y))) X0) = (M.op (M.op x (M.op x y)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq740 eq16
    | exact resolve eq16 eq740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq740
  have eq1175 : (M.op (M.op x (M.op x y)) x) = (M.op (M.op x (M.op x y)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq1164 x
       have i₂ := eq697 sF0 x
       grind)
    | exact superpose eq697 eq1164
    | exact resolve eq1164 eq697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697 eq1164
  have eq1191 : ∀ X0 : G, (M.op (M.op (M.op x y) x) (M.op (M.op (M.op x y) x) X0)) = (M.op (M.op (M.op x y) x) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq741 eq182
    | exact resolve eq182 eq741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741
  have eq1192 : (M.op (M.op (M.op x y) x) (M.op x (M.op x y))) = (M.op (M.op (M.op x y) x) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq1191 x
       have i₂ := eq729 sF0 x
       grind)
    | exact superpose eq729 eq1191
    | exact resolve eq1191 eq729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1191
  have eq1198 : (M.op (M.op (M.op x y) x) (M.op (M.op x y) x)) = (M.op (M.op (M.op x y) x) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq987 eq1192
    | exact resolve eq1192 eq987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1192
  have eq1205 : ∀ X0 : G, (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) X0) := by
    intro X0
    first
    | exact superpose eq742 eq16
    | exact resolve eq16 eq742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1208 : ∀ X0 : G, (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op (M.op X0 (M.op (σ x) (σ x))) X0) := by
    intro X0
    first
    | exact superpose eq742 eq177
    | exact resolve eq177 eq742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1210 : ∀ X0 : G, (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (M.op (σ x) (σ y))) X0)) := by
    intro X0
    first
    | exact superpose eq742 eq182
    | exact resolve eq182 eq742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1212 : (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op (M.op (M.op x y) x) (M.op (M.op (σ x) (M.op (σ x) (σ y))) y)) := by
    first
    | (have i₁ := eq1210 x
       have i₂ := eq204 (M.op sF2 sF4) x
       grind)
    | exact superpose eq204 eq1210
    | exact resolve eq1210 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1210
  have eq1214 : (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq755 eq1208
    | exact resolve eq1208 eq755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1208
  have eq1217 : (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq713 eq1205
    | exact resolve eq1205 eq713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1205
  have eq1222 : ∀ X0 : G, (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op x (M.op x y))) = (M.op (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) X0) := by
    intro X0
    first
    | exact superpose eq756 eq16
    | exact resolve eq16 eq756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1225 : ∀ X0 : G, (M.op (M.op x (M.op x y)) (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op (M.op X0 (M.op x (σ x))) X0) := by
    intro X0
    first
    | exact superpose eq756 eq177
    | exact resolve eq177 eq756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1227 : ∀ X0 : G, (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op x (M.op x y))) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (M.op (σ x) (σ y))) X0)) := by
    intro X0
    first
    | exact superpose eq756 eq182
    | exact resolve eq182 eq756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1228 : (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op x (M.op x y))) = (M.op (M.op (M.op x y) x) (M.op (M.op (σ x) (M.op (σ x) (σ y))) y)) := by
    first
    | (have i₁ := eq1227 x
       have i₂ := eq204 (M.op sF2 sF4) x
       grind)
    | exact superpose eq204 eq1227
    | exact resolve eq1227 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1227
  have eq1230 : (M.op (M.op x (M.op x y)) (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op (M.op x (σ x)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq755 eq1225
    | exact resolve eq1225 eq755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1225
  have eq1233 : (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op x (M.op x y))) := by
    first
    | exact superpose eq713 eq1222
    | exact resolve eq1222 eq713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1222
  have eq1236 : (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op x (M.op x y))) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1212 eq1228
    | exact resolve eq1228 eq1212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1228
  have eq1238 : (M.op (M.op x (M.op x y)) x) = (M.op (M.op x (σ x)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1175 eq1230
    | exact resolve eq1230 eq1175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1230
  have eq1241 : (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op x (M.op x y))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1214 eq1236
    | exact resolve eq1236 eq1214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1236
  have eq1243 : (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1233 eq1241
    | exact resolve eq1241 eq1233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1233 eq1241
  have eq1252 : ∀ X0 : G, (M.op (M.op (M.op x y) x) (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op (M.op X0 (M.op y (σ x))) X0) := by
    intro X0
    first
    | exact superpose eq757 eq177
    | exact resolve eq177 eq757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1257 : (M.op (M.op (M.op x y) x) (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op (M.op y (σ x)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq755 eq1252
    | exact resolve eq1252 eq755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755 eq1252
  have eq1265 : (M.op (M.op (M.op x y) x) (M.op (M.op x y) x)) = (M.op (M.op y (σ x)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1198 eq1257
    | exact resolve eq1257 eq1198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1198 eq1257
  have eq1370 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) X1)) X0) = (M.op (M.op (σ x) X1) (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x))) := by
    intro X0 X1
    first
    | exact superpose eq650 eq175
    | exact resolve eq175 eq650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1425 : ∀ X1 : G, (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) = (M.op (M.op (σ x) X1) (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x))) := by
    intro X1
    first
    | exact superpose eq713 eq1370
    | exact resolve eq1370 eq713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713 eq1370
  have eq1518 : (M.op (M.op (M.op x y) x) y) = (M.op (M.op (M.op x y) x) (M.op x (M.op x y))) := by
    first
    | exact superpose eq734 eq596
    | exact resolve eq596 eq734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596 eq734
  have eq1710 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) (M.op (M.op (σ x) X0) X1)) = (M.op (M.op (σ x) X0) (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x))) := by
    intro X0 X1
    first
    | exact superpose eq650 eq641
    | exact resolve eq641 eq650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1783 : ∀ X0 X1 : G, (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) = (M.op (M.op (σ x) X0) (M.op (M.op (σ x) X0) X1)) := by
    intro X0 X1
    first
    | exact superpose eq1425 eq1710
    | exact resolve eq1710 eq1425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1425 eq1710
  have eq1827 : ∀ X0 : G, (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) = (M.op (M.op (M.op x y) x) (M.op (M.op (σ x) X0) y)) := by
    intro X0
    first
    | (have i₁ := eq1783 X0 x
       have i₂ := eq204 (M.op sF2 X0) x
       grind)
    | exact superpose eq204 eq1783
    | exact resolve eq1783 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1783
  have eq2169 : ∀ X0 X1 X2 : G, (M.op (M.op X0 y) (M.op (M.op X0 y) X1)) = (M.op (M.op X0 (M.op X0 X2)) (M.op (M.op x y) x)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq179 X0 X2 (M.op X0 y) X1
       have i₂ := eq189 X0
       grind)
    | (have i₁ := eq179 x X1 (M.op x y) x
       have i₂ := eq189 X1
       grind)
    | exact superpose eq189 eq179
    | exact resolve eq179 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2170 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (σ x)) (M.op (M.op X0 (σ x)) X1)) = (M.op (M.op X0 (M.op X0 X2)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq709 eq179
    | exact resolve eq179 eq709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2184 : ∀ X0 X1 : G, (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (M.op (σ x) (σ y))) X0)) = (M.op (M.op (M.op x (σ x)) (M.op (M.op x (σ x)) X1)) (M.op x (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq756 eq179
    | exact resolve eq179 eq756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756
  have eq2185 : ∀ X0 X1 : G, (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (M.op (σ x) (σ y))) X0)) = (M.op (M.op (M.op y (σ x)) (M.op (M.op y (σ x)) X1)) (M.op (M.op x y) x)) := by
    intro X0 X1
    first
    | exact superpose eq757 eq179
    | exact resolve eq179 eq757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757
  have eq2186 : ∀ X0 X1 : G, (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (M.op (σ x) (σ y))) X0)) = (M.op (M.op (M.op (σ x) (σ x)) (M.op (M.op (σ x) (σ x)) X1)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq742 eq179
    | exact resolve eq179 eq742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742
  have eq2269 : ∀ X0 : G, (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (M.op (σ x) (σ y))) X0)) = (M.op (M.op (M.op (σ x) (σ x)) (M.op (σ x) (M.op (σ x) (σ y)))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq751 eq2186
    | exact resolve eq2186 eq751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2186
  have eq2270 : ∀ X0 : G, (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (M.op (σ x) (σ y))) X0)) = (M.op (M.op (M.op y (σ x)) (M.op (σ x) (M.op (σ x) (σ y)))) (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq751 eq2185
    | exact resolve eq2185 eq751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2185
  have eq2271 : ∀ X0 : G, (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (M.op (σ x) (σ y))) X0)) = (M.op (M.op (M.op x (σ x)) (M.op (σ x) (M.op (σ x) (σ y)))) (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq751 eq2184
    | exact resolve eq2184 eq751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2184
  have eq2285 : ∀ X0 X2 : G, (M.op (M.op X0 (σ x)) (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op (M.op X0 (M.op X0 X2)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0 X2
    first
    | exact superpose eq751 eq2170
    | exact resolve eq2170 eq751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751 eq2170
  have eq2286 : ∀ X0 X2 : G, (M.op (M.op X0 y) (M.op (M.op x y) x)) = (M.op (M.op X0 (M.op X0 X2)) (M.op (M.op x y) x)) := by
    intro X0 X2
    first
    | (have i₁ := eq2169 X0 x X2
       have i₂ := eq645 X0 x
       grind)
    | (have i₁ := eq2169 x x X2
       have i₂ := eq645 x x
       grind)
    | exact superpose eq645 eq2169
    | exact resolve eq2169 eq645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645 eq2169
  have eq2328 : ∀ X0 : G, (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (M.op (σ x) (σ y))) X0)) = (M.op (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq1243 eq2269
    | exact resolve eq2269 eq1243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2269
  have eq2329 : ∀ X0 : G, (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (M.op (σ x) (σ y))) X0)) = (M.op (M.op (M.op (M.op x y) x) (M.op (M.op x y) x)) (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq1265 eq2270
    | exact resolve eq2270 eq1265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1265 eq2270
  have eq2330 : ∀ X0 : G, (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (M.op (σ x) (σ y))) X0)) = (M.op (M.op (M.op x (M.op x y)) x) (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq1238 eq2271
    | exact resolve eq2271 eq1238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1238 eq2271
  have eq2349 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (M.op (σ x) (σ y))) X0)) := by
    intro X0
    first
    | (have i₁ := eq2328 X0
       have i₂ := eq594 (M.op sF2 sF4) sF2
       grind)
    | exact superpose eq594 eq2328
    | exact resolve eq2328 eq594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2328
  have eq2350 : ∀ X0 : G, (M.op (M.op (M.op x y) x) (M.op x (M.op x y))) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (M.op (σ x) (σ y))) X0)) := by
    intro X0
    first
    | (have i₁ := eq2329 X0
       have i₂ := eq733 sF0 (M.op sF0 x)
       grind)
    | exact superpose eq733 eq2329
    | exact resolve eq2329 eq733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq733 eq2329
  have eq2351 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op x (σ y))) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (M.op (σ x) (σ y))) X0)) := by
    intro X0
    first
    | (have i₁ := eq2330 X0
       have i₂ := eq594 (M.op x sF0) x
       grind)
    | exact superpose eq594 eq2330
    | exact resolve eq2330 eq594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594 eq2330
  have eq2360 : (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op x y) x) (M.op (M.op (σ x) (M.op (σ x) (σ y))) y)) := by
    first
    | (have i₁ := eq2349 x
       have i₂ := eq204 (M.op sF2 sF4) x
       grind)
    | exact superpose eq204 eq2349
    | exact resolve eq2349 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2349
  have eq2361 : (M.op (M.op (M.op x y) x) (M.op x (M.op x y))) = (M.op (M.op (M.op x y) x) (M.op (M.op (σ x) (M.op (σ x) (σ y))) y)) := by
    first
    | (have i₁ := eq2350 x
       have i₂ := eq204 (M.op sF2 sF4) x
       grind)
    | exact superpose eq204 eq2350
    | exact resolve eq2350 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2350
  have eq2362 : (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op x (σ y))) = (M.op (M.op (M.op x y) x) (M.op (M.op (σ x) (M.op (σ x) (σ y))) y)) := by
    first
    | (have i₁ := eq2351 x
       have i₂ := eq204 (M.op sF2 sF4) x
       grind)
    | exact superpose eq204 eq2351
    | exact resolve eq2351 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2351
  have eq2370 : (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1212 eq2360
    | exact resolve eq2360 eq1212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2360
  have eq2371 : (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) = (M.op (M.op (M.op x y) x) (M.op x (M.op x y))) := by
    first
    | exact superpose eq1827 eq2361
    | exact resolve eq2361 eq1827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1827 eq2361
  have eq2372 : (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op x (σ y))) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1212 eq2362
    | exact resolve eq2362 eq1212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1212 eq2362
  have eq2375 : (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1214 eq2370
    | exact resolve eq2370 eq1214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2370
  have eq2376 : (M.op (M.op (M.op x y) x) y) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq1518 eq2371
    | exact resolve eq2371 eq1518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1518 eq2371
  have eq2377 : (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op x (σ y))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1214 eq2372
    | exact resolve eq2372 eq1214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1214 eq2372
  have eq2380 : (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1243 eq2375
    | exact resolve eq2375 eq1243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2375
  have eq2381 : (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op x (σ y))) := by
    first
    | exact superpose eq1243 eq2377
    | exact resolve eq2377 eq1243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1243 eq2377
  have eq2382 : (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq2380
    | exact resolve eq2380 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2380
  have eq2383 : (M.op x (M.op x y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq721 eq2381
    | exact resolve eq2381 eq721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721 eq2381
  have eq2384 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq709 eq2382
    | exact resolve eq2382 eq709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2382
  have eq2386 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq875
       grind)
    | exact superpose eq875 eq40
    | exact resolve eq40 eq875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq2387 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2386
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2386
    | exact resolve eq2386 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2386
  have eq2389 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq2387
    | exact resolve eq2387 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2387
  have eq2397 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) X0) = (M.op (M.op (σ x) (σ y)) (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq2383 eq175
    | exact resolve eq175 eq2383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2399 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq2383 eq177
    | exact resolve eq177 eq2383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2406 : ∀ X0 : G, (M.op (σ x) (M.op (M.op X0 (σ x)) X0)) = (M.op (M.op x (M.op x y)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq2383 eq175
    | exact resolve eq175 eq2383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2421 : ∀ X0 : G, (M.op (M.op x (M.op x y)) x) = (M.op (σ x) (M.op (M.op X0 (σ x)) X0)) := by
    intro X0
    first
    | exact superpose eq1175 eq2406
    | exact resolve eq2406 eq1175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1175 eq2406
  have eq2426 : (M.op x (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op x (M.op x y))) := by
    first
    | exact superpose eq2399 eq2397
    | exact resolve eq2397 eq2399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2397
  have eq2433 : (M.op (M.op x (M.op x y)) x) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq709 eq2421
    | exact resolve eq2421 eq709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2421
  have eq2441 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op x (M.op x y)) x) := by
    first
    | exact superpose eq650 eq2433
    | exact resolve eq2433 eq650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2433
  have eq2454 : (M.op x (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2384 eq2383
    | exact resolve eq2383 eq2384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2383
  have eq2456 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) X0) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq2384 eq175
    | exact resolve eq175 eq2384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2458 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op (σ x) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq2384 eq177
    | exact resolve eq177 eq2384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2460 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq2384 eq709
    | exact resolve eq709 eq2384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709 eq2384
  have eq2485 : (M.op x (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq2399 eq2456
    | exact resolve eq2456 eq2399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2456
  have eq2494 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq2454 eq2485
    | exact resolve eq2485 eq2454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2485
  have eq2513 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op x (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq2454 eq647
    | exact resolve eq647 eq2454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647
  have eq2558 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 (M.op (σ x) (σ y)))) X1) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op x (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq2399 eq16
    | exact resolve eq16 eq2399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2568 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op x (M.op x y))) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (M.op X0 (M.op (σ x) (σ y))) X1)) := by
    intro X0 X1
    first
    | exact superpose eq2399 eq182
    | exact resolve eq182 eq2399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2588 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (M.op X0 (M.op (σ x) (σ y))) X1)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq2454 eq2568
    | exact resolve eq2568 eq2454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2568
  have eq2598 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 (M.op (σ x) (σ y)))) X1) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq2454 eq2558
    | exact resolve eq2558 eq2454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2558
  have eq2695 : ∀ X0 : G, (M.op (M.op X0 (M.op x (M.op x y))) X0) = (M.op (M.op x (M.op x y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq2426 eq177
    | exact resolve eq177 eq2426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2426
  have eq2705 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) X0) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq2454 eq2695
    | exact resolve eq2695 eq2454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2695
  have eq2712 : (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2598 eq2705
    | exact resolve eq2705 eq2598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2705
  have eq2716 : (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1217 eq2712
    | exact resolve eq2712 eq1217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1217 eq2712
  have eq2720 : (M.op x (M.op x y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2399 eq2716
    | exact resolve eq2716 eq2399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2716
  have eq2724 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2454 eq2720
    | exact resolve eq2720 eq2454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2720
  have eq2728 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) x) := by
    first
    | exact superpose eq2454 eq2441
    | exact resolve eq2441 eq2454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2735 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) X0) = (M.op (M.op x y) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq2441 eq175
    | exact resolve eq175 eq2441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2737 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq2441 eq177
    | exact resolve eq177 eq2441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2746 : ∀ X0 : G, (M.op (M.op X0 x) X0) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq2441 eq177
    | exact resolve eq177 eq2441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2441
  have eq2757 : ∀ X0 : G, (M.op (M.op X0 x) X0) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq2454 eq2746
    | exact resolve eq2746 eq2454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2746
  have eq2765 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op x y) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq2737 eq2735
    | exact resolve eq2735 eq2737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2735
  have eq2773 : ∀ X0 : G, (M.op (M.op X0 x) X0) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq2460 eq2757
    | exact resolve eq2757 eq2460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2460 eq2757
  have eq2823 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X2)) (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (M.op X0 (M.op (σ x) (σ y))) X1)) := by
    intro X0 X1 X2
    first
    | exact superpose eq2458 eq179
    | exact resolve eq179 eq2458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2844 : ∀ X0 X2 : G, (M.op (M.op X0 (M.op X0 X2)) (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0 X2
    first
    | exact superpose eq2588 eq2823
    | exact resolve eq2823 eq2588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2823
  have eq2853 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq2285 eq2844
    | exact resolve eq2844 eq2285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2844
  have eq2977 : (M.op x (M.op x y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq2724 eq2399
    | exact resolve eq2399 eq2724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2399
  have eq2998 : (M.op x (M.op x y)) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq2853 eq2977
    | exact resolve eq2977 eq2853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2977
  have eq3008 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq2454 eq2998
    | exact resolve eq2998 eq2454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2998
  have eq3074 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op x (M.op x y)) (M.op (M.op x y) x)) := by
    first
    | (have i₁ := eq2737 (M.op sF0 x)
       have i₂ := eq693 sF0
       grind)
    | exact superpose eq693 eq2737
    | exact resolve eq2737 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3106 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op (M.op X0 (M.op x y)) (M.op (M.op X0 (M.op x y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq2737 eq182
    | exact resolve eq182 eq2737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2737
  have eq3133 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (M.op x y) x)) := by
    first
    | exact superpose eq2454 eq3074
    | exact resolve eq3074 eq2454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3074
  have eq3187 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) X0) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq2765 eq177
    | exact resolve eq177 eq2765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2765
  have eq3197 : (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op x y)) := by
    first
    | exact superpose eq2598 eq3187
    | exact resolve eq3187 eq2598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2598 eq3187
  have eq3203 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op x y)) := by
    first
    | exact superpose eq2853 eq3197
    | exact resolve eq3197 eq2853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3197
  have eq3205 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op x y)) := by
    first
    | exact superpose eq3008 eq3203
    | exact resolve eq3203 eq3008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3008 eq3203
  have eq3246 : ∀ X0 X1 X2 : G, (M.op (M.op X0 x) (M.op (M.op X0 x) X1)) = (M.op (M.op X0 (M.op X0 X2)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq179 X0 X2 (M.op X0 x) X1
       have i₂ := eq2773 X0
       grind)
    | exact superpose eq2773 eq179
    | exact resolve eq179 eq2773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2773
  have eq3269 : ∀ X0 X1 : G, (M.op (M.op X0 x) (M.op (M.op X0 x) X1)) = (M.op (M.op X0 (σ x)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq2285 eq3246
    | exact resolve eq3246 eq2285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2285 eq3246
  have eq3400 : (M.op (M.op (M.op x y) x) y) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2376 eq2458
    | exact resolve eq2458 eq2376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2376 eq2458
  have eq3473 : ∀ X0 : G, (M.op (M.op X0 y) X0) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq3400 eq177
    | exact resolve eq177 eq3400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3400
  have eq3481 : ∀ X0 : G, (M.op (M.op X0 y) X0) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq3133 eq3473
    | exact resolve eq3473 eq3133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3133 eq3473
  have eq3491 : (M.op (M.op x y) x) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq3481 x
       have i₂ := eq189 x
       grind)
    | (have i₁ := eq3481 x
       have i₂ := eq189 x
       grind)
    | exact superpose eq189 eq3481
    | (have j0 := eq3481 x
       grind)
    | exact resolve eq3481 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189 eq3481
  have eq3521 : (M.op (M.op x y) x) = (M.op (M.op (σ x) (σ y)) (M.op (M.op x y) x)) := by
    first
    | exact superpose eq3491 eq2494
    | exact resolve eq2494 eq3491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2494
  have eq3522 : (M.op (M.op x y) x) = (M.op x (M.op (M.op x y) x)) := by
    first
    | exact superpose eq3491 eq2513
    | exact resolve eq2513 eq3491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2513
  have eq3524 : (M.op (M.op x y) x) = (M.op (M.op (M.op x y) x) x) := by
    first
    | exact superpose eq3491 eq2728
    | exact resolve eq2728 eq3491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2728
  have eq3526 : (M.op (M.op x y) x) = (M.op (M.op (M.op x y) x) (M.op x y)) := by
    first
    | exact superpose eq3491 eq3205
    | exact resolve eq3205 eq3491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3205
  have eq3549 : (M.op (M.op x y) x) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq3526
       have i₂ := eq693 sF0
       grind)
    | exact superpose eq693 eq3526
    | exact resolve eq3526 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693 eq3526
  have eq3583 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) X0) = (M.op (M.op (M.op x y) x) x) := by
    intro X0
    first
    | exact superpose eq3549 eq177
    | exact resolve eq177 eq3549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3594 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op X0 (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq3524 eq3583
    | exact resolve eq3583 eq3524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3524 eq3583
  have eq3610 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) X0) = (M.op (M.op (σ x) (σ y)) (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq3521 eq16
    | exact resolve eq16 eq3521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3625 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op X0 (M.op (σ x) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq3521 eq3610
    | exact resolve eq3610 eq3521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3521 eq3610
  have eq3645 : ∀ X0 : G, (M.op (M.op X0 x) X0) = (M.op x (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq3522 eq16
    | exact resolve eq16 eq3522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3660 : ∀ X0 : G, (M.op (M.op X0 x) X0) = (M.op (M.op x y) x) := by
    intro X0
    first
    | exact superpose eq3522 eq3645
    | exact resolve eq3645 eq3522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3522 eq3645
  have eq4066 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X2)) (M.op (M.op x y) x)) = (M.op (M.op X0 (M.op x y)) (M.op (M.op X0 (M.op x y)) X1)) := by
    intro X0 X1 X2
    first
    | exact superpose eq3594 eq179
    | exact resolve eq179 eq3594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4095 : ∀ X0 X2 : G, (M.op (M.op X0 (M.op X0 X2)) (M.op (M.op x y) x)) = (M.op (M.op X0 (M.op x y)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0 X2
    first
    | exact superpose eq3106 eq4066
    | exact resolve eq4066 eq3106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3106 eq4066
  have eq4111 : ∀ X0 X2 : G, (M.op (M.op X0 (M.op X0 X2)) (M.op (M.op x y) x)) = (M.op (M.op X0 (M.op x y)) (M.op (M.op x y) x)) := by
    intro X0 X2
    first
    | exact superpose eq3491 eq4095
    | exact resolve eq4095 eq3491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4095
  have eq5036 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X2)) (M.op (M.op x y) x)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (M.op X0 (M.op (σ x) (σ y))) X1)) := by
    intro X0 X1 X2
    first
    | exact superpose eq3625 eq179
    | exact resolve eq179 eq3625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3625
  have eq5069 : ∀ X0 X2 : G, (M.op (M.op X0 (M.op X0 X2)) (M.op (M.op x y) x)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0 X2
    first
    | exact superpose eq2588 eq5036
    | exact resolve eq5036 eq2588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2588 eq5036
  have eq5092 : ∀ X0 X2 : G, (M.op (M.op X0 (σ x)) (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op (M.op X0 (M.op X0 X2)) (M.op (M.op x y) x)) := by
    intro X0 X2
    first
    | exact superpose eq2853 eq5069
    | exact resolve eq5069 eq2853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2853 eq5069
  have eq5101 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op (M.op X0 (M.op x y)) (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq4111 eq5092
    | exact resolve eq5092 eq4111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4111 eq5092
  have eq5106 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) (M.op (M.op x y) x)) = (M.op (M.op X0 (σ x)) (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq3491 eq5101
    | exact resolve eq5101 eq3491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5101
  have eq5156 : ∀ X0 X1 X2 : G, (M.op (M.op X0 x) (M.op (M.op X0 x) X1)) = (M.op (M.op X0 (M.op X0 X2)) (M.op (M.op x y) x)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq179 X0 X2 (M.op X0 x) X1
       have i₂ := eq3660 X0
       grind)
    | exact superpose eq3660 eq179
    | exact resolve eq179 eq3660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq5159 : ∀ X0 X1 : G, (M.op (M.op X0 x) (M.op (M.op X0 x) X1)) = (M.op (M.op X0 x) (M.op (M.op x y) x)) := by
    intro X0 X1
    first
    | (have i₁ := eq182 (M.op X0 x) X1 X0
       have i₂ := eq3660 X0
       grind)
    | exact superpose eq3660 eq182
    | exact resolve eq182 eq3660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182 eq3660
  have eq5187 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op (M.op X0 x) (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq5159 X0 x
       have i₂ := eq3269 X0 x
       grind)
    | exact superpose eq3269 eq5159
    | exact resolve eq5159 eq3269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3269 eq5159
  have eq5190 : ∀ X0 X1 : G, (M.op (M.op X0 y) (M.op (M.op x y) x)) = (M.op (M.op X0 x) (M.op (M.op X0 x) X1)) := by
    intro X0 X1
    first
    | exact superpose eq2286 eq5156
    | exact resolve eq5156 eq2286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5156
  have eq5212 : ∀ X0 : G, (M.op (M.op X0 x) (M.op (M.op x y) x)) = (M.op (M.op X0 (σ x)) (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq3491 eq5187
    | exact resolve eq5187 eq3491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5187
  have eq5214 : ∀ X0 : G, (M.op (M.op X0 y) (M.op (M.op x y) x)) = (M.op (M.op X0 x) (M.op x (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq5190 X0 x
       have i₂ := eq729 X0 x
       grind)
    | exact superpose eq729 eq5190
    | exact resolve eq5190 eq729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5190
  have eq5225 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) (M.op (M.op x y) x)) = (M.op (M.op X0 x) (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq5106 eq5212
    | exact resolve eq5212 eq5106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5106 eq5212
  have eq5227 : ∀ X0 : G, (M.op (M.op X0 y) (M.op (M.op x y) x)) = (M.op (M.op X0 x) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq2454 eq5214
    | exact resolve eq5214 eq2454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5214
  have eq5232 : ∀ X0 : G, (M.op (M.op X0 y) (M.op (M.op x y) x)) = (M.op (M.op X0 x) (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq3491 eq5227
    | exact resolve eq5227 eq3491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5227
  have eq5235 : ∀ X0 : G, (M.op (M.op X0 y) (M.op (M.op x y) x)) = (M.op (M.op X0 (M.op x y)) (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq5225 eq5232
    | exact resolve eq5232 eq5225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5232
  have eq6830 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) (M.op (M.op x y) x)) = (M.op (M.op (M.op X1 X0) X1) X0) := by
    intro X0 X1
    first
    | exact superpose eq3594 eq178
    | exact resolve eq178 eq3594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3594
  have eq20612 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X0 (M.op X0 X1))) X2) = (M.op (M.op X0 (M.op X0 X1)) (M.op (M.op x y) x)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X0 (M.op X0 X1)) (M.op y X0) X2
       have i₂ := eq200 X0 X1
       grind)
    | exact superpose eq200 eq16
    | exact resolve eq16 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20656 : ∀ X0 X1 X2 : G, (M.op (M.op X0 y) (M.op (M.op x y) x)) = (M.op (M.op X2 (M.op X0 (M.op X0 X1))) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq2286 eq20612
    | exact resolve eq20612 eq2286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2286 eq20612
  have eq20868 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X0 (M.op X0 X1))) X2) = (M.op (M.op X0 (M.op x y)) (M.op (M.op x y) x)) := by
    intro X0 X1 X2
    first
    | exact superpose eq5235 eq20656
    | exact resolve eq20656 eq5235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5235 eq20656
  have eq21055 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op (M.op (M.op X0 X1) X0) X1)) = (M.op (M.op (M.op x y) x) (M.op (M.op X1 X2) y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq204 (M.op X1 X2) (M.op (M.op X1 X2) x)
       have i₂ := eq178 X0 X1 X2 x
       grind)
    | exact superpose eq178 eq204
    | exact resolve eq204 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21278 : ∀ X0 X1 X3 : G, (M.op (M.op (M.op x y) x) (M.op (M.op X0 X1) y)) = (M.op (M.op (M.op X3 X0) X3) X0) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq178 X3 X0 X1 x
       have i₂ := eq204 (M.op X0 X1) x
       grind)
    | (have i₁ := eq178 X0 (M.op x y) x y
       have i₂ := eq204 (M.op (M.op x y) x) X1
       grind)
    | exact superpose eq204 eq178
    | exact resolve eq178 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21379 : ∀ X0 X1 : G, (M.op (M.op x y) x) = (M.op (M.op (M.op (M.op x y) x) (M.op X0 (M.op X0 X1))) (M.op y (M.op (M.op x y) x))) := by
    intro X0 X1
    first
    | (have i₁ := eq200 X0 (M.op X0 X1)
       have i₂ := eq204 X0 X1
       grind)
    | exact superpose eq204 eq200
    | exact resolve eq200 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200 eq204
  have eq21394 : ∀ X0 X1 : G, (M.op (M.op x y) x) = (M.op (M.op (M.op (M.op x y) x) (M.op X0 (M.op X0 X1))) (M.op (M.op x y) x)) := by
    intro X0 X1
    first
    | exact superpose eq186 eq21379
    | exact resolve eq21379 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186 eq21379
  have eq21444 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) (M.op (M.op x y) x)) = (M.op (M.op (M.op x y) x) (M.op (M.op X0 X1) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq21278 X0 X1 x
       have i₂ := eq6830 X0 x
       grind)
    | exact superpose eq6830 eq21278
    | exact resolve eq21278 eq6830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21278
  have eq21513 : ∀ X1 X2 : G, (M.op (M.op X1 X2) (M.op (M.op X1 (M.op x y)) (M.op (M.op x y) x))) = (M.op (M.op (M.op x y) x) (M.op (M.op X1 X2) y)) := by
    intro X1 X2
    first
    | (have i₁ := eq21055 x X1 X2
       have i₂ := eq6830 X1 x
       grind)
    | exact superpose eq6830 eq21055
    | exact resolve eq21055 eq6830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6830 eq21055
  have eq21551 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op X0 (M.op x y)) (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq21394 X0 x
       have i₂ := eq20868 X0 x (M.op sF0 x)
       grind)
    | exact superpose eq20868 eq21394
    | exact resolve eq21394 eq20868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20868 eq21394
  have eq21610 : ∀ X1 X2 : G, (M.op (M.op X1 (M.op x y)) (M.op (M.op x y) x)) = (M.op (M.op X1 X2) (M.op (M.op X1 (M.op x y)) (M.op (M.op x y) x))) := by
    intro X1 X2
    first
    | exact superpose eq21444 eq21513
    | exact resolve eq21513 eq21444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21444 eq21513
  have eq21639 : ∀ X1 X2 : G, (M.op (M.op x y) x) = (M.op (M.op X1 X2) (M.op (M.op x y) x)) := by
    intro X1 X2
    first
    | exact superpose eq21551 eq21610
    | exact resolve eq21610 eq21551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21610
  have eq22110 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x y) x) := by
    intro X0 X1
    first
    | exact superpose eq21639 eq16
    | exact resolve eq16 eq21639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22112 : ∀ X0 X1 : G, (M.op (M.op x y) x) = (M.op X0 (M.op (M.op X1 X0) X1)) := by
    intro X0 X1
    first
    | exact superpose eq21639 eq175
    | exact resolve eq175 eq21639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq22114 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op x y) x) := by
    intro X0 X1
    first
    | exact superpose eq21639 eq177
    | exact resolve eq177 eq21639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq22115 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) x) X0) = (M.op (M.op X0 X1) (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq21639 eq178
    | exact resolve eq178 eq21639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq22116 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op (M.op x y) x)) := by
    intro X0 X1
    first
    | exact superpose eq21639 eq641
    | exact resolve eq641 eq21639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641
  have eq22191 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) x) X0) = (M.op (M.op X0 X1) (M.op (M.op x y) x)) := by
    intro X0 X1
    first
    | (have i₁ := eq22115 X0 X1 x
       have i₂ := eq22116 (M.op X0 X1) x
       grind)
    | (have i₁ := eq22115 x y x
       have i₂ := eq22116 (M.op x y) X1
       grind)
    | exact superpose eq22116 eq22115
    | exact resolve eq22115 eq22116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22115 eq22116
  have eq22192 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op X0 (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq22112 X0 x
       have i₂ := eq22114 x X0
       grind)
    | (have i₁ := eq22112 y x
       have i₂ := eq22114 X0 x
       grind)
    | exact superpose eq22114 eq22112
    | exact resolve eq22112 eq22114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22112
  have eq22210 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op (M.op x y) x) X0) := by
    intro X0
    first
    | exact superpose eq21639 eq22191
    | exact resolve eq22191 eq21639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21639 eq22191
  have eq23292 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) x) (M.op (M.op (M.op x y) x) X0)) = (k (M.op (M.op x y) x) X1) ∨ (M.op X1 X1) = X1 ∨ (M.op (M.op (M.op x y) x) (M.op (M.op x y) x)) = X1 := by
    intro X0 X1
    first
    | exact superpose eq22192 eq866
    | (have j0 := eq866 X1 X1 x
       grind)
    | exact resolve eq866 eq22192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq866
  have eq23379 : ∀ X1 : G, (M.op (M.op (M.op x y) x) (M.op x (M.op x y))) = (k (M.op (M.op x y) x) X1) ∨ (M.op X1 X1) = X1 ∨ (M.op (M.op (M.op x y) x) (M.op (M.op x y) x)) = X1 := by
    intro X1
    first
    | (have i₁ := eq23292 X1 X1
       have i₂ := eq729 sF0 X1
       grind)
    | exact superpose eq729 eq23292
    | (have j0 := eq23292 x X1
       grind)
    | exact resolve eq23292 eq729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729 eq23292
  have eq23401 : ∀ X1 : G, (M.op (M.op (M.op x y) x) (M.op (M.op x y) x)) = (k (M.op (M.op x y) x) X1) ∨ (M.op X1 X1) = X1 ∨ (M.op (M.op (M.op x y) x) (M.op (M.op x y) x)) = X1 := by
    intro X1
    first
    | exact superpose eq987 eq23379
    | (have j0 := eq23379 X1
       grind)
    | exact resolve eq23379 eq987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq987 eq23379
  have eq23409 : ∀ X1 : G, (M.op (M.op (M.op x y) x) (M.op (M.op x y) x)) = (k (M.op (M.op x y) x) X1) ∨ (M.op (M.op (M.op x y) x) (M.op (M.op x y) x)) = X1 := by
    intro X1
    first
    | (have j0 := eq23401 X1
       have j1 := eq12 (M.op (M.op x y) x) X1
       grind)
    | (have r₁ := eq23401 X1
       have r₂ := eq12 x X1
       grind)
    | (have r₁ := eq23401 (M.op (M.op x y) x)
       have r₂ := eq12 x (M.op (M.op x y) x)
       grind)
    | (have r₁ := eq23401 (M.op (M.op (M.op (M.op x y) x) (M.op (M.op x y) x)) (M.op (M.op (M.op x y) x) (M.op (M.op x y) x)))
       have r₂ := eq12 x (M.op (M.op (M.op x y) x) (M.op (M.op x y) x))
       grind)
    | exact resolve eq23401 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23401
  have eq23412 : ∀ X1 : G, (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) x)) = (k (M.op (M.op x y) x) X1) ∨ (M.op (M.op (M.op x y) x) (M.op (M.op x y) x)) = X1 := by
    intro X1
    first
    | exact superpose eq5225 eq23409
    | (have j0 := eq23409 X1
       grind)
    | exact resolve eq23409 eq5225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23409
  have eq23413 : ∀ X1 : G, (M.op (M.op x y) x) = (k (M.op (M.op x y) x) X1) ∨ (M.op (M.op (M.op x y) x) (M.op (M.op x y) x)) = X1 := by
    intro X1
    first
    | exact superpose eq21551 eq23412
    | (have j0 := eq23412 X1
       grind)
    | exact resolve eq23412 eq21551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23412
  have eq23414 : ∀ X1 : G, (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) x)) = X1 ∨ (M.op (M.op x y) x) = (k (M.op (M.op x y) x) X1) := by
    intro X1
    first
    | exact superpose eq5225 eq23413
    | (have j0 := eq23413 X1
       grind)
    | exact resolve eq23413 eq5225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5225 eq23413
  have eq23415 : ∀ X1 : G, (M.op (M.op x y) x) = (k (M.op (M.op x y) x) X1) ∨ (M.op (M.op x y) x) = X1 := by
    intro X1
    first
    | exact superpose eq21551 eq23414
    | (have j0 := eq23414 X1
       grind)
    | exact resolve eq23414 eq21551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21551 eq23414
  have eq160039 : (M.op (M.op x y) x) = (σ (M.op (τ (M.op (M.op x y) x)) (τ (M.op (M.op x y) x)))) ∨ (M.op (M.op x y) x) = (σ (M.op (τ (M.op (M.op x y) x)) (τ (M.op (M.op x y) x)))) := by
    first
    | exact superpose eq23415 eq334
    | (have j1 := eq23415 (σ (M.op (τ (M.op (M.op x y) x)) (τ (M.op (M.op x y) x))))
       grind)
    | exact resolve eq334 eq23415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334 eq23415
  have eq160074 : (M.op (M.op x y) x) = (σ (M.op (τ (M.op (M.op x y) x)) (τ (M.op (M.op x y) x)))) := by grind
  clear eq160039
  have eq160088 : (τ (M.op (M.op x y) x)) = (M.op (τ (M.op (M.op x y) x)) (τ (M.op (M.op x y) x))) := by
    first
    | exact superpose eq160074 eq15
    | exact resolve eq15 eq160074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq160331 : (M.op (M.op x y) x) = (M.op (τ (M.op (M.op x y) x)) (τ (M.op (M.op x y) x))) := by
    first
    | exact superpose eq160088 eq22114
    | exact resolve eq22114 eq160088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq160464 : (M.op (M.op x y) x) = (τ (M.op (M.op x y) x)) := by
    first
    | exact superpose eq160331 eq160088
    | exact resolve eq160088 eq160331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160088
  have eq160465 : (M.op (M.op x y) x) = (σ (M.op (M.op x y) x)) := by
    first
    | exact superpose eq160331 eq160074
    | exact resolve eq160074 eq160331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160074 eq160331
  have eq186423 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq2389 eq882
    | exact resolve eq882 eq2389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186432 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq186423
       have r₂ := eq27
       grind)
    | exact resolve eq186423 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186423
  have eq186441 : (τ (σ y)) = (k y (τ (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq186432 eq227
    | exact resolve eq227 eq186432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186432
  have eq186611 : y = (k y y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq31 eq186441
    | exact resolve eq186441 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186441
  have eq186663 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k y y) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq186611
       have r₂ := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq186611
       have r₂ := eq13 y y
       grind)
    | (have r₁ := eq186611
       have r₂ := eq13 x y
       grind)
    | exact resolve eq186611 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186611
  have eq186696 : (τ (σ y)) = (k x (τ (σ y))) ∨ y = (k y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq186663 eq216
    | exact resolve eq216 eq186663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216 eq186663
  have eq186875 : y = (k x y) ∨ y = (k y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq31 eq186696
    | exact resolve eq186696 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186696
  have eq186932 : y = (k y y) ∨ y = (k x y) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq186875
       have r₂ := eq13 x y
       grind)
    | exact resolve eq186875 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186875
  have eq186974 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq914 y
       have i₂ := eq186932
       grind)
    | exact superpose eq186932 eq914
    | (have j0 := eq914 y
       grind)
    | exact resolve eq914 eq186932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186978 : y ≠ y ∨ y = (M.op y y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq891 y
       have i₂ := eq186932
       grind)
    | exact superpose eq186932 eq891
    | (have j0 := eq891 y
       grind)
    | (have r₁ := eq891 y
       have r₂ := eq186932
       grind)
    | exact resolve eq891 eq186932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq891 eq186932
  have eq186981 : y = (k x y) ∨ y = (M.op y y) := by grind
  clear eq186978
  have eq186983 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (k x y) := by grind
  clear eq186974
  have eq186985 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq186983
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq186983
    | exact resolve eq186983 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186983
  have eq186993 : y = (M.op x y) ∨ y = (M.op y y) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq875
       have i₂ := eq186981
       grind)
    | exact superpose eq186981 eq875
    | exact resolve eq875 eq186981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq875
  have eq186994 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq35 y
       have i₂ := eq186981
       grind)
    | exact superpose eq186981 eq35
    | exact resolve eq35 eq186981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186981
  have eq186998 : y = (M.op y y) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq186993
  have eq187002 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq186994
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq186994
    | exact resolve eq186994 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186994
  have eq187106 : (M.op (M.op x y) x) = (M.op (σ y) (σ y)) ∨ y = (k x y) := by
    first
    | exact superpose eq186985 eq22114
    | exact resolve eq22114 eq186985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187115 : (σ y) = (M.op (M.op x y) x) ∨ y = (k x y) := by
    first
    | exact superpose eq186985 eq187106
    | exact resolve eq187106 eq186985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186985 eq187106
  have eq187285 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y y) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq187002 eq2389
    | exact resolve eq2389 eq187002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2389 eq187002
  have eq187293 : y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by grind
  clear eq187285
  have eq187492 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ y = (k x y) := by
    intro X0
    first
    | exact superpose eq187115 eq22192
    | exact resolve eq22192 eq187115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187115
  have eq188307 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq187492 eq26
    | (have j1 := eq187492 (σ x)
       grind)
    | exact resolve eq26 eq187492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187492
  have eq188796 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq35 y
       have i₂ := eq188307
       grind)
    | exact superpose eq188307 eq35
    | exact resolve eq35 eq188307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq188307
  have eq188801 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq188796
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq188796
    | exact resolve eq188796 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188796
  have eq201468 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq188801 eq882
    | exact resolve eq882 eq188801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq882 eq188801
  have eq201473 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq201468
  have eq205047 : (M.op (M.op x y) x) = (M.op y y) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq22114 y y
       have i₂ := eq186998
       grind)
    | exact superpose eq186998 eq22114
    | exact resolve eq22114 eq186998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq205056 : y = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq186998 eq205047
    | exact resolve eq205047 eq186998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186998 eq205047
  have eq205553 : (M.op (M.op x y) x) = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq22114 y y
       have i₂ := eq187293
       grind)
    | exact superpose eq187293 eq22114
    | exact resolve eq22114 eq187293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq205562 : y = (M.op (M.op x y) x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq187293 eq205553
    | exact resolve eq205553 eq187293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187293 eq205553
  have eq206132 : ∀ X0 : G, y = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | exact superpose eq205056 eq22192
    | exact resolve eq22192 eq205056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq206140 : y = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq205056 eq160465
    | exact resolve eq160465 eq205056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205056
  have eq206364 : y = (M.op x x) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq206140
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq206140
    | exact resolve eq206140 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206140
  have eq206703 : (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq22110 x x
       have i₂ := eq206364
       grind)
    | exact superpose eq206364 eq22110
    | exact resolve eq22110 eq206364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206364
  have eq206714 : (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq206703
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq206703
    | exact resolve eq206703 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206703
  have eq207146 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | exact superpose eq206714 eq160465
    | exact resolve eq160465 eq206714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq207374 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | exact superpose eq20 eq207146
    | exact resolve eq207146 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207146
  have eq226907 : ∀ X0 : G, y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | exact superpose eq205562 eq22192
    | exact resolve eq22192 eq205562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq226915 : y = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq205562 eq160465
    | exact resolve eq160465 eq205562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205562
  have eq227151 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq226915
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq226915
    | exact resolve eq226915 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226915
  have eq227504 : (M.op x y) = (M.op (M.op x y) x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq22110 x x
       have i₂ := eq227151
       grind)
    | exact superpose eq227151 eq22110
    | exact resolve eq22110 eq227151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227151
  have eq227515 : (M.op x y) = (M.op (M.op x y) x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq227504
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq227504
    | exact resolve eq227504 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227504
  have eq232076 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq22110 x x
       have i₂ := eq206132 X0
       grind)
    | exact superpose eq206132 eq22110
    | (have j1 := eq206132 x
       grind)
    | exact resolve eq22110 eq206132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206132
  have eq232088 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq232076 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq232076
    | (have j0 := eq232076 x
       grind)
    | exact resolve eq232076 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232076
  have eq232176 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    intro X0
    first
    | exact superpose eq206714 eq232088
    | (have j0 := eq232088 x
       grind)
    | exact resolve eq232088 eq206714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206714 eq232088
  have eq249910 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq22110 x x
       have i₂ := eq226907 X0
       grind)
    | exact superpose eq226907 eq22110
    | (have j1 := eq226907 X0
       grind)
    | exact resolve eq22110 eq226907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226907
  have eq249922 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq249910 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq249910
    | (have j0 := eq249910 X0
       grind)
    | exact resolve eq249910 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249910
  have eq250014 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    intro X0
    first
    | exact superpose eq227515 eq249922
    | exact resolve eq249922 eq227515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227515 eq249922
  have eq251652 : (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq232176 eq26
    | (have j1 := eq232176 (σ x)
       grind)
    | exact resolve eq26 eq232176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq252391 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq251652 eq22210
    | exact resolve eq22210 eq251652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq252398 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq251652 eq160465
    | exact resolve eq160465 eq251652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251652
  have eq252645 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq20 eq252398
    | exact resolve eq252398 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252398
  have eq252978 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq252645 eq3491
    | exact resolve eq3491 eq252645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3491
  have eq253039 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq26 eq252978
    | exact resolve eq252978 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252978
  have eq253129 : (σ y) = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq252645 eq253039
    | exact resolve eq253039 eq252645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252645 eq253039
  have eq256357 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq253129 eq22192
    | exact resolve eq22192 eq253129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22192 eq253129
  have eq277449 : (τ (σ y)) = (k y (τ (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq201473 eq227
    | exact resolve eq227 eq201473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227
  have eq277563 : (M.op (M.op x y) x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq201473 eq22114
    | exact resolve eq22114 eq201473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq277572 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq201473 eq277563
    | exact resolve eq277563 eq201473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201473 eq277563
  have eq277647 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y y) := by
    first
    | exact superpose eq31 eq277449
    | exact resolve eq277449 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277449
  have eq284110 : (M.op x y) = (M.op (M.op x y) x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq250014 eq26
    | (have j1 := eq250014 (σ x)
       grind)
    | exact resolve eq26 eq250014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250014
  have eq284870 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq284110 eq22210
    | exact resolve eq22210 eq284110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22210 eq284110
  have eq330567 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq277572 eq22110
    | exact resolve eq22110 eq277572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277572
  have eq330578 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq26 eq330567
    | exact resolve eq330567 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330567
  have eq330933 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y y) := by
    first
    | exact superpose eq277647 eq22110
    | exact resolve eq22110 eq277647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22110 eq277647
  have eq330944 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y y) := by
    first
    | exact superpose eq26 eq330933
    | exact resolve eq330933 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330933
  have eq368063 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq284870 eq330578
    | exact resolve eq330578 eq284870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq368064 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq252391 eq330578
    | exact resolve eq330578 eq252391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252391 eq330578
  have eq368442 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq368064
  have eq368443 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq368063
  have eq370858 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq368442 eq27
    | exact resolve eq27 eq368442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368442
  have eq371377 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq368443 eq2724
    | exact resolve eq2724 eq368443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2724
  have eq371503 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq371377
    | exact resolve eq371377 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371377
  have eq371595 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq368443 eq371503
    | exact resolve eq371503 eq368443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368443 eq371503
  have eq388714 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y y) := by
    first
    | exact superpose eq330944 eq284870
    | exact resolve eq284870 eq330944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284870 eq330944
  have eq388833 : y = (k y y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq388714
  have eq482540 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq914 y
       have i₂ := eq388833
       grind)
    | exact superpose eq388833 eq914
    | (have j0 := eq914 y
       grind)
    | exact resolve eq914 eq388833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq914 eq388833
  have eq482549 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq482540
  have eq482552 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq482549
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq482549
    | exact resolve eq482549 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482549
  have eq482557 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq371595 eq482552
    | exact resolve eq482552 eq371595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371595 eq482552
  have eq482558 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq482557
  have eq482704 : (M.op (M.op x y) x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq482558 eq22114
    | exact resolve eq22114 eq482558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22114
  have eq482714 : (σ y) = (M.op (M.op x y) x) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq482558 eq482704
    | exact resolve eq482704 eq482558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482558 eq482704
  have eq483187 : (σ y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq482714 eq160464
    | exact resolve eq160464 eq482714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160464
  have eq483526 : (σ (M.op x y)) = (σ y) ∨ y = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31 eq483187
    | exact resolve eq483187 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483187
  have eq483863 : (M.op x y) = (τ (σ y)) ∨ y = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq483526 eq28
    | exact resolve eq28 eq483526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq483526
  have eq483976 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq483863
    | exact resolve eq483863 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq483863
  have eq505836 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq483976 eq27
    | exact resolve eq27 eq483976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483976
  have eq506153 : y = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq505836
       have r₂ := eq207374
       grind)
    | exact resolve eq505836 eq207374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207374 eq505836
  have eq506222 : (M.op x y) = (M.op x (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq506153
       grind)
    | exact superpose eq506153 eq18
    | exact resolve eq18 eq506153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq506351 : (M.op x y) ≠ (σ y) ∨ y = (M.op x y) := by grind
  clear eq506153
  have eq506652 : (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq506222 eq232176
    | exact resolve eq232176 eq506222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232176
  have eq506656 : (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq506222 eq256357
    | exact resolve eq256357 eq506222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256357 eq506222
  have eq506768 : (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq506656
  have eq506771 : (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) x) := by grind
  clear eq506652
  have eq506842 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq506768
       have r₂ := eq506351
       grind)
    | exact resolve eq506768 eq506351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506768
  have eq506845 : (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq506771
       have r₂ := eq506351
       grind)
    | exact resolve eq506771 eq506351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506771
  have eq507367 : (M.op x y) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq506845 eq482714
    | exact resolve eq482714 eq506845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482714 eq506845
  have eq507671 : (M.op x y) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq507367
       have r₂ := eq370858
       grind)
    | exact resolve eq507367 eq370858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370858 eq507367
  have eq507851 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq507671
       have r₂ := eq506351
       grind)
    | exact resolve eq507671 eq506351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506351 eq507671
  have eq508078 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq507851 eq27
    | exact resolve eq27 eq507851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq507851
  have eq508396 : y = (M.op x y) := by
    first
    | (have r₁ := eq508078
       have r₂ := eq506842
       grind)
    | exact resolve eq508078 eq506842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506842 eq508078
  have eq508470 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq508396
       grind)
    | exact superpose eq508396 eq18
    | exact resolve eq18 eq508396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq508471 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq508396
       grind)
    | exact superpose eq508396 eq24
    | exact resolve eq24 eq508396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq508396
  have eq509089 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq508470 eq2454
    | exact resolve eq2454 eq508470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2454
  have eq509090 : (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq508470 eq3549
    | exact resolve eq3549 eq508470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3549 eq508470
  have eq509832 : (M.op x y) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq509089 eq650
    | exact resolve eq650 eq509089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650 eq509089
  have eq510514 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq509090 eq160465
    | exact resolve eq160465 eq509090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160465 eq509090
  have eq511044 : (M.op x y) = (σ y) := by
    first
    | exact superpose eq510514 eq508471
    | exact resolve eq508471 eq510514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508471
  have eq511045 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq510514 eq20
    | exact resolve eq20 eq510514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq510514
  have eq511325 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq511044 eq26
    | exact resolve eq26 eq511044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq511044
  have eq511758 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq509832 eq511325
    | exact resolve eq511325 eq509832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509832 eq511325
  have eq511991 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq511758 eq27
    | exact resolve eq27 eq511758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq511758
  have eq512290 : False := by grind
  exact eq512290

/-- `Equation4419`: `x ◇ (x ◇ y) = (z ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_pyx_x_pxy_Equation4419 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4419 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4419.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X1) X0) := by
    intro X0 X1 X2
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
  have eq28 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq44 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq35 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq35
    | (have j0 := eq35 y
       grind)
    | exact resolve eq35 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq35
    | (have j0 := eq35 (M.op x y)
       grind)
    | exact resolve eq35 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq50 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X1)) X2) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op X2 X1) X3
       have i₂ := eq14 X2 X1 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op X2 X1)) = (M.op (M.op X2 X1) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 X1) X0 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X1 X3
       have i₂ := eq14 X2 X1 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X0)) = (M.op (M.op X0 (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X0 (M.op x X1)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op X0 (M.op X0 y)) = (M.op (M.op x y) X0) := by
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
  have eq56 : ∀ X0 : G, (M.op X0 (M.op X0 (σ y))) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op X2 X1) ∨ (M.op X0 (M.op X0 X1)) = (k X0 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op X2 X1)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : x ≠ (M.op x y) ∨ y = (M.op y x) ∨ x = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq36 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq36
    | exact resolve eq36 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq82 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq88 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq81
       grind)
    | exact superpose eq81 eq16
    | exact resolve eq16 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq89 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq91 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq11 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq97 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq97
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq97
    | exact resolve eq97 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq108 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq105
    | exact resolve eq105 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq109 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq108
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq108
    | exact resolve eq108 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq218 : (M.op x (M.op x y)) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq55 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq55
    | (have j0 := eq55 x
       grind)
    | exact resolve eq55 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219 : ∀ X0 X1 : G, (M.op (M.op X0 y) X1) = (M.op (M.op x y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X1
       have i₂ := eq14 X1 y X0
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq223 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 y))) = (M.op (M.op (M.op x y) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 y) X0
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq228 : (M.op x y) ≠ (M.op x (M.op x y)) ∨ (k x (M.op x y)) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq218 eq13
    | exact resolve eq13 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq232 : ∀ X0 X1 : G, (M.op (M.op X0 (σ y)) X1) = (M.op (M.op (σ x) (σ y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq56 X0
       have i₂ := eq14 X0 sF3 x
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq237 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 (σ y))) X0) = (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq305 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (k y (τ X0))
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq16
    | exact resolve eq16 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq372 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) X0) X1) = (M.op (M.op X2 (M.op X0 y)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X0 (M.op X0 y) X1 X2
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq52
    | exact resolve eq52 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq373 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) X1) = (M.op (M.op X2 (M.op X0 (σ y))) X1) := by
    intro X0 X1 X2
    first
    | exact superpose eq56 eq52
    | exact resolve eq52 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq405 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) ≠ (M.op X3 X1) ∨ (M.op (M.op X0 X1) X2) = (k X2 (M.op X3 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X2 (M.op X0 X1)
       have i₂ := eq52 X0 X1 X2 X3
       grind)
    | (have i₁ := eq13 X2 (M.op X3 X1)
       have i₂ := eq52 X0 X1 X2 X3
       grind)
    | exact superpose eq52 eq13
    | (have r₁ := eq13 X2 (M.op (M.op X3 X2) X2)
       have r₂ := eq52 (M.op X3 X2) X2 X2 X3
       grind)
    | (have r₁ := eq13 X2 (M.op (M.op X0 X2) X2)
       have r₂ := eq52 X0 X2 X2 (M.op X0 X2)
       grind)
    | exact resolve eq13 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq458 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 y)) = (M.op (M.op X0 y) (M.op (M.op x y) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq56 (M.op X0 y)
       have i₂ := eq219 X0 sF3
       grind)
    | (have i₁ := eq56 (M.op x y)
       have i₂ := eq219 X0 sF3
       grind)
    | exact superpose eq219 eq56
    | exact resolve eq56 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq459 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 y)) = (M.op (M.op x y) (M.op (M.op x y) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq458 X0
       have i₂ := eq219 X0 (M.op sF0 sF3)
       grind)
    | (have i₁ := eq458 x
       have i₂ := eq219 X0 (M.op sF0 sF3)
       grind)
    | exact superpose eq219 eq458
    | exact resolve eq458 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458
  have eq468 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 y)) = (M.op (M.op (σ x) (σ y)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq56 eq459
    | exact resolve eq459 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459
  have eq502 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (σ y))) = (M.op (M.op X0 (σ y)) (M.op (M.op (σ x) (σ y)) y)) := by
    intro X0
    first
    | exact superpose eq232 eq55
    | exact resolve eq55 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq503 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) = (M.op (M.op X0 (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq232 eq56
    | exact resolve eq56 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq504 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq232 eq503
    | exact resolve eq503 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503
  have eq505 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) y)) := by
    intro X0
    first
    | exact superpose eq232 eq502
    | exact resolve eq502 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502
  have eq513 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq56 eq504
    | exact resolve eq504 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq504
  have eq514 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (σ y))) = (M.op (M.op x y) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq505 X0
       have i₂ := eq55 sF4
       grind)
    | exact superpose eq55 eq505
    | exact resolve eq505 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505
  have eq559 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X2)) X3) = (M.op X3 (M.op X3 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq54 X1 X2 X3
       have i₂ := eq52 X1 (M.op X1 X2) X3 X0
       grind)
    | (have i₁ := eq54 X1 X2 X3
       have i₂ := eq52 X0 (M.op X1 X2) X3 X1
       grind)
    | exact superpose eq52 eq54
    | exact resolve eq54 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq622 : (k y (k y x)) = (τ (k (σ y) (k (σ y) (σ x)))) := by
    first
    | exact superpose eq88 eq305
    | exact resolve eq305 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305
  have eq662 : (M.op (M.op (σ x) (σ y)) (M.op x y)) = (M.op (M.op x y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq468 sF4
       have i₂ := eq55 sF4
       grind)
    | exact superpose eq55 eq468
    | exact resolve eq468 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq692 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 y) X0)) = (M.op (M.op (M.op x y) X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq50 X1 y X0 X0
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq50
    | exact resolve eq50 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq693 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 (σ y)) X0)) = (M.op (M.op (M.op (σ x) (σ y)) X0) X0) := by
    intro X0 X1
    first
    | exact superpose eq56 eq50
    | exact resolve eq50 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq785 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (M.op (σ x) (σ y)) X0) X0) := by
    intro X0
    first
    | exact superpose eq232 eq693
    | (have j0 := eq693 X0 (σ x)
       grind)
    | exact resolve eq693 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693
  have eq786 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) X0)) = (M.op (M.op (M.op x y) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq692 X0 x
       have i₂ := eq219 x X0
       grind)
    | (have i₁ := eq692 x x
       have i₂ := eq219 X0 x
       grind)
    | exact superpose eq219 eq692
    | (have j0 := eq692 X0 x
       grind)
    | exact resolve eq692 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692
  have eq1081 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (σ y)) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op X1 X0) (M.op X2 (σ y))) := by
    intro X0 X1 X2
    first
    | exact superpose eq56 eq51
    | exact resolve eq51 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1115 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) y) (M.op X1 (M.op X1 y))) := by
    intro X0 X1
    first
    | (have i₁ := eq55 (M.op X0 X1)
       have i₂ := eq51 X1 y (M.op X0 X1) X0
       grind)
    | exact superpose eq51 eq55
    | exact resolve eq55 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1116 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) (σ y)) (M.op X1 (M.op X1 (σ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq56 (M.op x X0)
       have i₂ := eq51 X0 sF3 (M.op x X0) x
       grind)
    | exact superpose eq51 eq56
    | exact resolve eq56 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq1166 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op X1 (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq232 eq1116
    | exact resolve eq1116 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1116
  have eq1167 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 X1)) = (M.op (M.op x y) (M.op X1 (M.op X1 y))) := by
    intro X0 X1
    first
    | (have i₁ := eq1115 X0 X1
       have i₂ := eq219 (M.op X0 X1) (M.op X1 (M.op X1 y))
       grind)
    | exact superpose eq219 eq1115
    | exact resolve eq1115 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1115
  have eq1177 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op X1 X0) (M.op X2 (σ y))) := by
    intro X0 X1 X2
    first
    | exact superpose eq232 eq1081
    | exact resolve eq1081 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1081
  have eq1190 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq56 eq1166
    | exact resolve eq1166 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1166
  have eq1191 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 X1)) = (M.op (M.op x y) (M.op (M.op x y) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1167 X0 X1
       have i₂ := eq55 X1
       grind)
    | exact superpose eq55 eq1167
    | exact resolve eq1167 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1167
  have eq1344 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) ≠ (M.op X1 (σ y)) ∨ (M.op (M.op (σ x) (σ y)) X0) = (k X0 (M.op X1 (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq56 eq67
    | (have r₁ := eq67 (σ y) (σ y) (M.op (σ x) (σ y))
       have r₂ := eq56 (σ y)
       grind)
    | exact resolve eq67 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq67
  have eq1864 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq89 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq2282 : (M.op (M.op x y) y) = (M.op y (M.op (M.op (σ x) (σ y)) y)) := by
    first
    | (have i₁ := eq785 y
       have i₂ := eq219 sF4 y
       grind)
    | exact superpose eq219 eq785
    | exact resolve eq785 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2283 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq232 eq785
    | exact resolve eq785 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq785
  have eq2350 : (M.op (M.op x y) y) = (M.op y (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq786 y
       have i₂ := eq219 sF0 y
       grind)
    | exact superpose eq219 eq786
    | exact resolve eq786 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2351 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (M.op (M.op x y) (σ y))) := by
    first
    | exact superpose eq232 eq786
    | exact resolve eq786 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq786
  have eq2409 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 y) (M.op (σ x) (σ y)))) = (M.op (M.op (M.op x y) y) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq2282 eq50
    | exact resolve eq50 eq2282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2282
  have eq2437 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) y)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 y) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq2409 X0
       have i₂ := eq14 sF4 y sF0
       grind)
    | exact superpose eq14 eq2409
    | exact resolve eq2409 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2409
  have eq2441 : (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) y)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) y))) := by
    first
    | (have i₁ := eq2437 x
       have i₂ := eq14 sF4 y x
       grind)
    | exact superpose eq14 eq2437
    | exact resolve eq2437 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2437
  have eq2442 : (M.op (M.op x y) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op x y) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq2441
       have i₂ := eq55 sF4
       grind)
    | exact superpose eq55 eq2441
    | exact resolve eq2441 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2441
  have eq2482 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op X0 y) (M.op x y))) = (M.op (M.op (M.op x y) y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq2350 eq50
    | exact resolve eq50 eq2350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2511 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op x y) y)) = (M.op (M.op x y) (M.op (M.op X0 y) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq2482 X0
       have i₂ := eq14 sF0 y sF0
       grind)
    | exact superpose eq14 eq2482
    | exact resolve eq2482 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2482
  have eq2517 : (M.op (M.op x y) (M.op (M.op x y) y)) = (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op x y) y))) := by
    first
    | (have i₁ := eq2511 x
       have i₂ := eq14 sF0 y x
       grind)
    | exact superpose eq14 eq2511
    | exact resolve eq2511 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2511
  have eq2518 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq2517
       have i₂ := eq55 sF0
       grind)
    | exact superpose eq55 eq2517
    | exact resolve eq2517 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2517
  have eq2520 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op X0 (σ y)) (M.op x y))) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq2351 eq50
    | exact resolve eq50 eq2351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2351
  have eq2550 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op x y) (σ y))) = (M.op (M.op x y) (M.op (M.op X0 (σ y)) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq2520 X0
       have i₂ := eq14 sF0 sF3 sF4
       grind)
    | exact superpose eq14 eq2520
    | exact resolve eq2520 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2520
  have eq2557 : (M.op (M.op x y) (M.op (M.op x y) (σ y))) = (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op x y) (σ y)))) := by
    first
    | (have i₁ := eq2550 x
       have i₂ := eq14 sF0 sF3 x
       grind)
    | exact superpose eq14 eq2550
    | exact resolve eq2550 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2550
  have eq2558 : (M.op (M.op x y) (M.op (σ x) (σ y))) = (M.op (M.op x y) (M.op (M.op x y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq514 eq2557
    | exact resolve eq2557 eq514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514 eq2557
  have eq2591 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op X0 y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq1190 X0 (M.op X0 y)
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq1190
    | exact resolve eq1190 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq2694 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq468 eq2591
    | exact resolve eq2591 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468 eq2591
  have eq2705 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op x y) (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq662 eq2694
    | exact resolve eq2694 eq662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2694
  have eq2706 : ∀ X0 : G, (M.op (M.op x y) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq2442 eq2705
    | exact resolve eq2705 eq2442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2705
  have eq2714 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op x y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq513 eq2706
    | exact resolve eq2706 eq513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513 eq2706
  have eq2964 : ∀ X0 : G, (M.op (M.op (M.op x y) (M.op (σ x) (σ y))) (M.op x y)) = (M.op (M.op x y) (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq2558 eq50
    | exact resolve eq50 eq2558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2986 : (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) = (M.op (M.op (M.op x y) (M.op (σ x) (σ y))) (M.op x y)) := by
    first
    | exact superpose eq1191 eq2964
    | exact resolve eq2964 eq1191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2964
  have eq2991 : (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) = (M.op (M.op x y) (M.op (M.op x y) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq2986
       have i₂ := eq14 sF0 sF4 sF0
       grind)
    | exact superpose eq14 eq2986
    | exact resolve eq2986 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2986
  have eq2993 : (M.op (M.op x y) (M.op (σ x) (σ y))) = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq2558 eq2991
    | exact resolve eq2991 eq2558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2558 eq2991
  have eq2995 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2518 eq2993
    | exact resolve eq2993 eq2518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2993
  have eq3113 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op x y) (M.op X0 y))) = (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1191 eq223
    | exact resolve eq223 eq1191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3117 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op X0 y))) = (M.op (M.op (M.op x y) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq1190 eq223
    | exact resolve eq223 eq1190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3218 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op X0 y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq3117 X0
       have i₂ := eq14 sF4 sF4 sF0
       grind)
    | exact superpose eq14 eq3117
    | exact resolve eq3117 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3117
  have eq3222 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op x y) (M.op X0 y))) = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq3113 X0
       have i₂ := eq14 sF0 sF0 sF0
       grind)
    | exact superpose eq14 eq3113
    | exact resolve eq3113 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3113
  have eq3275 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op X0 y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op x y) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq2714 eq3218
    | exact resolve eq3218 eq2714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2714 eq3218
  have eq3279 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op (M.op x y) (M.op X0 y))) := by
    intro X0
    first
    | exact superpose eq2518 eq3222
    | exact resolve eq3222 eq2518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2518 eq3222
  have eq3312 : ∀ X0 : G, (M.op (M.op x y) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op X0 y))) := by
    intro X0
    first
    | exact superpose eq2442 eq3275
    | exact resolve eq3275 eq2442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2442 eq3275
  have eq3316 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op x y) X0) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq3279 X0
       have i₂ := eq223 X0 sF0
       grind)
    | exact superpose eq223 eq3279
    | exact resolve eq3279 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3279
  have eq3331 : ∀ X0 : G, (M.op (M.op x y) (M.op (σ x) (σ y))) = (M.op (M.op (M.op x y) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq3312 X0
       have i₂ := eq223 X0 sF4
       grind)
    | exact superpose eq223 eq3312
    | exact resolve eq3312 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223 eq3312
  have eq3334 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq3316 x
       have i₂ := eq14 sF0 x sF0
       grind)
    | exact superpose eq14 eq3316
    | exact resolve eq3316 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3316
  have eq3343 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op x y) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq3331 x
       have i₂ := eq14 sF4 x sF0
       grind)
    | exact superpose eq14 eq3331
    | exact resolve eq3331 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3331
  have eq3349 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq2995 eq3343
    | exact resolve eq3343 eq2995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3343
  have eq3369 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op X0 X1)) := by
    intro X0 X1
    first
    | exact superpose eq1191 eq3334
    | exact resolve eq3334 eq1191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3334
  have eq3438 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | exact superpose eq1190 eq3349
    | exact resolve eq3349 eq1190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1190 eq3349
  have eq4575 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op x y) (M.op X2 X1)) X3) = (M.op (M.op (M.op X0 (M.op y X1)) y) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq372 (M.op X2 X1) X3 y
       have i₂ := eq50 X2 X1 y X0
       grind)
    | exact superpose eq50 eq372
    | exact resolve eq372 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4772 : ∀ X1 X2 X3 : G, (M.op (M.op x y) X3) = (M.op (M.op (M.op x y) (M.op X2 X1)) X3) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq4575 x X1 X2 X3
       have i₂ := eq219 (M.op x (M.op y X1)) X3
       grind)
    | exact superpose eq219 eq4575
    | exact resolve eq4575 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4575
  have eq4836 : ∀ X3 : G, (M.op (M.op x y) X3) = (M.op (M.op (M.op x y) (M.op x y)) X3) := by
    intro X3
    first
    | exact superpose eq3369 eq4772
    | (have j0 := eq4772 y x X3
       grind)
    | exact resolve eq4772 eq3369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4772
  have eq4881 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (M.op (M.op X0 (M.op x y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4836 x
       have i₂ := eq52 sF0 sF0 x x
       grind)
    | (have i₁ := eq4836 x
       have i₂ := eq52 X0 sF0 x sF0
       grind)
    | exact superpose eq52 eq4836
    | exact resolve eq4836 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5229 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 y)) X1) = (M.op (M.op X2 (M.op (M.op x y) (σ y))) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq373 (M.op X0 y) X1 X2
       have i₂ := eq219 X0 sF3
       grind)
    | (have i₁ := eq373 (M.op x y) X1 X2
       have i₂ := eq219 X0 sF3
       grind)
    | exact superpose eq219 eq373
    | exact resolve eq373 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq5245 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op X2 X1)) X3) = (M.op (M.op (M.op X0 (M.op (σ y) X1)) (σ y)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq373 (M.op X0 X1) X1 sF3
       have i₂ := eq50 X0 X1 sF3 X3
       grind)
    | exact superpose eq50 eq373
    | exact resolve eq373 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq5455 : ∀ X1 X2 X3 : G, (M.op (M.op (σ x) (σ y)) X3) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X2 X1)) X3) := by
    intro X1 X2 X3
    first
    | exact superpose eq232 eq5245
    | exact resolve eq5245 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232 eq5245
  have eq5469 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 y)) X1) = (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq373 eq5229
    | exact resolve eq5229 eq373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373 eq5229
  have eq5527 : ∀ X3 : G, (M.op (M.op (σ x) (σ y)) X3) = (M.op (M.op (M.op x y) (M.op x y)) X3) := by
    intro X3
    first
    | exact superpose eq3438 eq5455
    | exact resolve eq5455 eq3438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5455
  have eq5539 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 y)) X1) = (M.op (M.op (M.op x y) (M.op (σ x) (σ y))) X1) := by
    intro X0 X1
    first
    | exact superpose eq662 eq5469
    | exact resolve eq5469 eq662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662 eq5469
  have eq5580 : ∀ X3 : G, (M.op (M.op x y) X3) = (M.op (M.op (σ x) (σ y)) X3) := by
    intro X3
    first
    | exact superpose eq4836 eq5527
    | exact resolve eq5527 eq4836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5527
  have eq5588 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 y)) X1) = (M.op (M.op (M.op x y) (M.op x y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq2995 eq5539
    | exact resolve eq5539 eq2995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5539
  have eq5615 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq4836 eq5588
    | exact resolve eq5588 eq4836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4836 eq5588
  have eq5627 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (M.op (M.op (M.op x y) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5615 X0 X1
       have i₂ := eq372 X0 X1 sF4
       grind)
    | exact superpose eq372 eq5615
    | exact resolve eq5615 eq372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372 eq5615
  have eq6943 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op x y) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5627 X1 X2
       have i₂ := eq52 sF0 X1 X2 x
       grind)
    | (have i₁ := eq5627 X1 X2
       have i₂ := eq52 X0 X1 X2 sF0
       grind)
    | exact superpose eq52 eq5627
    | exact resolve eq5627 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq7583 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X1)) = (M.op (M.op (M.op x y) (M.op (M.op x y) X0)) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq1191 eq559
    | exact resolve eq559 eq1191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559 eq1191
  have eq7923 : ∀ X1 X2 : G, (M.op X2 (M.op X2 X1)) = (M.op (M.op x y) X2) := by
    intro X1 X2
    first
    | exact superpose eq5627 eq7583
    | exact resolve eq7583 eq5627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5627 eq7583
  have eq10421 : ∀ X0 X1 X2 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op X1 X0) (M.op X2 (σ y))) := by
    intro X0 X1 X2
    first
    | exact superpose eq3438 eq1177
    | exact resolve eq1177 eq3438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1177
  have eq10604 : ∀ X2 : G, (M.op (M.op (M.op x y) (M.op x y)) X2) = (M.op X2 (M.op (M.op (σ x) (σ y)) X2)) := by
    intro X2
    first
    | exact superpose eq10421 eq237
    | exact resolve eq237 eq10421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237 eq10421
  have eq10676 : ∀ X2 : G, (M.op (M.op (M.op x y) (M.op x y)) X2) = (M.op X2 (M.op (M.op x y) X2)) := by
    intro X2
    first
    | exact superpose eq5580 eq10604
    | exact resolve eq10604 eq5580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10604
  have eq10754 : ∀ X2 : G, (M.op (M.op x y) X2) = (M.op X2 (M.op (M.op x y) X2)) := by
    intro X2
    first
    | exact superpose eq4881 eq10676
    | exact resolve eq10676 eq4881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4881 eq10676
  have eq13393 : ∀ X0 X1 : G, (M.op (M.op x y) X0) ≠ (M.op X1 (σ y)) ∨ (M.op (M.op (σ x) (σ y)) X0) = (k X0 (M.op X1 (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq5580 eq1344
    | (have j0 := eq1344 X0 X1
       grind)
    | (have r₁ := eq1344 (σ y) (M.op x y)
       have r₂ := eq5580 (σ y)
       grind)
    | exact resolve eq1344 eq5580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1344
  have eq13394 : ∀ X0 X1 : G, (M.op (M.op x y) X0) ≠ (M.op X1 (σ y)) ∨ (M.op (M.op x y) X0) = (k X0 (M.op X1 (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq5580 eq13393
    | (have j0 := eq13393 X0 X1
       grind)
    | (have r₁ := eq13393 (σ y) (M.op (σ x) (σ y))
       have r₂ := eq5580 (σ y)
       grind)
    | exact resolve eq13393 eq5580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5580 eq13393
  have eq13513 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (M.op x y) X0) ∨ (M.op (M.op x y) X0) = (k X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq13394
    | (have j0 := eq13394 X0 (σ x)
       grind)
    | exact resolve eq13394 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13394
  have eq14426 : ∀ X0 X1 X2 X3 : G, (M.op X3 X1) ≠ (M.op (M.op x y) X2) ∨ (M.op (M.op X0 X1) X2) = (k X2 (M.op X3 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq405 X0 X1 X2 X3
       have i₂ := eq6943 X0 X1 X2
       grind)
    | (have i₁ := eq405 x y X2 X3
       have i₂ := eq6943 X0 X1 X2
       grind)
    | exact superpose eq6943 eq405
    | (have j0 := eq405 X0 X1 X2 X3
       grind)
    | (have r₁ := eq405 X0 X2 X2 (M.op x y)
       have r₂ := eq6943 X0 X2 X2
       grind)
    | (have r₁ := eq405 x y y (M.op X0 X1)
       have r₂ := eq6943 X0 X1 y
       grind)
    | exact resolve eq405 eq6943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405
  have eq14427 : ∀ X1 X2 X3 : G, (M.op X3 X1) ≠ (M.op (M.op x y) X2) ∨ (k X2 (M.op X3 X1)) = (M.op (M.op x y) X2) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq14426 x X1 X2 X3
       have i₂ := eq6943 x X1 X2
       grind)
    | (have i₁ := eq14426 x y X2 X3
       have i₂ := eq6943 x X1 X2
       grind)
    | exact superpose eq6943 eq14426
    | (have j0 := eq14426 x X1 X2 X3
       grind)
    | (have r₁ := eq14426 x X2 X2 (M.op x X1)
       have r₂ := eq6943 x X1 X2
       grind)
    | (have r₁ := eq14426 x X2 X2 (M.op x y)
       have r₂ := eq6943 x y X2
       grind)
    | exact resolve eq14426 eq6943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14426
  have eq14534 : ∀ X0 : G, (M.op (M.op x y) X0) = (k X0 (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have j0 := eq14427 X0 X0 (M.op x y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14427
  have eq14571 : (M.op x (M.op x y)) = (k x (M.op x (M.op x y))) := by
    first
    | exact superpose eq218 eq14534
    | exact resolve eq14534 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14534
  have eq16819 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq91 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq91
    | (have j0 := eq91 y
       grind)
    | exact resolve eq91 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq16852 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq16819
  have eq16873 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16852
       have i₂ := eq82
       grind)
    | exact superpose eq82 eq16852
    | exact resolve eq16852 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16852
  have eq16900 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq16873
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq16873 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16873
  have eq21034 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq109 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21035 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq21034
    | exact resolve eq21034 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21034
  have eq21046 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq21035
       have r₂ := eq27
       grind)
    | exact resolve eq21035 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21035
  have eq21048 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq21046
    | exact resolve eq21046 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21046
  have eq21051 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq21048 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq21048
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq21048
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq21048
       grind)
    | exact resolve eq12 eq21048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21048
  have eq21079 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq21051
  have eq21091 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq21079
    | exact resolve eq21079 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21079
  have eq21092 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq21091
  have eq21632 : (τ (σ y)) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq21092 eq88
    | exact resolve eq88 eq21092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21092
  have eq21648 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq21632
    | exact resolve eq21632 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq21632
  have eq22687 : y = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq21648
       grind)
    | exact superpose eq21648 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq21648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21648
  have eq22688 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq22687
  have eq22691 : x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq22688
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq22688
    | exact resolve eq22688 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22688
  have eq22692 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq22691
  have eq22882 : y ≠ y ∨ x = (M.op x y) ∨ y = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq22692
       grind)
    | exact superpose eq22692 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq22692
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq22692
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq22692
       grind)
    | exact resolve eq12 eq22692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22902 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op y X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq6943 y x X0
       have i₂ := eq22692
       grind)
    | exact superpose eq22692 eq6943
    | exact resolve eq6943 eq22692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22908 : x = (M.op x y) ∨ y = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq22882
  have eq22919 : x = (M.op x y) ∨ y = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq22908
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq22908
    | exact resolve eq22908 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22908
  have eq22920 : y = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq22919
  have eq22964 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1864 y x
       have i₂ := eq22920
       grind)
    | exact superpose eq22920 eq1864
    | (have j0 := eq1864 y x
       grind)
    | exact resolve eq1864 eq22920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22920
  have eq22967 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq22964
  have eq22969 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq22967
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq22967
    | exact resolve eq22967 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22967
  have eq22977 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq22969
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq22969
    | exact resolve eq22969 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22969
  have eq22980 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq22977
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq22977
    | exact resolve eq22977 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22977
  have eq22981 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq22980
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq22980
    | exact resolve eq22980 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22980
  have eq22982 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq22981
    | exact resolve eq22981 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22981
  have eq22983 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq22982
  have eq23068 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ y) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq22983 eq6943
    | exact resolve eq6943 eq22983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23273 : (M.op y x) = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq218 eq22902
    | exact resolve eq22902 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22902
  have eq23528 : y = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq22692
       have i₂ := eq23273
       grind)
    | exact superpose eq23273 eq22692
    | exact resolve eq22692 eq23273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22692 eq23273
  have eq23560 : y = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq23528
  have eq23587 : y ≠ (M.op x y) ∨ y = (k x (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23560 eq228
    | exact resolve eq228 eq23560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq23619 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23560 eq7923
    | exact resolve eq7923 eq23560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23623 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq218 eq23619
    | exact resolve eq23619 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218 eq23619
  have eq23645 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq23623
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq23623
    | exact resolve eq23623 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23623
  have eq23664 : (M.op x y) = (k x (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23645 eq14571
    | exact resolve eq14571 eq23645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14571
  have eq23666 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23645 eq23560
    | exact resolve eq23560 eq23645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23560 eq23645
  have eq23692 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq23666
  have eq23748 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23664 eq45
    | exact resolve eq45 eq23664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23664
  have eq23764 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq23748
    | exact resolve eq23748 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23748
  have eq24393 : (σ y) = (M.op (M.op x y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23068 eq22983
    | exact resolve eq22983 eq23068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22983 eq23068
  have eq24490 : (σ y) = (M.op (M.op x y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq24393
  have eq24641 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24490 eq10754
    | exact resolve eq10754 eq24490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10754 eq24490
  have eq24705 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq24641
    | exact resolve eq24641 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24641
  have eq24720 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24705 eq27
    | exact resolve eq27 eq24705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24705
  have eq27484 : y = (k x (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq23587
       have r₂ := eq23692
       grind)
    | exact resolve eq23587 eq23692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23587 eq23692
  have eq27487 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27484 eq45
    | exact resolve eq45 eq27484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq27484
  have eq27506 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq27487
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq27487
    | exact resolve eq27487 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27487
  have eq27525 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27506 eq23764
    | exact resolve eq23764 eq27506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23764 eq27506
  have eq27528 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq27525
  have eq27530 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq27528
       have r₂ := eq24720
       grind)
    | exact resolve eq27528 eq24720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24720 eq27528
  have eq27542 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27530 eq27
    | exact resolve eq27 eq27530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27543 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27530 eq69
    | (have r₁ := eq69
       have r₂ := eq27530
       grind)
    | exact resolve eq69 eq27530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq27544 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27530 eq74
    | (have r₁ := eq74
       have r₂ := eq27530
       grind)
    | exact resolve eq74 eq27530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq27552 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27530 eq2283
    | exact resolve eq2283 eq27530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2283
  have eq27557 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27530 eq2995
    | exact resolve eq2995 eq27530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2995
  have eq27562 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (σ x) (M.op X0 X1)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq27530 eq3438
    | exact resolve eq3438 eq27530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3438
  have eq27575 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq27544
  have eq27576 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq27543
  have eq27581 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq27552
    | exact resolve eq27552 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27552
  have eq27594 : (k y (k y x)) = (τ (k (σ y) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27576 eq622
    | exact resolve eq622 eq27576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622 eq27576
  have eq27618 : (k y x) = (k y (k y x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq88 eq27594
    | exact resolve eq27594 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq27594
  have eq27624 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27530 eq27581
    | exact resolve eq27581 eq27530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27676 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq27624
  have eq27770 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27676 eq13
    | (have r₁ := eq13 y x
       have r₂ := eq27676
       grind)
    | exact resolve eq13 eq27676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27792 : (M.op (σ y) (σ x)) = (M.op (M.op x y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27676 eq7923
    | exact resolve eq7923 eq27676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7923
  have eq28533 : (σ x) = (M.op (M.op x y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27792 eq27676
    | exact resolve eq27676 eq27792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27792
  have eq28566 : (σ x) = (M.op (M.op x y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq28533
  have eq31399 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27575 eq27676
    | exact resolve eq27676 eq27575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27575
  have eq31442 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
  clear eq31399
  have eq31469 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq31442
       have r₂ := eq27770
       grind)
    | exact resolve eq31442 eq27770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27770 eq31442
  have eq31490 : (τ (σ x)) = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31469 eq60
    | exact resolve eq60 eq31469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq31491 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31469 eq109
    | exact resolve eq109 eq31469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq31512 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq31491
  have eq31527 : y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq31512
       have r₂ := eq27542
       grind)
    | exact resolve eq31512 eq27542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27542 eq31512
  have eq31528 : x = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq31490
    | exact resolve eq31490 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31490
  have eq31536 : y ≠ y ∨ x = (M.op x y) ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq31527
       grind)
    | exact superpose eq31527 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq31527
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq31527
       grind)
    | exact resolve eq12 eq31527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31537 : y ≠ y ∨ y = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq31527
       grind)
    | exact superpose eq31527 eq13
    | (have r₁ := eq13 x y
       have r₂ := eq31527
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq31527
       grind)
    | exact resolve eq13 eq31527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31554 : (M.op (M.op x y) y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3369 y x
       have i₂ := eq31527
       grind)
    | exact superpose eq31527 eq3369
    | exact resolve eq3369 eq31527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3369
  have eq31556 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op y X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq6943 y x X0
       have i₂ := eq31527
       grind)
    | exact superpose eq31527 eq6943
    | exact resolve eq6943 eq31527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6943 eq31527
  have eq31565 : y = (k x y) ∨ x = (M.op x y) := by grind
  clear eq31537
  have eq31566 : x = (M.op x y) ∨ y = (k y x) ∨ x = (M.op x y) := by grind
  clear eq31536
  have eq31579 : x = (M.op x y) ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq31566
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq31566
    | exact resolve eq31566 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31566
  have eq31580 : y = (k y x) ∨ x = (M.op x y) := by grind
  clear eq31579
  have eq31636 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq31565
       grind)
    | exact superpose eq31565 eq44
    | exact resolve eq44 eq31565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31644 : x = y ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq31528
       have i₂ := eq31565
       grind)
    | exact superpose eq31565 eq31528
    | exact resolve eq31528 eq31565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31528 eq31565
  have eq31647 : x = (M.op x y) ∨ x = y := by grind
  clear eq31644
  have eq31658 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq31636
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq31636
    | exact resolve eq31636 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31636
  have eq32115 : y = (k y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq27618
       have i₂ := eq31580
       grind)
    | exact superpose eq31580 eq27618
    | exact resolve eq27618 eq31580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27618 eq31580
  have eq32124 : y = (k y y) ∨ x = (M.op x y) := by grind
  clear eq32115
  have eq32163 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31658 eq31469
    | exact resolve eq31469 eq31658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31469 eq31658
  have eq32166 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq32163
  have eq32300 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32166 eq27676
    | exact resolve eq27676 eq32166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27676
  have eq32311 : (σ x) = (M.op (M.op x y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32166 eq28566
    | exact resolve eq28566 eq32166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28566
  have eq32320 : (σ x) = (M.op (M.op x y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq32311
  have eq32332 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq32300
  have eq32482 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1864 y y
       have i₂ := eq32124
       grind)
    | exact superpose eq32124 eq1864
    | (have j0 := eq1864 y y
       grind)
    | exact resolve eq1864 eq32124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32483 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq32124
       grind)
    | exact superpose eq32124 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq32124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32124
  have eq32484 : y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq32483
  have eq32485 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq32482
  have eq32486 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq32485
  have eq32490 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq32486
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq32486
    | exact resolve eq32486 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32486
  have eq32891 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32490 eq27562
    | exact resolve eq27562 eq32490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27562 eq32490
  have eq32895 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq32891
  have eq32904 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq32895
    | exact resolve eq32895 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32895
  have eq34130 : (σ x) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32320 eq27557
    | exact resolve eq27557 eq32320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27557 eq32320
  have eq34206 : (σ x) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq34130
  have eq36642 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31554 eq32904
    | exact resolve eq32904 eq31554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32904
  have eq36643 : (σ x) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31554 eq34206
    | exact resolve eq34206 eq31554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31554 eq34206
  have eq36713 : (σ x) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by grind
  clear eq36643
  have eq36714 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by grind
  clear eq36642
  have eq36935 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k y (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq36713 eq13513
    | exact resolve eq13513 eq36713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13513 eq36713
  have eq37030 : (σ x) = (k y (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq36935
       have r₂ := eq27530
       grind)
    | exact resolve eq36935 eq27530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27530 eq36935
  have eq37363 : (M.op (σ x) (σ y)) = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31556 eq36714
    | exact resolve eq36714 eq31556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31556 eq36714
  have eq37525 : (M.op (σ x) (σ y)) = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq37363
  have eq38017 : y = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq32484
       have i₂ := eq37525
       grind)
    | exact superpose eq37525 eq32484
    | exact resolve eq32484 eq37525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32484 eq37525
  have eq38062 : y = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq38017
  have eq38140 : y = (M.op (σ y) y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38062 eq27581
    | exact resolve eq27581 eq38062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27581
  have eq38158 : (σ x) = (k y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38062 eq37030
    | exact resolve eq37030 eq38062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37030 eq38062
  have eq38159 : (σ x) = (k y y) ∨ x = (M.op x y) := by grind
  clear eq38158
  have eq38177 : y = (M.op (σ y) y) ∨ x = (M.op x y) := by grind
  clear eq38140
  have eq38557 : (k (σ y) (σ y)) = (σ (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq82
       have i₂ := eq38159
       grind)
    | exact superpose eq38159 eq82
    | exact resolve eq82 eq38159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq38159
  have eq38588 : (M.op (σ y) (σ y)) = (σ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16900 eq38557
    | exact resolve eq38557 eq16900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16900 eq38557
  have eq38757 : y = (M.op (σ x) y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32166 eq38177
    | exact resolve eq38177 eq32166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38177
  have eq38813 : y = (M.op (σ x) y) ∨ x = (M.op x y) := by grind
  clear eq38757
  have eq41340 : (M.op (σ x) (σ x)) = (σ (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32166 eq38588
    | exact resolve eq38588 eq32166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32166 eq38588
  have eq41411 : (M.op (σ x) (σ x)) = (σ (σ x)) ∨ x = (M.op x y) := by grind
  clear eq41340
  have eq41572 : (σ x) = (σ (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq41411 eq32332
    | exact resolve eq32332 eq41411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32332 eq41411
  have eq41615 : (σ x) = (σ (σ x)) ∨ x = (M.op x y) := by grind
  clear eq41572
  have eq41672 : (σ x) = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq41615 eq16
    | exact resolve eq16 eq41615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41615
  have eq41713 : x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq41672
    | exact resolve eq41672 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq41672
  have eq41875 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq41713 eq38813
    | exact resolve eq38813 eq41713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38813 eq41713
  have eq41888 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq41875
  have eq41975 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq41888
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq41888
    | exact resolve eq41888 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41888
  have eq42275 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq41975
  have eq42278 : x = (M.op x y) := by
    first
    | (have r₁ := eq42275
       have r₂ := eq31647
       grind)
    | exact resolve eq42275 eq31647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31647 eq42275
  have eq42404 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq42278 eq20
    | exact resolve eq20 eq42278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq42408 : x ≠ x ∨ y = (M.op y x) ∨ x = (k x y) := by
    first
    | exact superpose eq42278 eq73
    | (have r₁ := eq73
       have r₂ := eq42278
       grind)
    | exact resolve eq73 eq42278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq42471 : (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq42278 eq2350
    | exact resolve eq2350 eq42278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2350
  have eq42526 : y = (M.op y x) ∨ x = (k x y) := by grind
  clear eq42408
  have eq42545 : (M.op x y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq42471
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq42471
    | exact resolve eq42471 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq42471
  have eq42600 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq42404
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq42404
    | exact resolve eq42404 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42404
  have eq42611 : x = (M.op y x) := by
    first
    | exact superpose eq42278 eq42545
    | exact resolve eq42545 eq42278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42278 eq42545
  have eq42658 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq42600 eq26
    | exact resolve eq26 eq42600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42994 : x ≠ y ∨ x = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq42611
       grind)
    | exact superpose eq42611 eq13
    | exact resolve eq13 eq42611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71709 : x = y ∨ x = (k x y) := by
    first
    | (have i₁ := eq42526
       have i₂ := eq42611
       grind)
    | exact superpose eq42611 eq42526
    | exact resolve eq42526 eq42611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42526 eq42611
  have eq71710 : x = (k x y) := by
    first
    | (have r₁ := eq71709
       have r₂ := eq42994
       grind)
    | exact resolve eq71709 eq42994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42994 eq71709
  have eq71718 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq71710
       grind)
    | exact superpose eq71710 eq44
    | exact resolve eq44 eq71710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq71735 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq1864 x y
       have i₂ := eq71710
       grind)
    | exact superpose eq71710 eq1864
    | (have j0 := eq1864 x y
       grind)
    | exact resolve eq1864 eq71710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1864 eq71710
  have eq71744 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq71735
  have eq71755 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq71744
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq71744
    | exact resolve eq71744 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71744
  have eq71766 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq42600 eq71718
    | exact resolve eq71718 eq42600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71718
  have eq71776 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq71755
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq71755
    | exact resolve eq71755 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71755
  have eq71786 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq71766
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq71766
    | exact resolve eq71766 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71766
  have eq71795 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq71776
    | exact resolve eq71776 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq71776
  have eq71805 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq42600 eq71786
    | exact resolve eq71786 eq42600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71786
  have eq71814 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq42600 eq71795
    | exact resolve eq71795 eq42600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71795
  have eq71829 : (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq71814
       have r₂ := eq27
       grind)
    | exact resolve eq71814 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71814
  have eq71841 : (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq71829
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq71829
    | exact resolve eq71829 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq71829
  have eq71853 : (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq42600 eq71841
    | exact resolve eq71841 eq42600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42600 eq71841
  have eq71865 : (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq71853
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq71853
    | exact resolve eq71853 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq71853
  have eq71979 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq71865 eq13
    | (have r₁ := eq13 (σ (M.op x y)) (σ y)
       have r₂ := eq71865
       grind)
    | exact resolve eq13 eq71865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72020 : (σ y) = (k (σ (M.op x y)) (σ y)) := by grind
  clear eq71979
  have eq72044 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq71805 eq72020
    | exact resolve eq72020 eq71805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71805 eq72020
  have eq72314 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq72044 eq42658
    | exact resolve eq42658 eq72044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42658
  have eq72319 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq72044 eq71865
    | exact resolve eq71865 eq72044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71865 eq72044
  have eq73117 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq72314 eq72319
    | exact resolve eq72319 eq72314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72314 eq72319
  have eq73118 : False := by grind
  exact eq73118

/-- `Equation4419`: `x ◇ (x ◇ y) = (z ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(Y,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_x_pyx_pyx_pxy_Equation4419 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4419 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4419.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X1) X0) := by
    intro X0 X1 X2
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
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 X0 y
       grind)
    | exact resolve eq10 eq25
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
  have eq51 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X1)) X2) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op X2 X1) X3
       have i₂ := eq14 X2 X1 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op X2 X1)) = (M.op (M.op X2 X1) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 X1) X0 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X1 X3
       have i₂ := eq14 X2 X1 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X0)) = (M.op (M.op X0 (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X0 (M.op x X1)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op X0 (M.op X0 y)) = (M.op (M.op x y) X0) := by
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
  have eq57 : ∀ X0 : G, (M.op X0 (M.op X0 (σ y))) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
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
  have eq82 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq76
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq77
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq77
    | exact resolve eq77 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq85 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq21 eq84
    | exact resolve eq84 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq93 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq104 : ∀ X1 : G, (M.op X1 (M.op X1 X1)) = (k (M.op X1 X1) X1) := by
    intro X1
    grind
  have eq105 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq93
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq93
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq93 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq93
       grind)
    | exact superpose eq93 eq16
    | exact resolve eq16 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq105
  have eq148 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
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
  have eq188 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq11 (σ X0) sF3
       grind)
    | exact superpose eq11 eq41
    | (have j1 := eq11 (σ X0) (σ y)
       grind)
    | exact resolve eq41 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq213 : (M.op x (M.op x y)) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq56 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq56
    | (have j0 := eq56 x
       grind)
    | exact resolve eq56 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq214 : ∀ X0 X1 : G, (M.op (M.op X0 y) X1) = (M.op (M.op x y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq56 X1
       have i₂ := eq14 X1 y X0
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 y))) = (M.op (M.op (M.op x y) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 y) X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq223 : ∀ X0 X1 : G, (M.op (M.op X0 (σ y)) X1) = (M.op (M.op (σ x) (σ y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X0
       have i₂ := eq14 X0 sF3 x
       grind)
    | exact superpose eq14 eq57
    | exact resolve eq57 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq227 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 (σ y))) X0) = (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq57 eq14
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq374 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 y)) = (M.op (M.op X0 y) (M.op (M.op x y) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq57 (M.op X0 y)
       have i₂ := eq214 X0 sF3
       grind)
    | (have i₁ := eq57 (M.op x y)
       have i₂ := eq214 X0 sF3
       grind)
    | exact superpose eq214 eq57
    | exact resolve eq57 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq375 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 y)) = (M.op (M.op x y) (M.op (M.op x y) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq374 X0
       have i₂ := eq214 X0 (M.op sF0 sF3)
       grind)
    | (have i₁ := eq374 x
       have i₂ := eq214 X0 (M.op sF0 sF3)
       grind)
    | exact superpose eq214 eq374
    | exact resolve eq374 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374
  have eq385 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 y)) = (M.op (M.op (σ x) (σ y)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq57 eq375
    | exact resolve eq375 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375
  have eq396 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) X0) X1) = (M.op (M.op X2 (M.op X0 y)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 (M.op X0 y) X1 X2
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq53
    | exact resolve eq53 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq397 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) X1) = (M.op (M.op X2 (M.op X0 (σ y))) X1) := by
    intro X0 X1 X2
    first
    | exact superpose eq57 eq53
    | exact resolve eq53 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq491 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (σ y))) = (M.op (M.op X0 (σ y)) (M.op (M.op (σ x) (σ y)) y)) := by
    intro X0
    first
    | exact superpose eq223 eq56
    | exact resolve eq56 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq492 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) = (M.op (M.op X0 (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq223 eq57
    | exact resolve eq57 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq493 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq223 eq492
    | exact resolve eq492 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492
  have eq494 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) y)) := by
    intro X0
    first
    | exact superpose eq223 eq491
    | exact resolve eq491 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491
  have eq503 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq57 eq493
    | exact resolve eq493 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493
  have eq504 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (σ y))) = (M.op (M.op x y) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq494 X0
       have i₂ := eq56 sF4
       grind)
    | exact superpose eq56 eq494
    | exact resolve eq494 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494
  have eq549 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X2)) X3) = (M.op X3 (M.op X3 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq55 X1 X2 X3
       have i₂ := eq53 X1 (M.op X1 X2) X3 X0
       grind)
    | (have i₁ := eq55 X1 X2 X3
       have i₂ := eq53 X0 (M.op X1 X2) X3 X1
       grind)
    | exact superpose eq53 eq55
    | exact resolve eq55 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq642 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 y) X0)) = (M.op (M.op (M.op x y) X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X1 y X0 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq51
    | exact resolve eq51 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq643 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 (σ y)) X0)) = (M.op (M.op (M.op (σ x) (σ y)) X0) X0) := by
    intro X0 X1
    first
    | exact superpose eq57 eq51
    | exact resolve eq51 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq729 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (M.op (σ x) (σ y)) X0) X0) := by
    intro X0
    first
    | exact superpose eq223 eq643
    | (have j0 := eq643 X0 (σ x)
       grind)
    | exact resolve eq643 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643
  have eq730 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) X0)) = (M.op (M.op (M.op x y) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq642 X0 x
       have i₂ := eq214 x X0
       grind)
    | (have i₁ := eq642 x x
       have i₂ := eq214 X0 x
       grind)
    | exact superpose eq214 eq642
    | (have j0 := eq642 X0 x
       grind)
    | exact resolve eq642 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642
  have eq775 : (M.op (M.op (σ x) (σ y)) (M.op x y)) = (M.op (M.op x y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq385 sF4
       have i₂ := eq56 sF4
       grind)
    | exact superpose eq56 eq385
    | exact resolve eq385 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1056 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (σ y)) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op X1 X0) (M.op X2 (σ y))) := by
    intro X0 X1 X2
    first
    | exact superpose eq57 eq52
    | exact resolve eq52 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1090 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) y) (M.op X1 (M.op X1 y))) := by
    intro X0 X1
    first
    | (have i₁ := eq56 (M.op X0 X1)
       have i₂ := eq52 X1 y (M.op X0 X1) X0
       grind)
    | exact superpose eq52 eq56
    | exact resolve eq56 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1091 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) (σ y)) (M.op X1 (M.op X1 (σ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq57 (M.op x X0)
       have i₂ := eq52 X0 sF3 (M.op x X0) x
       grind)
    | exact superpose eq52 eq57
    | exact resolve eq57 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1140 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op X1 (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq223 eq1091
    | exact resolve eq1091 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1091
  have eq1141 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 X1)) = (M.op (M.op x y) (M.op X1 (M.op X1 y))) := by
    intro X0 X1
    first
    | (have i₁ := eq1090 X0 X1
       have i₂ := eq214 (M.op X0 X1) (M.op X1 (M.op X1 y))
       grind)
    | exact superpose eq214 eq1090
    | exact resolve eq1090 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1090
  have eq1151 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op X1 X0) (M.op X2 (σ y))) := by
    intro X0 X1 X2
    first
    | exact superpose eq223 eq1056
    | exact resolve eq1056 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1056
  have eq1164 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq57 eq1140
    | exact resolve eq1140 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1140
  have eq1165 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 X1)) = (M.op (M.op x y) (M.op (M.op x y) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1141 X0 X1
       have i₂ := eq56 X1
       grind)
    | exact superpose eq56 eq1141
    | exact resolve eq1141 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1141
  have eq2057 : (M.op (M.op x y) y) = (M.op y (M.op (M.op (σ x) (σ y)) y)) := by
    first
    | (have i₁ := eq729 y
       have i₂ := eq214 sF4 y
       grind)
    | exact superpose eq214 eq729
    | exact resolve eq729 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729
  have eq2121 : (M.op (M.op x y) y) = (M.op y (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq730 y
       have i₂ := eq214 sF0 y
       grind)
    | exact superpose eq214 eq730
    | exact resolve eq730 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2122 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (M.op (M.op x y) (σ y))) := by
    first
    | exact superpose eq223 eq730
    | exact resolve eq730 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730
  have eq2176 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 y) (M.op (σ x) (σ y)))) = (M.op (M.op (M.op x y) y) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq2057 eq51
    | exact resolve eq51 eq2057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2057
  have eq2199 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) y)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 y) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq2176 X0
       have i₂ := eq14 sF4 y sF0
       grind)
    | exact superpose eq14 eq2176
    | exact resolve eq2176 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2176
  have eq2202 : (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) y)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) y))) := by
    first
    | (have i₁ := eq2199 x
       have i₂ := eq14 sF4 y x
       grind)
    | exact superpose eq14 eq2199
    | exact resolve eq2199 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2199
  have eq2203 : (M.op (M.op x y) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op x y) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq2202
       have i₂ := eq56 sF4
       grind)
    | exact superpose eq56 eq2202
    | exact resolve eq2202 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2202
  have eq2238 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op X0 y) (M.op x y))) = (M.op (M.op (M.op x y) y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq2121 eq51
    | exact resolve eq51 eq2121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2121
  have eq2262 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op x y) y)) = (M.op (M.op x y) (M.op (M.op X0 y) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq2238 X0
       have i₂ := eq14 sF0 y sF0
       grind)
    | exact superpose eq14 eq2238
    | exact resolve eq2238 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2238
  have eq2268 : (M.op (M.op x y) (M.op (M.op x y) y)) = (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op x y) y))) := by
    first
    | (have i₁ := eq2262 x
       have i₂ := eq14 sF0 y x
       grind)
    | exact superpose eq14 eq2262
    | exact resolve eq2262 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2262
  have eq2269 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq2268
       have i₂ := eq56 sF0
       grind)
    | exact superpose eq56 eq2268
    | exact resolve eq2268 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2268
  have eq2271 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op X0 (σ y)) (M.op x y))) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq2122 eq51
    | exact resolve eq51 eq2122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2122
  have eq2295 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op x y) (σ y))) = (M.op (M.op x y) (M.op (M.op X0 (σ y)) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq2271 X0
       have i₂ := eq14 sF0 sF3 sF4
       grind)
    | exact superpose eq14 eq2271
    | exact resolve eq2271 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2271
  have eq2301 : (M.op (M.op x y) (M.op (M.op x y) (σ y))) = (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op x y) (σ y)))) := by
    first
    | (have i₁ := eq2295 x
       have i₂ := eq14 sF0 sF3 x
       grind)
    | exact superpose eq14 eq2295
    | exact resolve eq2295 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2295
  have eq2302 : (M.op (M.op x y) (M.op (σ x) (σ y))) = (M.op (M.op x y) (M.op (M.op x y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq504 eq2301
    | exact resolve eq2301 eq504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq504 eq2301
  have eq2330 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op X0 y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq1164 X0 (M.op X0 y)
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq1164
    | exact resolve eq1164 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2424 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq385 eq2330
    | exact resolve eq2330 eq385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385 eq2330
  have eq2435 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op x y) (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq775 eq2424
    | exact resolve eq2424 eq775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2424
  have eq2436 : ∀ X0 : G, (M.op (M.op x y) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq2203 eq2435
    | exact resolve eq2435 eq2203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2435
  have eq2444 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op x y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq503 eq2436
    | exact resolve eq2436 eq503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503 eq2436
  have eq2672 : ∀ X0 : G, (M.op (M.op (M.op x y) (M.op (σ x) (σ y))) (M.op x y)) = (M.op (M.op x y) (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq2302 eq51
    | exact resolve eq51 eq2302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2689 : (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) = (M.op (M.op (M.op x y) (M.op (σ x) (σ y))) (M.op x y)) := by
    first
    | exact superpose eq1165 eq2672
    | exact resolve eq2672 eq1165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2672
  have eq2694 : (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) = (M.op (M.op x y) (M.op (M.op x y) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq2689
       have i₂ := eq14 sF0 sF4 sF0
       grind)
    | exact superpose eq14 eq2689
    | exact resolve eq2689 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2689
  have eq2696 : (M.op (M.op x y) (M.op (σ x) (σ y))) = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq2302 eq2694
    | exact resolve eq2694 eq2302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2302 eq2694
  have eq2698 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2269 eq2696
    | exact resolve eq2696 eq2269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2696
  have eq2801 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op x y) (M.op X0 y))) = (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1165 eq217
    | exact resolve eq217 eq1165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2805 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op X0 y))) = (M.op (M.op (M.op x y) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq1164 eq217
    | exact resolve eq217 eq1164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2898 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op X0 y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq2805 X0
       have i₂ := eq14 sF4 sF4 sF0
       grind)
    | exact superpose eq14 eq2805
    | exact resolve eq2805 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2805
  have eq2902 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op x y) (M.op X0 y))) = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq2801 X0
       have i₂ := eq14 sF0 sF0 sF0
       grind)
    | exact superpose eq14 eq2801
    | exact resolve eq2801 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2801
  have eq2953 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op X0 y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op x y) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq2444 eq2898
    | exact resolve eq2898 eq2444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2444 eq2898
  have eq2957 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op (M.op x y) (M.op X0 y))) := by
    intro X0
    first
    | exact superpose eq2269 eq2902
    | exact resolve eq2902 eq2269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2269 eq2902
  have eq2989 : ∀ X0 : G, (M.op (M.op x y) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op X0 y))) := by
    intro X0
    first
    | exact superpose eq2203 eq2953
    | exact resolve eq2953 eq2203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2203 eq2953
  have eq2993 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op x y) X0) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq2957 X0
       have i₂ := eq217 X0 sF0
       grind)
    | exact superpose eq217 eq2957
    | exact resolve eq2957 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2957
  have eq3007 : ∀ X0 : G, (M.op (M.op x y) (M.op (σ x) (σ y))) = (M.op (M.op (M.op x y) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq2989 X0
       have i₂ := eq217 X0 sF4
       grind)
    | exact superpose eq217 eq2989
    | exact resolve eq2989 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217 eq2989
  have eq3010 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq2993 x
       have i₂ := eq14 sF0 x sF0
       grind)
    | exact superpose eq14 eq2993
    | exact resolve eq2993 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2993
  have eq3019 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op x y) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq3007 x
       have i₂ := eq14 sF4 x sF0
       grind)
    | exact superpose eq14 eq3007
    | exact resolve eq3007 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3007
  have eq3025 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq2698 eq3019
    | exact resolve eq3019 eq2698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3019
  have eq3045 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op X0 X1)) := by
    intro X0 X1
    first
    | exact superpose eq1165 eq3010
    | exact resolve eq3010 eq1165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3010
  have eq3107 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | exact superpose eq1164 eq3025
    | exact resolve eq3025 eq1164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1164 eq3025
  have eq4168 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op x y) (M.op X2 X1)) X3) = (M.op (M.op (M.op X0 (M.op y X1)) y) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq396 (M.op X2 X1) X3 y
       have i₂ := eq51 X2 X1 y X0
       grind)
    | exact superpose eq51 eq396
    | exact resolve eq396 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4358 : ∀ X1 X2 X3 : G, (M.op (M.op x y) X3) = (M.op (M.op (M.op x y) (M.op X2 X1)) X3) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq4168 x X1 X2 X3
       have i₂ := eq214 (M.op x (M.op y X1)) X3
       grind)
    | exact superpose eq214 eq4168
    | exact resolve eq4168 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4168
  have eq4420 : ∀ X3 : G, (M.op (M.op x y) X3) = (M.op (M.op (M.op x y) (M.op x y)) X3) := by
    intro X3
    first
    | exact superpose eq3045 eq4358
    | (have j0 := eq4358 y x X3
       grind)
    | exact resolve eq4358 eq3045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3045 eq4358
  have eq4465 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (M.op (M.op X0 (M.op x y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4420 x
       have i₂ := eq53 sF0 sF0 x x
       grind)
    | (have i₁ := eq4420 x
       have i₂ := eq53 X0 sF0 x sF0
       grind)
    | exact superpose eq53 eq4420
    | exact resolve eq4420 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4795 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 y)) X1) = (M.op (M.op X2 (M.op (M.op x y) (σ y))) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq397 (M.op X0 y) X1 X2
       have i₂ := eq214 X0 sF3
       grind)
    | (have i₁ := eq397 (M.op x y) X1 X2
       have i₂ := eq214 X0 sF3
       grind)
    | exact superpose eq214 eq397
    | exact resolve eq397 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4811 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op X2 X1)) X3) = (M.op (M.op (M.op X0 (M.op (σ y) X1)) (σ y)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq397 (M.op X0 X1) X1 sF3
       have i₂ := eq51 X0 X1 sF3 X3
       grind)
    | exact superpose eq51 eq397
    | exact resolve eq397 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq5014 : ∀ X1 X2 X3 : G, (M.op (M.op (σ x) (σ y)) X3) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X2 X1)) X3) := by
    intro X1 X2 X3
    first
    | exact superpose eq223 eq4811
    | exact resolve eq4811 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223 eq4811
  have eq5028 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 y)) X1) = (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq397 eq4795
    | exact resolve eq4795 eq397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397 eq4795
  have eq5084 : ∀ X3 : G, (M.op (M.op (σ x) (σ y)) X3) = (M.op (M.op (M.op x y) (M.op x y)) X3) := by
    intro X3
    first
    | exact superpose eq3107 eq5014
    | exact resolve eq5014 eq3107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5014
  have eq5096 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 y)) X1) = (M.op (M.op (M.op x y) (M.op (σ x) (σ y))) X1) := by
    intro X0 X1
    first
    | exact superpose eq775 eq5028
    | exact resolve eq5028 eq775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775 eq5028
  have eq5137 : ∀ X3 : G, (M.op (M.op x y) X3) = (M.op (M.op (σ x) (σ y)) X3) := by
    intro X3
    first
    | exact superpose eq4420 eq5084
    | exact resolve eq5084 eq4420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5084
  have eq5145 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 y)) X1) = (M.op (M.op (M.op x y) (M.op x y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq2698 eq5096
    | exact resolve eq5096 eq2698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2698 eq5096
  have eq5171 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq4420 eq5145
    | exact resolve eq5145 eq4420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4420 eq5145
  have eq5182 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (M.op (M.op (M.op x y) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5171 X0 X1
       have i₂ := eq396 X0 X1 sF4
       grind)
    | exact superpose eq396 eq5171
    | exact resolve eq5171 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396 eq5171
  have eq6466 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op x y) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5182 X1 X2
       have i₂ := eq53 sF0 X1 X2 x
       grind)
    | (have i₁ := eq5182 X1 X2
       have i₂ := eq53 X0 X1 X2 sF0
       grind)
    | exact superpose eq53 eq5182
    | exact resolve eq5182 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq7086 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X1)) = (M.op (M.op (M.op x y) (M.op (M.op x y) X0)) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq1165 eq549
    | exact resolve eq549 eq1165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549 eq1165
  have eq7413 : ∀ X1 X2 : G, (M.op X2 (M.op X2 X1)) = (M.op (M.op x y) X2) := by
    intro X1 X2
    first
    | exact superpose eq5182 eq7086
    | exact resolve eq7086 eq5182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5182 eq7086
  have eq9808 : ∀ X0 X1 X2 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op X1 X0) (M.op X2 (σ y))) := by
    intro X0 X1 X2
    first
    | exact superpose eq3107 eq1151
    | exact resolve eq1151 eq3107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1151 eq3107
  have eq9989 : ∀ X2 : G, (M.op (M.op (M.op x y) (M.op x y)) X2) = (M.op X2 (M.op (M.op (σ x) (σ y)) X2)) := by
    intro X2
    first
    | exact superpose eq9808 eq227
    | exact resolve eq227 eq9808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227 eq9808
  have eq10056 : ∀ X2 : G, (M.op (M.op (M.op x y) (M.op x y)) X2) = (M.op X2 (M.op (M.op x y) X2)) := by
    intro X2
    first
    | exact superpose eq5137 eq9989
    | exact resolve eq9989 eq5137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9989
  have eq10129 : ∀ X2 : G, (M.op (M.op x y) X2) = (M.op X2 (M.op (M.op x y) X2)) := by
    intro X2
    first
    | exact superpose eq4465 eq10056
    | exact resolve eq10056 eq4465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4465 eq10056
  have eq14391 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq148 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq148
    | (have j0 := eq148 x
       grind)
    | exact resolve eq148 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq14429 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq14391
  have eq14458 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14429
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq14429
    | exact resolve eq14429 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14429
  have eq14471 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq14458
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq14458 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14458
  have eq14480 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq14471 eq50
    | exact resolve eq50 eq14471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq14551 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq188 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq188
    | (have j0 := eq188 y
       grind)
    | exact resolve eq188 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq14598 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq14551
  have eq14634 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq14598
       have i₂ := eq93
       grind)
    | exact superpose eq93 eq14598
    | exact resolve eq14598 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14598
  have eq14653 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq14634
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq14634 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14634
  have eq14671 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq14653 eq110
    | exact resolve eq110 eq14653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq20105 : (σ (M.op x x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq14471 eq82
    | exact resolve eq82 eq14471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq20324 : (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq14653 eq111
    | exact resolve eq111 eq14653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq24935 : (M.op x x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq20105
       grind)
    | exact superpose eq20105 eq16
    | exact resolve eq16 eq20105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20105
  have eq24985 : (k x x) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq14480 eq24935
    | exact resolve eq24935 eq14480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14480 eq24935
  have eq24997 : (k x x) = (M.op x x) := by
    first
    | (have j1 := eq13 x x
       grind)
    | (have r₁ := eq24985
       have r₂ := eq13 x x
       grind)
    | exact resolve eq24985 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24985
  have eq25914 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq24997
       grind)
    | exact superpose eq24997 eq44
    | exact resolve eq44 eq24997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq24997
  have eq25933 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq14471 eq25914
    | exact resolve eq25914 eq14471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14471 eq25914
  have eq25948 : (σ (k (M.op x x) x)) = (k (M.op (σ x) (σ x)) (σ x)) := by
    first
    | (have i₁ := eq40 (M.op x x)
       have i₂ := eq25933
       grind)
    | exact superpose eq25933 eq40
    | exact resolve eq40 eq25933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq25933
  have eq25995 : (M.op (σ x) (M.op (σ x) (σ x))) = (σ (k (M.op x x) x)) := by
    first
    | (have i₁ := eq25948
       have i₂ := eq104 sF2
       grind)
    | exact superpose eq104 eq25948
    | exact resolve eq25948 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25948
  have eq26007 : (M.op (σ x) (M.op (σ x) (σ x))) = (σ (M.op x (M.op x x))) := by
    first
    | (have i₁ := eq25995
       have i₂ := eq104 x
       grind)
    | exact superpose eq104 eq25995
    | exact resolve eq25995 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25995
  have eq26014 : (σ (M.op (M.op x y) x)) = (M.op (σ x) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq26007
       have i₂ := eq7413 x x
       grind)
    | exact superpose eq7413 eq26007
    | exact resolve eq26007 eq7413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26007
  have eq26020 : (σ (M.op (M.op x y) x)) = (M.op (M.op x y) (σ x)) := by
    first
    | (have i₁ := eq26014
       have i₂ := eq7413 sF2 sF2
       grind)
    | exact superpose eq7413 eq26014
    | exact resolve eq26014 eq7413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26014
  have eq26024 : (σ (M.op x (M.op x y))) = (M.op (M.op x y) (σ x)) := by
    first
    | exact superpose eq213 eq26020
    | exact resolve eq26020 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26020
  have eq29326 : (M.op y y) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq20324
       grind)
    | exact superpose eq20324 eq16
    | exact resolve eq16 eq20324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20324
  have eq29386 : (M.op y y) = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq14671 eq29326
    | exact resolve eq29326 eq14671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29326
  have eq29400 : (M.op y y) = (k y y) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq29386
       have r₂ := eq13 y y
       grind)
    | exact resolve eq29386 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29386
  have eq29431 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq93
       have i₂ := eq29400
       grind)
    | exact superpose eq29400 eq93
    | exact resolve eq93 eq29400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq29453 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq14653 eq29431
    | exact resolve eq29431 eq14653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14653 eq29431
  have eq29467 : (σ (k (M.op y y) y)) = (k (M.op (σ y) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq41 (M.op y y)
       have i₂ := eq29453
       grind)
    | exact superpose eq29453 eq41
    | exact resolve eq41 eq29453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq29523 : (M.op (σ y) (M.op (σ y) (σ y))) = (σ (k (M.op y y) y)) := by
    first
    | (have i₁ := eq29467
       have i₂ := eq104 sF3
       grind)
    | exact superpose eq104 eq29467
    | exact resolve eq29467 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29467
  have eq29537 : (M.op (σ y) (M.op (σ y) (σ y))) = (σ (M.op y (M.op y y))) := by
    first
    | (have i₁ := eq29523
       have i₂ := eq104 y
       grind)
    | exact superpose eq104 eq29523
    | exact resolve eq29523 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq29523
  have eq29548 : (σ (M.op (M.op x y) y)) = (M.op (σ y) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq29537
       have i₂ := eq56 y
       grind)
    | exact superpose eq56 eq29537
    | exact resolve eq29537 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq29537
  have eq29557 : (σ (M.op (M.op x y) y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq57 eq29548
    | exact resolve eq29548 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq29548
  have eq29561 : (σ (M.op (M.op x y) y)) = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq5137 eq29557
    | exact resolve eq29557 eq5137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5137 eq29557
  have eq45874 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq85 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45884 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq27 eq45874
    | exact resolve eq45874 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45874
  have eq45895 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq45884
       have r₂ := eq28
       grind)
    | exact resolve eq45884 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45884
  have eq45900 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq45895 eq13
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq45895
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq45895
       grind)
    | exact resolve eq13 eq45895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45895
  have eq45928 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq45900
  have eq45948 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq45928 eq85
    | exact resolve eq85 eq45928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq45928
  have eq45966 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq45948
  have eq45982 : (τ (σ x)) = (k y y) ∨ x = (M.op y y) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq45966 eq14671
    | exact resolve eq14671 eq45966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14671 eq45966
  have eq46066 : (τ (σ x)) = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq45982
       have i₂ := eq29400
       grind)
    | exact superpose eq29400 eq45982
    | exact resolve eq45982 eq29400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29400 eq45982
  have eq46083 : x = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq29 eq46066
    | exact resolve eq46066 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq46066
  have eq46084 : y = (M.op y x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq46083
  have eq46113 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op y X0) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq6466 y x X0
       have i₂ := eq46084
       grind)
    | exact superpose eq46084 eq6466
    | exact resolve eq6466 eq46084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46427 : (M.op y x) = (M.op x (M.op x y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq213 eq46113
    | exact resolve eq46113 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46113
  have eq46862 : y = (M.op x (M.op x y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq46084
       have i₂ := eq46427
       grind)
    | exact superpose eq46427 eq46084
    | exact resolve eq46084 eq46427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46084 eq46427
  have eq46889 : y = (M.op x (M.op x y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq46862
  have eq46921 : (σ y) = (M.op (M.op x y) (σ x)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq46889 eq26024
    | exact resolve eq26024 eq46889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46949 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq46889 eq7413
    | exact resolve eq7413 eq46889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7413 eq46889
  have eq46955 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq213 eq46949
    | exact resolve eq46949 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213 eq46949
  have eq46977 : (σ y) = (M.op (M.op x y) (σ x)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq46921
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq46921
    | exact resolve eq46921 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq46921
  have eq46980 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq46955
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq46955
    | exact resolve eq46955 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46955
  have eq47310 : (σ (M.op x y)) = (M.op (M.op x y) (σ x)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq46980 eq26024
    | exact resolve eq26024 eq46980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46980
  have eq47361 : (σ (M.op x y)) = (M.op (M.op x y) (σ x)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq21 eq47310
    | exact resolve eq47310 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47310
  have eq47811 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq47361 eq46977
    | exact resolve eq46977 eq47361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46977 eq47361
  have eq47865 : x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq47811
  have eq47912 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq29453
       have i₂ := eq47865
       grind)
    | exact superpose eq47865 eq29453
    | exact resolve eq29453 eq47865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29453
  have eq47917 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op x X0) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq214 y X0
       have i₂ := eq47865
       grind)
    | exact superpose eq47865 eq214
    | exact resolve eq214 eq47865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214 eq47865
  have eq47978 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq47912
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq47912
    | exact resolve eq47912 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq47912
  have eq48042 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ x) X0) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq47978 eq6466
    | exact resolve eq6466 eq47978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6466 eq47978
  have eq48292 : (σ (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq47917 eq29561
    | exact resolve eq29561 eq47917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29561 eq47917
  have eq48510 : (σ (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq48292
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq48292
    | exact resolve eq48292 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48292
  have eq48558 : (σ (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq21 eq48510
    | exact resolve eq48510 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48510
  have eq50201 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq27 eq48042
    | (have j0 := eq48042 (σ y)
       grind)
    | exact resolve eq48042 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48042
  have eq50874 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq50201 eq48558
    | exact resolve eq48558 eq50201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48558 eq50201
  have eq50939 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq50874
  have eq50965 : (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq50939
       have r₂ := eq28
       grind)
    | exact resolve eq50939 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50939
  have eq50979 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq50965 eq27
    | exact resolve eq27 eq50965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq50980 : y = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq50965 eq30
    | exact resolve eq30 eq50965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq50965
  have eq51159 : y = (M.op x y) := by
    first
    | exact superpose eq31 eq50980
    | exact resolve eq50980 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq50980
  have eq52051 : ∀ X0 : G, (M.op y X0) = (M.op X0 (M.op y X0)) := by
    intro X0
    first
    | exact superpose eq51159 eq10129
    | exact resolve eq10129 eq51159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10129
  have eq52098 : (σ (M.op x y)) = (M.op y (σ x)) := by
    first
    | exact superpose eq51159 eq26024
    | exact resolve eq26024 eq51159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26024 eq51159
  have eq52192 : (σ (M.op x y)) = (M.op y (σ x)) := by
    first
    | (have i₁ := eq52098
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq52098
    | exact resolve eq52098 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq52098
  have eq52318 : (σ (M.op x y)) = (M.op y (σ x)) := by
    first
    | exact superpose eq21 eq52192
    | exact resolve eq52192 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq52192
  have eq54455 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq52318 eq52051
    | exact resolve eq52051 eq52318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52051 eq52318
  have eq54724 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq50979 eq54455
    | exact resolve eq54455 eq50979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50979 eq54455
  have eq54815 : False := by grind
  exact eq54815
