import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = m(X,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pxy_pyx_pyy_pxy_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
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
  have eq29 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  clear eq19
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
  have eq63 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq23
  have eq66 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X2 X1) (M.op X0 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq63 X1 (M.op (M.op X2 X1) (M.op X0 X0))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq63
    | exact resolve eq63 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 X0
       have i₂ := eq63 X0 X0
       grind)
    | exact superpose eq63 eq9
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 X3
       have i₂ := eq63 X1 X0
       grind)
    | exact superpose eq63 eq9
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 (M.op X0 X0)) X0
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq9
    | exact resolve eq9 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq66 X1 (M.op (M.op x x) (M.op X0 X0)) x
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq66
    | exact resolve eq66 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq105 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq105 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq105
    | (have j0 := eq105 (σ X0)
       grind)
    | exact resolve eq105 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq105 (τ X0)
       grind)
    | exact superpose eq105 eq18
    | (have j1 := eq105 (τ X0)
       grind)
    | exact resolve eq18 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq132 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq131 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq131
    | (have j0 := eq131 X0
       grind)
    | exact resolve eq131 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq150 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X1 X1))
       have i₂ := eq74 X1 X0
       grind)
    | exact superpose eq74 eq9
    | exact resolve eq9 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq151 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq74 X0 X0
       grind)
    | exact superpose eq74 eq9
    | exact resolve eq9 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq156 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq84 X0 (M.op X1 (M.op X1 X1))
       have i₂ := eq74 X1 X1
       grind)
    | exact superpose eq74 eq84
    | exact resolve eq84 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq207 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq150 X2 X1 (M.op X0 (M.op X0 X0))
       have i₂ := eq150 X0 X0 X0
       grind)
    | exact superpose eq150 eq150
    | exact resolve eq150 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq259 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq156 X2 X3
       have i₂ := eq151 X2 X0 X1
       grind)
    | exact superpose eq151 eq156
    | exact resolve eq156 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq261 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X2)) (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq150 X2 X3 X2
       have i₂ := eq151 X2 X0 X1
       grind)
    | exact superpose eq151 eq150
    | exact resolve eq150 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq263 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X0 (M.op (M.op X1 X0) X2)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq84 X2 X2
       have i₂ := eq151 X2 X0 X1
       grind)
    | exact superpose eq151 eq84
    | exact resolve eq84 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq268 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X3 (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 X3) X3 X2
       have i₂ := eq151 (M.op X2 X3) X0 X1
       grind)
    | exact superpose eq151 eq9
    | exact resolve eq9 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq397 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) (M.op (M.op X3 (M.op X0 X0)) (M.op X0 X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq259 (M.op X3 (M.op X0 X0)) (M.op x (M.op X3 X3)) X2 X1
       have i₂ := eq150 X3 x X0
       grind)
    | exact superpose eq150 eq259
    | exact resolve eq259 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq966 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq71 X0 (M.op X1 X0) X2 X3
       have i₂ := eq151 X0 X0 X1
       grind)
    | exact superpose eq151 eq71
    | exact resolve eq71 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151
  have eq973 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X1 X2))) = (M.op X2 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq71 (M.op X0 (M.op X1 X2)) (M.op X1 X2) X2 X1
       have i₂ := eq71 (M.op X1 X2) X0 (M.op X1 X2) X0
       grind)
    | exact superpose eq71 eq71
    | exact resolve eq71 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1030 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq966 X0 X1 x x
       have i₂ := eq71 X0 X0 x x
       grind)
    | exact superpose eq71 eq966
    | exact resolve eq966 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq966
  have eq1908 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op X1 (M.op (M.op X2 X1) X0)))) = (M.op (M.op X3 (M.op (M.op X4 X0) (M.op X4 X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq207 (M.op X1 (M.op (M.op X2 X1) X0)) X3 (M.op X4 X0)
       have i₂ := eq259 X1 X2 X0 X4
       grind)
    | exact superpose eq259 eq207
    | exact resolve eq207 eq259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2060 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op X1 (M.op (M.op X2 X1) X0)))) = (M.op (M.op X3 (M.op X0 (M.op X4 X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1908 X0 X1 X2 X3 X4
       have i₂ := eq63 X4 X0
       grind)
    | exact superpose eq63 eq1908
    | exact resolve eq1908 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1908
  have eq2111 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op (M.op (M.op X2 X1) X0) (M.op X1 (M.op (M.op X2 X1) X0)))) = (M.op (M.op X3 (M.op X0 (M.op X4 X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2060 X0 X1 X2 X3 X4
       have i₂ := eq63 X1 (M.op (M.op X2 X1) X0)
       grind)
    | exact superpose eq63 eq2060
    | exact resolve eq2060 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2060
  have eq2135 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) X0) = (M.op (M.op X3 (M.op X0 (M.op X4 X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2111 X0 X1 X2 X3 X4
       have i₂ := eq259 X1 X2 X0 (M.op X2 X1)
       grind)
    | exact superpose eq259 eq2111
    | exact resolve eq2111 eq259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2111
  have eq2140 : ∀ X0 X3 X4 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 (M.op X4 X0))) X0) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq2135 X0 x x X3 X4
       have i₂ := eq263 x x X0
       grind)
    | exact superpose eq263 eq2135
    | exact resolve eq2135 eq263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263 eq2135
  have eq2159 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X2 (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0)))) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2140 (M.op X1 X0) X2 (M.op x (M.op X1 X1))
       have i₂ := eq207 X0 x X1
       grind)
    | exact superpose eq207 eq2140
    | exact resolve eq2140 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2226 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X2 X0) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2159 X0 X1 X2
       have i₂ := eq156 X0 X1
       grind)
    | exact superpose eq156 eq2159
    | exact resolve eq2159 eq156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2159
  have eq2242 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X0) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2226 X0 X1 X2
       have i₂ := eq63 X1 X0
       grind)
    | exact superpose eq63 eq2226
    | exact resolve eq2226 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq2226
  have eq3303 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 (M.op X3 (M.op X4 X0))) X0) = (M.op (M.op X1 (M.op (M.op (M.op X2 (M.op X3 (M.op X4 X0))) X0) (M.op (M.op X2 (M.op X3 (M.op X4 X0))) X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq261 (M.op X4 X0) X3 (M.op (M.op X2 (M.op X3 (M.op X4 X0))) X0) X1
       have i₂ := eq259 (M.op X3 (M.op X4 X0)) X2 X0 X4
       grind)
    | exact superpose eq259 eq261
    | exact resolve eq261 eq259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3426 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 (M.op X3 (M.op X4 X0))) X0) = (M.op (M.op X1 (M.op X0 (M.op (M.op X2 (M.op X3 (M.op X4 X0))) X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq3303 X0 X1 X2 X3 X4
       have i₂ := eq2242 X0 (M.op X2 (M.op X3 (M.op X4 X0))) (M.op X2 (M.op X3 (M.op X4 X0)))
       grind)
    | exact superpose eq2242 eq3303
    | exact resolve eq3303 eq2242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3303
  have eq3484 : ∀ X0 X2 X3 X4 : G, (M.op X0 X0) = (M.op (M.op X2 (M.op X3 (M.op X4 X0))) X0) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq3426 X0 x X2 X3 X4
       have i₂ := eq2140 X0 x (M.op X2 (M.op X3 (M.op X4 X0)))
       grind)
    | exact superpose eq2140 eq3426
    | exact resolve eq3426 eq2140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2140 eq3426
  have eq4208 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq268 (M.op X1 X1) x X1 (M.op X0 X0)
       have i₂ := eq150 X1 x X0
       grind)
    | exact superpose eq150 eq268
    | exact resolve eq268 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150 eq268
  have eq4334 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4208 X0 X1
       have i₂ := eq2242 X0 (M.op X1 X1) X0
       grind)
    | exact superpose eq2242 eq4208
    | exact resolve eq4208 eq2242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4208
  have eq4378 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = (M.op (M.op X1 X1) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4334 (M.op X1 X0) (M.op X1 X1)
       have i₂ := eq207 X0 (M.op X1 X1) X1
       grind)
    | exact superpose eq207 eq4334
    | exact resolve eq4334 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq4469 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 (M.op X0 X0)) X2) (M.op (M.op X1 (M.op X0 X0)) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq259 (M.op X0 X0) X1 X2 (M.op X1 (M.op X0 X0))
       have i₂ := eq4334 (M.op (M.op X1 (M.op X0 X0)) X2) X0
       grind)
    | exact superpose eq4334 eq259
    | exact resolve eq259 eq4334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4334
  have eq4495 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op (M.op X1 (M.op X0 X0)) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4469 X0 X1 X2
       have i₂ := eq2242 X2 (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X0 X0))
       grind)
    | exact superpose eq2242 eq4469
    | exact resolve eq4469 eq2242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4469
  have eq4538 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = (M.op (M.op X1 X1) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4378 X0 X1
       have i₂ := eq2242 X0 X1 X1
       grind)
    | exact superpose eq2242 eq4378
    | exact resolve eq4378 eq2242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4378
  have eq4577 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4538 X0 X1
       have i₂ := eq156 X0 X1
       grind)
    | exact superpose eq156 eq4538
    | exact resolve eq4538 eq156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156 eq4538
  have eq4652 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4577 (M.op (M.op X2 X1) X0) X1
       have i₂ := eq259 X1 X2 X0 (M.op X2 X1)
       grind)
    | exact superpose eq259 eq4577
    | exact resolve eq4577 eq259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4849 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4652 (M.op X0 (M.op X2 X0)) X2 X1
       have i₂ := eq4577 X0 X2
       grind)
    | exact superpose eq4577 eq4652
    | exact resolve eq4652 eq4577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4577 eq4652
  have eq5249 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq6018 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X2 (M.op X3 (M.op X1 X1))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq4495 X1 X3 (M.op (M.op X2 (M.op X3 (M.op X1 X1))) X0)
       have i₂ := eq259 (M.op X3 (M.op X1 X1)) X2 X0 (M.op X2 (M.op X3 (M.op X1 X1)))
       grind)
    | exact superpose eq259 eq4495
    | exact resolve eq4495 eq259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6070 : ∀ X0 X1 X2 X3 : G, (M.op X3 X0) = (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X2 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq71 X0 (M.op X1 (M.op (M.op X2 X3) (M.op X2 X3))) X3 X2
       have i₂ := eq4495 (M.op X2 X3) X1 X0
       grind)
    | exact superpose eq4495 eq71
    | exact resolve eq71 eq4495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq4495
  have eq6097 : ∀ X0 X1 X2 X3 : G, (M.op X3 X0) = (M.op (M.op X1 (M.op X3 (M.op X2 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6070 X0 X1 X2 X3
       have i₂ := eq2242 X3 X2 X2
       grind)
    | exact superpose eq2242 eq6070
    | exact resolve eq6070 eq2242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6070
  have eq9515 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq5249 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X0)
       have i₂ := eq5249 X0 X1
       grind)
    | exact superpose eq5249 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq5249 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq5249 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq5249 X1 X1
       grind)
    | exact resolve eq13 eq5249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9539 : ∀ X0 X1 X2 X3 : G, (M.op (σ X1) (σ X1)) = (M.op (M.op X2 (M.op X3 (M.op (σ X0) (σ X0)))) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3484 (σ X1) X2 X3 (σ X0)
       have i₂ := eq5249 X0 X1
       grind)
    | (have i₁ := eq3484 (σ X0) X2 X3 (σ X0)
       have i₂ := eq5249 X0 X1
       grind)
    | exact superpose eq5249 eq3484
    | (have j1 := eq5249 X0 X1
       grind)
    | exact resolve eq3484 eq5249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3484 eq5249
  have eq9551 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq9515 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9515
  have eq9552 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq9551 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9551
  have eq9556 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9539 X0 X1 x x
       have i₂ := eq6018 (σ X1) (σ X0) x x
       grind)
    | exact superpose eq6018 eq9539
    | (have j0 := eq9539 X0 X1 x x
       grind)
    | exact resolve eq9539 eq6018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6018 eq9539
  have eq9562 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9552 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq9552
    | (have j0 := eq9552 X0 X1
       grind)
    | exact resolve eq9552 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9552
  have eq9620 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X3) (M.op (M.op X4 (M.op X0 X1)) (M.op (M.op X1 (M.op (M.op X0 X1) (M.op X0 X1))) X3))) = X3 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq397 (M.op X1 (M.op (M.op X0 X1) (M.op X0 X1))) X2 X3 X4
       have i₂ := eq261 X1 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq261 eq397
    | exact resolve eq397 eq261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261 eq397
  have eq9864 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X3) (M.op (M.op X4 (M.op X0 X1)) (M.op (M.op X1 (M.op X1 (M.op X0 X1))) X3))) = X3 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9620 X0 X1 X2 X3 X4
       have i₂ := eq2242 X1 X0 X0
       grind)
    | exact superpose eq2242 eq9620
    | exact resolve eq9620 eq2242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2242 eq9620
  have eq9916 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X3) (M.op (M.op X4 (M.op X0 X1)) (M.op X1 X3))) = X3 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9864 X0 X1 X2 X3 X4
       have i₂ := eq6097 X3 X1 X0 X1
       grind)
    | exact superpose eq6097 eq9864
    | exact resolve eq9864 eq6097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6097 eq9864
  have eq14971 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 X0) = (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq4849 (M.op X4 X0) X1 (M.op X2 (M.op X3 X4))
       have i₂ := eq9916 X3 X4 X4 X0 X2
       grind)
    | exact superpose eq9916 eq4849
    | exact resolve eq4849 eq9916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4849 eq9916
  have eq18301 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq124 X0
       have i₂ := eq105 X0
       grind)
    | exact superpose eq105 eq124
    | (have j0 := eq124 X0
       have j1 := eq105 (σ X0)
       grind)
    | exact resolve eq124 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq124
  have eq19051 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq132 X0
       grind)
    | exact superpose eq132 eq10
    | (have j1 := eq132 X0
       grind)
    | exact resolve eq10 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq27705 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq9562 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9562
  have eq27783 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq27705 X0 X1
       have j1 := eq9556 X0 X1
       grind)
    | (have r₁ := eq27705 X0 X1
       have r₂ := eq9556 X0 X1
       grind)
    | (have r₁ := eq27705 X0 X0
       have r₂ := eq9556 X0 X0
       grind)
    | exact resolve eq27705 eq9556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9556 eq27705
  have eq27824 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq27783 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27783
  have eq27853 : ∀ X0 X2 : G, (σ X2) = (M.op (σ X0) (σ X0)) ∨ (σ (k X2 X0)) = (M.op (σ X2) (σ X0)) := by
    intro X0 X2
    first
    | (have j0 := eq27824 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27824
  have eq27885 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq27853 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27853
  have eq27894 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  have eq27900 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq27885 (τ X0) (τ X1)
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq27885
    | (have j0 := eq27885 (τ X0) (τ X1)
       grind)
    | exact resolve eq27885 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq27917 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq27885 X0 X1
       grind)
    | exact superpose eq27885 eq10
    | (have j1 := eq27885 X0 X1
       grind)
    | exact resolve eq10 eq27885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27938 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq27900 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq27900
    | (have j0 := eq27900 X0 X1
       grind)
    | exact resolve eq27900 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27900
  have eq27955 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq27938 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq27938
    | (have j0 := eq27938 X0 X1
       grind)
    | exact resolve eq27938 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27938
  have eq27960 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq27955 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq27955
    | (have j0 := eq27955 X0 X1
       grind)
    | exact resolve eq27955 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27955
  have eq27965 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq27960 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq27960
    | (have j0 := eq27960 X0 X1
       grind)
    | exact resolve eq27960 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27960
  have eq27970 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq27965 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq27965
    | (have j0 := eq27965 X0 X1
       grind)
    | exact resolve eq27965 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27965
  have eq27984 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq27885 X0 X1
       have i₂ := eq27970 X0 X1
       grind)
    | exact superpose eq27970 eq27885
    | (have j0 := eq27885 X0 X1
       have j1 := eq27970 (σ X0) (σ X1)
       grind)
    | exact resolve eq27885 eq27970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27885
  have eq31716 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op X3 (M.op X1 (M.op X2 X0))) (M.op X0 (M.op X0 (M.op X1 (M.op X2 X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq259 X0 X2 (M.op X1 (M.op X2 X0)) X3
       have i₂ := eq973 X1 X2 X0
       grind)
    | exact superpose eq973 eq259
    | exact resolve eq259 eq973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259 eq973
  have eq31861 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op X0 (M.op X0 (M.op X0 (M.op X1 (M.op X2 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31716 X0 X1 X2 x
       have i₂ := eq14971 (M.op X0 (M.op X0 (M.op X1 (M.op X2 X0)))) x X1 X2 X0
       grind)
    | exact superpose eq14971 eq31716
    | exact resolve eq31716 eq14971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14971 eq31716
  have eq59837 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq19051 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19051
  have eq59859 : ∀ X0 : G, (τ (σ X0)) ≠ (k X0 (τ (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq59837 (σ X0)
       have i₂ := eq29 X0 (σ X0)
       grind)
    | exact superpose eq29 eq59837
    | (have j0 := eq59837 (σ X0)
       grind)
    | exact resolve eq59837 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq59837
  have eq59860 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq59859 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq59859
    | (have j0 := eq59859 X0
       grind)
    | exact resolve eq59859 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59859
  have eq59863 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq59860 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq59860
    | (have j0 := eq59860 X0
       grind)
    | exact resolve eq59860 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59860
  have eq133877 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    grind
  have eq133878 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq68 (σ X0)
       have i₂ := eq18301 X0
       grind)
    | exact superpose eq18301 eq68
    | (have j1 := eq18301 X0
       grind)
    | exact resolve eq68 eq18301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18301
  have eq134022 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq133877 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq133877
    | (have j0 := eq133877 X0
       grind)
    | exact resolve eq133877 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133877
  have eq134037 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    grind
  clear eq134022
  have eq445908 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq27984 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27984
  have eq454275 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq445908 x y
       grind)
    | exact superpose eq445908 eq16
    | (have j1 := eq445908 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq445908 x y
       grind)
    | exact resolve eq16 eq445908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445908
  have eq454626 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq454275
  have eq454747 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq27917 y y
       have i₂ := eq454626
       grind)
    | exact superpose eq454626 eq27917
    | exact resolve eq27917 eq454626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27917
  have eq454752 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  have eq454858 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1030 (σ y) (σ y)
       have i₂ := eq454626
       grind)
    | exact superpose eq454626 eq1030
    | exact resolve eq1030 eq454626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq455118 : (σ (k x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq454752
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq454752
    | exact resolve eq454752 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454752
  have eq455121 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq454747
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq454747
    | exact resolve eq454747 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454747
  have eq455140 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27970 eq455118
    | (have j1 := eq27970 x y
       grind)
    | exact resolve eq455118 eq27970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455118
  have eq455152 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq454858
       grind)
    | exact superpose eq454858 eq16
    | exact resolve eq16 eq454858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454858
  have eq455507 : x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq27970 y y
       have i₂ := eq455121
       grind)
    | exact superpose eq455121 eq27970
    | (have j0 := eq27970 x y
       grind)
    | exact resolve eq27970 eq455121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27970 eq455121
  have eq455509 : y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq455507
  have eq455829 : (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq27894 y
       have i₂ := eq455509
       grind)
    | exact superpose eq455509 eq27894
    | (have j0 := eq27894 y
       grind)
    | exact resolve eq27894 eq455509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq456222 : (σ x) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq454626 eq455829
    | exact resolve eq455829 eq454626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455829
  have eq456264 : (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq454626 eq456222
    | exact resolve eq456222 eq454626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456222
  have eq456265 : (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by grind
  clear eq456264
  have eq456279 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq455509 eq456265
    | exact resolve eq456265 eq455509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455509 eq456265
  have eq456280 : x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq456279
  have eq456289 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq456280 eq454626
    | exact resolve eq454626 eq456280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454626
  have eq456291 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq456280 eq455140
    | exact resolve eq455140 eq456280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455140 eq456280
  have eq480535 : (σ (M.op x y)) = (σ x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq456289 eq456291
    | exact resolve eq456291 eq456289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456289 eq456291
  have eq480536 : x = (M.op y y) := by
    first
    | (have r₁ := eq480535
       have r₂ := eq455152
       grind)
    | exact resolve eq480535 eq455152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455152 eq480535
  have eq480544 : y = (M.op y (M.op y x)) := by
    first
    | (have i₁ := eq68 y
       have i₂ := eq480536
       grind)
    | exact superpose eq480536 eq68
    | exact resolve eq68 eq480536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq480651 : x = (M.op x y) := by
    first
    | (have i₁ := eq1030 y y
       have i₂ := eq480536
       grind)
    | exact superpose eq480536 eq1030
    | exact resolve eq1030 eq480536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1030 eq480536
  have eq480904 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq480651
       grind)
    | exact superpose eq480651 eq16
    | exact resolve eq16 eq480651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq481263 : y = (M.op x (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq31861 x y y
       have i₂ := eq480544
       grind)
    | exact superpose eq480544 eq31861
    | exact resolve eq31861 eq480544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31861 eq480544
  have eq481639 : y = (M.op x (M.op x x)) := by
    first
    | (have i₁ := eq481263
       have i₂ := eq480651
       grind)
    | exact superpose eq480651 eq481263
    | exact resolve eq481263 eq480651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480651 eq481263
  have eq940769 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 (M.op X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq134037 eq133878
    | (have j0 := eq133878 X0
       have j1 := eq134037 X0
       grind)
    | exact resolve eq133878 eq134037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133878 eq134037
  have eq942232 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq940769 x
       have i₂ := eq481639
       grind)
    | exact superpose eq481639 eq940769
    | (have j0 := eq940769 x
       grind)
    | exact resolve eq940769 eq481639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq940769
  have eq942686 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq942232
       have r₂ := eq480904
       grind)
    | exact resolve eq942232 eq480904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq942232
  have eq943320 : (τ (M.op (σ x) (σ x))) = (k (τ (σ x)) x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq65 x
       have i₂ := eq942686
       grind)
    | exact superpose eq942686 eq65
    | exact resolve eq65 eq942686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq943905 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq943320
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq943320
    | exact resolve eq943320 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq943320
  have eq943968 : (τ (σ x)) = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq942686 eq943905
    | exact resolve eq943905 eq942686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq942686 eq943905
  have eq943987 : x = (k x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq943968
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq943968
    | exact resolve eq943968 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq943968
  have eq943994 : x = (M.op x x) := by
    first
    | (have j1 := eq59863 x
       grind)
    | (have r₁ := eq943987
       have r₂ := eq59863 x
       grind)
    | exact resolve eq943987 eq59863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59863 eq943987
  have eq943996 : y = (M.op x x) := by
    first
    | (have i₁ := eq481639
       have i₂ := eq943994
       grind)
    | exact superpose eq943994 eq481639
    | exact resolve eq481639 eq943994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481639
  have eq944087 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq27894 x
       have i₂ := eq943994
       grind)
    | exact superpose eq943994 eq27894
    | (have j0 := eq27894 x
       grind)
    | exact resolve eq27894 eq943994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27894
  have eq944634 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq944087
       have i₂ := eq943994
       grind)
    | exact superpose eq943994 eq944087
    | exact resolve eq944087 eq943994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq944087
  have eq944635 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq944634
  have eq944685 : x = y := by
    first
    | (have i₁ := eq943996
       have i₂ := eq943994
       grind)
    | exact superpose eq943994 eq943996
    | exact resolve eq943996 eq943994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq943994 eq943996
  have eq944841 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq480904
       have i₂ := eq944685
       grind)
    | exact superpose eq944685 eq480904
    | exact resolve eq480904 eq944685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480904 eq944685
  have eq944931 : False := by grind
  exact eq944931

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = m(X,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pxy_pyx_pxx_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq30 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op (M.op X0 X2) (M.op X1 X1)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30 X1 (M.op (M.op X2 X1) (M.op X0 X0))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq30
    | exact resolve eq30 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 X0
       have i₂ := eq30 X0 X0
       grind)
    | exact superpose eq30 eq9
    | exact resolve eq9 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 (M.op X0 X0)) X0
       have i₂ := eq57 X0
       grind)
    | exact superpose eq57 eq9
    | exact resolve eq9 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq130 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq133 : ∀ X1 X3 : G, (M.op X3 X3) = (M.op (M.op X1 (M.op X3 X3)) X3) := by
    intro X1 X3
    first
    | (have i₁ := eq55 x X3 (M.op (M.op x x) (M.op X1 X1))
       have i₂ := eq9 X1 x x
       grind)
    | exact superpose eq9 eq55
    | exact resolve eq55 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq175 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq130 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq130 X0 X1
       grind)
    | exact superpose eq130 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq130 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq130 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq130 X1 X1
       grind)
    | exact resolve eq13 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) (M.op X2 X2))) = X2 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1 X0
       have i₂ := eq130 X0 X1
       grind)
    | (have i₁ := eq9 X0 X0 X0
       have i₂ := eq130 X0 X1
       grind)
    | exact superpose eq130 eq9
    | (have j1 := eq130 X0 X1
       grind)
    | exact resolve eq9 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq181 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq175 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq184 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq181 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq181 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq181 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq200 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq133 X1 (M.op X1 (M.op X1 X1))
       have i₂ := eq63 X1 X1
       grind)
    | exact superpose eq63 eq133
    | exact resolve eq133 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq133
  have eq264 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq184 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq659 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X3 (M.op (M.op X2 X2) (M.op X1 (M.op X0 X1)))) ∨ (M.op X3 X2) = (k X2 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq177 X2 X3 (M.op X0 X1)
       have i₂ := eq30 X0 X1
       grind)
    | exact superpose eq30 eq177
    | (have j0 := eq177 X2 X3 X2
       grind)
    | exact resolve eq177 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq177
  have eq11007 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq659 X0 X0 X0 X1
       have i₂ := eq200 X0 X0
       grind)
    | exact superpose eq200 eq659
    | (have j0 := eq659 X0 X1 X0 X1
       grind)
    | exact resolve eq659 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200 eq659
  have eq11145 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq11007 X0 X1
       have j1 := eq264 X0 X1
       grind)
    | (have r₁ := eq11007 X0 X1
       have r₂ := eq264 X0 X1
       grind)
    | (have r₁ := eq11007 X0 X0
       have r₂ := eq264 X0 X0
       grind)
    | exact resolve eq11007 eq264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264 eq11007
  have eq11268 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq11145 (σ X0) (σ X1)
       grind)
    | exact superpose eq11145 eq15
    | exact resolve eq15 eq11145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11278 : ∀ X0 X1 : G, (σ (M.op X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11268 X0 X1
       have i₂ := eq11145 X0 X1
       grind)
    | exact superpose eq11145 eq11268
    | exact resolve eq11268 eq11145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11145 eq11268
  have eq11396 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11278 y x
       grind)
    | exact superpose eq11278 eq16
    | (have r₁ := eq16
       have r₂ := eq11278 y x
       grind)
    | exact resolve eq16 eq11278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11278
  have eq11436 : False := by grind
  exact eq11436

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyy_pyx_pxx_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq41 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq41 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq41 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq41 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq55 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 (M.op X1 X1) X1
       have r₂ := eq12 X0 (M.op X1 X1)
       grind)
    | (have r₁ := eq14 X0 (M.op X0 X0)
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq55
    | (have j0 := eq55 (σ X0) (σ X1)
       grind)
    | exact resolve eq55 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq42 (τ X0)
       grind)
    | exact superpose eq42 eq18
    | exact resolve eq18 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq82 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq81 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq81
    | exact resolve eq81 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq90 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq82 X0
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq82
    | exact resolve eq82 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq82
  have eq94 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq90 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq90
    | exact resolve eq90 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq90 X0
       grind)
    | exact superpose eq90 eq10
    | exact resolve eq10 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq167 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq66 y x
       grind)
    | exact superpose eq66 eq16
    | (have j1 := eq66 y x
       grind)
    | exact resolve eq16 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq224 : ∀ X0 X1 : G, (M.op (τ X0) (M.op (τ (M.op X0 X0)) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (τ X0) (τ X0)
       have i₂ := eq101 X0
       grind)
    | exact superpose eq101 eq9
    | exact resolve eq9 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq562 : (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq167
       have i₂ := eq94 x
       grind)
    | exact superpose eq94 eq167
    | exact resolve eq167 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq563 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq562
       have i₂ := eq94 y
       grind)
    | exact superpose eq94 eq562
    | exact resolve eq562 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq596 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq563
       have i₂ := eq55 y x
       grind)
    | exact superpose eq55 eq563
    | (have j1 := eq55 x y
       grind)
    | exact resolve eq563 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq563
  have eq597 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq596
  have eq7356 : (M.op y y) = (τ (σ (M.op x x))) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq597
       grind)
    | exact superpose eq597 eq10
    | exact resolve eq10 eq597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597
  have eq7403 : (M.op x x) = (M.op y y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq7356
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq7356
    | exact resolve eq7356 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7356
  have eq7404 : (M.op x x) = (M.op y y) := by grind
  clear eq7403
  have eq7433 : ∀ X0 : G, y = (M.op (τ X0) (M.op (τ (M.op X0 X0)) (M.op x x))) := by
    intro X0
    first
    | (have i₁ := eq224 X0 y
       have i₂ := eq7404
       grind)
    | exact superpose eq7404 eq224
    | exact resolve eq224 eq7404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7404
  have eq7510 : x = y := by
    first
    | (have i₁ := eq7433 x
       have i₂ := eq224 x x
       grind)
    | exact superpose eq224 eq7433
    | exact resolve eq7433 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224 eq7433
  have eq7578 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7510
       grind)
    | exact superpose eq7510 eq16
    | exact resolve eq16 eq7510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7510
  have eq7579 : False := by grind
  exact eq7579

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyy_x_pyx_pyy_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
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
  clear eq37
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
  clear eq45
  have eq115 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq48 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq48
    | (have j0 := eq48 x
       grind)
    | exact resolve eq48 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
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
  have eq175 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 y x
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
       have i₂ := eq16 X0 X2 X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq16 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq176 (M.op sF4 sF4)
       have i₂ := eq16 sF4 sF4 sF4
       grind)
    | exact superpose eq16 eq176
    | exact resolve eq176 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (M.op X1 X0) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq182 eq16
    | exact resolve eq16 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq570 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (k X0 X0))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq176 X0
       have i₂ := eq28 X0 X0
       grind)
    | exact superpose eq28 eq176
    | (have j1 := eq28 X0 X0
       grind)
    | exact resolve eq176 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq572 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 := by
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
  have eq579 : (M.op x y) = (k y x) ∨ y = (M.op x x) := by
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
  have eq580 : ∀ X0 : G, (k (M.op (M.op x y) (M.op X0 X0)) y) = X0 ∨ (M.op (M.op x y) (M.op X0 X0)) = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq175 X0
       have i₂ := eq28 (M.op sF0 (M.op X0 X0)) y
       grind)
    | exact superpose eq28 eq175
    | (have j1 := eq28 (M.op (M.op x y) (M.op X0 X0)) y
       grind)
    | exact resolve eq175 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq585 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
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
  have eq596 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq601 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq572 X0 X1
       have j1 := eq13 X1 X0
       grind)
    | (have r₁ := eq572 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq572 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572
  have eq603 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq579
       grind)
    | exact superpose eq579 eq40
    | exact resolve eq40 eq579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq604 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq603
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq603
    | exact resolve eq603 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603
  have eq606 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq604
    | exact resolve eq604 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604
  have eq616 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq606 eq585
    | exact resolve eq585 eq606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq623 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq616
       have r₂ := eq27
       grind)
    | exact resolve eq616 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616
  have eq627 : (σ y) = (k (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq623
       have i₂ := eq28 sF2 sF2
       grind)
    | exact superpose eq28 eq623
    | (have j1 := eq28 y x
       grind)
    | exact resolve eq623 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq630 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) (M.op X0 X0))) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq623 eq16
    | exact resolve eq16 eq623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq631 : (σ x) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq623 eq176
    | exact resolve eq176 eq623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq632 : (σ x) = (M.op y (M.op (M.op x y) (σ y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq623 eq175
    | exact resolve eq175 eq623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq656 : ∀ X0 : G, (σ y) ≠ X0 ∨ (σ x) = (σ y) ∨ (σ y) = (k X0 (σ x)) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq623 eq12
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq623
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq623
       grind)
    | exact resolve eq12 eq623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq658 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq12 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq659 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq28 eq658
    | (have j0 := eq658 X0
       have j1 := eq28 X0 X0
       grind)
    | exact resolve eq658 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq661 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq601 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq601
    | (have j0 := eq601 (σ X0) X1
       grind)
    | exact resolve eq601 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601
  have eq681 : (σ x) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq623 eq630
    | exact resolve eq630 eq623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623
  have eq683 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq630 (M.op sF3 sF3)
       have i₂ := eq16 sF3 sF3 sF3
       grind)
    | exact superpose eq16 eq630
    | exact resolve eq630 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq689 : (σ x) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ y = (M.op x x) := by grind
  clear eq681
  have eq692 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26 eq683
    | exact resolve eq683 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683
  have eq697 : (σ y) = (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq692 eq630
    | exact resolve eq630 eq692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq699 : (σ y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq692 eq176
    | exact resolve eq176 eq692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq702 : ∀ X0 X1 : G, (σ y) = (M.op X0 (M.op (M.op X1 X0) (M.op (σ x) (σ y)))) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq692 eq16
    | exact resolve eq16 eq692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq703 : (σ y) = (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ y = (M.op x x) := by grind
  clear eq697
  have eq704 : (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq182 eq699
    | exact resolve eq699 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699
  have eq709 : (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (σ y)) (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y))))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq689 eq188
    | exact resolve eq188 eq689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq710 : ∀ X0 : G, (M.op (M.op (σ y) (σ y)) (M.op (σ x) (M.op X0 X0))) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq689 eq16
    | exact resolve eq16 eq689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689
  have eq712 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op X0 X0))) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq692 eq710
    | exact resolve eq710 eq692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710
  have eq713 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y))))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq692 eq709
    | exact resolve eq709 eq692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692 eq709
  have eq717 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq703 eq713
    | exact resolve eq713 eq703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703 eq713
  have eq730 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq717 eq631
    | exact resolve eq631 eq717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631 eq717
  have eq734 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x x) := by grind
  clear eq730
  have eq742 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (M.op X1 X0) (σ x))) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq734 eq188
    | exact resolve eq188 eq734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq772 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq734 eq704
    | exact resolve eq704 eq734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704
  have eq780 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq772
  have eq1120 : ∀ X0 X1 : G, (M.op X0 (k X0 X1)) = (M.op (k X0 X1) (k X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq178 X1 X0
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq178
    | (have j1 := eq28 (M.op X0 (k X0 X1)) (k X0 X1)
       grind)
    | exact resolve eq178 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1157 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 X0 X0
       have i₂ := eq178 X0 X0
       grind)
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1161 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq176 (M.op X1 X0)
       have i₂ := eq178 X1 X0
       grind)
    | exact superpose eq178 eq176
    | exact resolve eq176 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1162 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op y (M.op (M.op x y) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq175 (M.op X1 X0)
       have i₂ := eq178 X1 X0
       grind)
    | exact superpose eq178 eq175
    | exact resolve eq175 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1163 : ∀ X0 X1 X2 : G, (M.op X1 X0) ≠ (M.op X0 (M.op X1 X0)) ∨ (k X2 (M.op X1 X0)) = (M.op (M.op X1 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op X1 X0)
       have i₂ := eq178 X1 X0
       grind)
    | exact superpose eq178 eq13
    | (have j0 := eq13 X2 (M.op X1 X0)
       grind)
    | exact resolve eq13 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1164 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op X1 X0) X2 X3
       have i₂ := eq178 X1 X0
       grind)
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1167 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (k (M.op X1 X0) (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq178 X0 X1
       grind)
    | exact superpose eq178 eq28
    | exact resolve eq28 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1695 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (M.op X0 X1) (M.op (σ y) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq188 eq702
    | exact resolve eq702 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188 eq702
  have eq1845 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (M.op X0 X1) (M.op (σ y) (M.op (σ x) (σ y)))) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq182 eq1695
    | exact resolve eq1695 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1695
  have eq1857 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (M.op X0 X1) (σ x)) (σ x)) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq734 eq1845
    | exact resolve eq1845 eq734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734 eq1845
  have eq2642 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq712 eq1857
    | exact resolve eq1857 eq712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712 eq1857
  have eq2692 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (σ x)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq2642 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2642
  have eq3347 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq627 eq659
    | (have j0 := eq659 (σ x)
       grind)
    | exact resolve eq659 eq627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq627 eq659
  have eq3351 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq3347
  have eq3352 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq606 eq3351
    | exact resolve eq3351 eq606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3351
  have eq3425 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X0 X1)) (M.op (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) (M.op X4 X4))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq177 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) X2 X3 X4
       have i₂ := eq177 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq177 eq177
    | exact resolve eq177 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3434 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq177 X4 X2 X3 (M.op X1 X0)
       have i₂ := eq178 X1 X0
       grind)
    | exact superpose eq178 eq177
    | exact resolve eq177 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3435 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq177 X4 X2 X3 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq177 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq177 eq177
    | exact resolve eq177 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3451 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) X2 X3
       have i₂ := eq177 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3452 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq175 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq177 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq177 eq175
    | exact resolve eq175 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3453 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq176 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq177 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq177 eq176
    | exact resolve eq176 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3456 : ∀ X0 X1 X4 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 (M.op X4 X4))) = X4 := by
    intro X0 X1 X4
    first
    | (have i₁ := eq16 X4 (M.op X1 (M.op X0 X0)) (M.op (M.op x x) (M.op X1 X1))
       have i₂ := eq177 X1 x x X0
       grind)
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3458 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq178 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
       have i₂ := eq177 X0 x x X3
       grind)
    | exact superpose eq177 eq178
    | exact resolve eq178 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3475 : ∀ X0 X1 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3453 X0 X1
       have i₂ := eq178 X0 X1
       grind)
    | exact superpose eq178 eq3453
    | exact resolve eq3453 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3453
  have eq3476 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3452 X0 X1
       have i₂ := eq178 X0 X1
       grind)
    | exact superpose eq178 eq3452
    | exact resolve eq3452 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3452
  have eq3477 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3451 X0 X1 X2 X3
       have i₂ := eq178 X0 X1
       grind)
    | exact superpose eq178 eq3451
    | exact resolve eq3451 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3451
  have eq3486 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq3435 X0 X1 X2 X3 X4
       have i₂ := eq178 X0 X1
       grind)
    | exact superpose eq178 eq3435
    | exact resolve eq3435 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3435
  have eq3488 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X0 X1)) (M.op (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) (M.op X4 X4))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq3425 X0 X1 X2 X3 X4
       have i₂ := eq178 X0 X1
       grind)
    | exact superpose eq178 eq3425
    | exact resolve eq3425 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3425
  have eq3489 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X0 X1))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3476 X0 X1
       have i₂ := eq3475 X0 X1
       grind)
    | exact superpose eq3475 eq3476
    | exact resolve eq3476 eq3475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3476
  have eq3490 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3477 X0 X1 X2 X3
       have i₂ := eq3475 X0 X1
       grind)
    | exact superpose eq3475 eq3477
    | exact resolve eq3477 eq3475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3477
  have eq3496 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 X1))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq3486 X0 X1 X2 X3 X4
       have i₂ := eq3475 X0 X1
       grind)
    | exact superpose eq3475 eq3486
    | exact resolve eq3486 eq3475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3486
  have eq3497 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X0 X1)) (M.op (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) (M.op X4 X4))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq3488 X0 X1 X2 X3 X4
       have i₂ := eq3475 X0 X1
       grind)
    | exact superpose eq3475 eq3488
    | exact resolve eq3488 eq3475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3488
  have eq3559 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq3352 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq3352
       grind)
    | exact resolve eq13 eq3352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3566 : (σ x) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq3352 eq630
    | exact resolve eq630 eq3352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3352
  have eq3596 : (σ x) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq3566
  have eq3597 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq3559 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3559
  have eq3608 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq780 eq3596
    | exact resolve eq3596 eq780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780 eq3596
  have eq3611 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq3608
    | exact resolve eq3608 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3608
  have eq3631 : ∀ X0 X1 : G, x = (M.op X0 (M.op (M.op X1 X0) y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 x X0 X1
       have i₂ := eq3611
       grind)
    | exact superpose eq3611 eq16
    | exact resolve eq16 eq3611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3611
  have eq4940 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (M.op (M.op X0 (σ x)) (σ x)) (σ x)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq3597 eq742
    | exact resolve eq742 eq3597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742 eq3597
  have eq4966 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (M.op (M.op X0 (σ x)) (σ x)) (σ x)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq4940 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4940
  have eq5018 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2692 eq4966
    | exact resolve eq4966 eq2692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2692 eq4966
  have eq5064 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq606 eq5018
    | exact resolve eq5018 eq606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606 eq5018
  have eq5094 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq5064
       have r₂ := eq27
       grind)
    | exact resolve eq5064 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5064
  have eq5110 : ∀ X0 : G, y ≠ X0 ∨ x = y ∨ y = (k X0 x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq5094
       grind)
    | exact superpose eq5094 eq12
    | (have r₁ := eq12 y x
       have r₂ := eq5094
       grind)
    | exact resolve eq12 eq5094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5112 : ∀ X0 X1 : G, x = (M.op X0 (M.op (M.op X1 X0) y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 x X0 X1
       have i₂ := eq5094
       grind)
    | exact superpose eq5094 eq16
    | exact resolve eq16 eq5094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5114 : x = (M.op (σ y) (M.op (M.op (σ x) (σ y)) y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq176 x
       have i₂ := eq5094
       grind)
    | exact superpose eq5094 eq176
    | exact resolve eq176 eq5094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5119 : ∀ X0 : G, (M.op x (M.op y (M.op X0 X0))) = X0 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq16 X0 x x
       have i₂ := eq5094
       grind)
    | exact superpose eq5094 eq16
    | exact resolve eq16 eq5094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5120 : y = (k x x) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq28 x x
       have i₂ := eq5094
       grind)
    | exact superpose eq5094 eq28
    | exact resolve eq28 eq5094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5122 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq178 x x
       have i₂ := eq5094
       grind)
    | exact superpose eq5094 eq178
    | exact resolve eq178 eq5094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5127 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq5122
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq5122
    | exact resolve eq5122 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5122
  have eq5128 : (M.op x y) = (k y y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq5127
       have i₂ := eq28 y y
       grind)
    | exact superpose eq28 eq5127
    | (have j1 := eq28 y y
       grind)
    | exact resolve eq5127 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5131 : ∀ X0 X1 : G, y = (M.op X0 (M.op (M.op X1 X0) (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 y X0 X1
       have i₂ := eq5127
       grind)
    | exact superpose eq5127 eq16
    | exact resolve eq16 eq5127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5133 : y = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq176 y
       have i₂ := eq5127
       grind)
    | exact superpose eq5127 eq176
    | exact resolve eq176 eq5127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5141 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq28 y y
       have i₂ := eq5127
       grind)
    | exact superpose eq5127 eq28
    | exact resolve eq28 eq5127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5160 : (M.op x y) = (k y y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq5141 eq5128
    | exact resolve eq5128 eq5141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5128
  have eq5241 : (M.op y y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq5133 eq178
    | exact resolve eq178 eq5133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5257 : (M.op x y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq5127 eq5241
    | exact resolve eq5241 eq5127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5241
  have eq5540 : x = (M.op x (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1157 x
       have i₂ := eq5094
       grind)
    | exact superpose eq5094 eq1157
    | exact resolve eq1157 eq5094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5587 : x = (M.op x (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq5540
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq5540
    | exact resolve eq5540 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5540
  have eq5595 : ∀ X0 : G, (M.op (M.op x y) (M.op x (M.op X0 X0))) = X0 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq5587 eq16
    | exact resolve eq16 eq5587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5598 : (M.op x x) = (M.op (M.op x y) x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq5587 eq178
    | exact resolve eq178 eq5587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5587
  have eq5615 : y = (M.op (M.op x y) x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq5094 eq5598
    | exact resolve eq5598 eq5094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5094 eq5598
  have eq5764 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq5120
       grind)
    | exact superpose eq5120 eq40
    | exact resolve eq40 eq5120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5120
  have eq5771 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq5764
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5764
    | exact resolve eq5764 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5764
  have eq5773 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq5771
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq5771
    | exact resolve eq5771 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5771
  have eq5868 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq5141
       grind)
    | exact superpose eq5141 eq41
    | exact resolve eq41 eq5141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5141
  have eq5877 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq5868
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq5868
    | exact resolve eq5868 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5868
  have eq5879 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq5877
    | exact resolve eq5877 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5877
  have eq5888 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq5773 eq596
    | (have j0 := eq596 (σ x)
       grind)
    | exact resolve eq596 eq5773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6023 : x = (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) (M.op y y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq5133 eq5112
    | exact resolve eq5112 eq5133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5133
  have eq6042 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq5257 eq5112
    | exact resolve eq5112 eq5257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5257
  have eq6073 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq6042
  have eq6080 : x = (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) (M.op y y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq6023
  have eq6122 : x = (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq5127 eq6080
    | exact resolve eq6080 eq5127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5127 eq6080
  have eq6151 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq6073
       have i₂ := eq28 sF0 sF0
       grind)
    | exact superpose eq28 eq6073
    | (have j1 := eq28 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq6073 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6160 : ∀ X0 X1 : G, (M.op x y) = (M.op X0 (M.op (M.op X1 X0) x)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq6073 eq16
    | exact resolve eq16 eq6073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6162 : (M.op x y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq6073 eq176
    | exact resolve eq176 eq6073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6171 : (M.op x y) = (M.op (M.op x y) (M.op (M.op x y) x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq6073 eq1157
    | exact resolve eq1157 eq6073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6202 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq5615 eq6171
    | exact resolve eq6171 eq5615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5615 eq6171
  have eq7213 : ∀ X0 : G, y = (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) (M.op X0 (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq176 eq5131
    | exact resolve eq5131 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5131
  have eq7479 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (M.op x y) (M.op x (M.op X0 X1))) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq5595 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq177 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq177 eq5595
    | exact resolve eq5595 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5595
  have eq7547 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) = (M.op (M.op x y) (M.op x (M.op X0 X1))) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq7479 X0 X1
       have i₂ := eq178 X0 X1
       grind)
    | exact superpose eq178 eq7479
    | exact resolve eq7479 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7479
  have eq7548 : ∀ X0 X1 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) = (M.op (M.op x y) (M.op x (M.op X0 X1))) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq7547 X0 X1
       have i₂ := eq3475 X0 X1
       grind)
    | exact superpose eq3475 eq7547
    | exact resolve eq7547 eq3475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7547
  have eq8880 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op X1 (M.op X0 X0)) (M.op X0 x)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq6160 (M.op X1 (M.op X0 X0)) (M.op (M.op x x) (M.op X1 X1))
       have i₂ := eq177 X1 x x X0
       grind)
    | exact superpose eq177 eq6160
    | exact resolve eq6160 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10612 : (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op x y))) := by
    first
    | exact superpose eq180 eq176
    | exact resolve eq176 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq11449 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq5160
       grind)
    | exact superpose eq5160 eq41
    | exact resolve eq41 eq5160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5160
  have eq11461 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq11449
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq11449
    | exact resolve eq11449 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11449
  have eq11463 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq20 eq11461
    | exact resolve eq11461 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11461
  have eq12634 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1161 (M.op X0 X0) (M.op X1 (M.op X0 X0))
       have i₂ := eq16 X0 (M.op X0 X0) X1
       grind)
    | exact superpose eq16 eq1161
    | exact resolve eq1161 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12957 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (k X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq6151 eq13
    | (have j0 := eq13 X0 (M.op x y)
       grind)
    | (have r₁ := eq13 X0 (M.op x y)
       have r₂ := eq6151
       grind)
    | exact resolve eq13 eq6151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6151
  have eq13021 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq12957 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12957
  have eq13381 : y = (k y x) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have j0 := eq5110 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5110
  have eq13385 : (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq13381
       grind)
    | exact superpose eq13381 eq40
    | exact resolve eq40 eq13381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13381
  have eq13387 : (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq13385
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq13385
    | exact resolve eq13385 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13385
  have eq13393 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13387 eq585
    | exact resolve eq585 eq13387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585 eq13387
  have eq15373 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq176 (M.op X0 (M.op X0 X0))
       have i₂ := eq3456 X0 X0 X0
       grind)
    | exact superpose eq3456 eq176
    | exact resolve eq176 eq3456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15390 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op x (M.op y X0)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq5119 (M.op X0 (M.op X0 X0))
       have i₂ := eq3456 X0 X0 X0
       grind)
    | exact superpose eq3456 eq5119
    | exact resolve eq5119 eq3456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15751 : ∀ X0 : G, (M.op X0 (M.op x (M.op y X0))) = X0 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq1157 X0
       have i₂ := eq15390 X0
       grind)
    | exact superpose eq15390 eq1157
    | exact resolve eq1157 eq15390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15390
  have eq15973 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq15751 (M.op X0 X0)
       have i₂ := eq5119 X0
       grind)
    | exact superpose eq5119 eq15751
    | exact resolve eq15751 eq5119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5119 eq15751
  have eq16029 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq15973 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15973
  have eq21370 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13393 eq178
    | exact resolve eq178 eq13393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13393
  have eq21435 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq21370
    | exact resolve eq21370 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21370
  have eq25501 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq21435 eq28
    | exact resolve eq28 eq21435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21435
  have eq25543 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq25501
  have eq25940 : ∀ X0 X1 X2 : G, (M.op x y) = (M.op (M.op X2 (M.op X0 X1)) (M.op (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) x)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8880 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) X2
       have i₂ := eq177 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq177 eq8880
    | exact resolve eq8880 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq8880
  have eq26266 : ∀ X0 X1 X2 : G, (M.op x y) = (M.op (M.op X2 (M.op X0 X1)) (M.op (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) x)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25940 X0 X1 X2
       have i₂ := eq15373 (M.op X0 X1)
       grind)
    | exact superpose eq15373 eq25940
    | exact resolve eq25940 eq15373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25940
  have eq26287 : ∀ X0 X1 X2 : G, (M.op x y) = (M.op (M.op X2 (M.op X0 X1)) (M.op (M.op (M.op x y) (M.op x (M.op X0 X1))) x)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1 X2
    first
    | exact superpose eq7548 eq26266
    | exact resolve eq26266 eq7548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26266
  have eq29041 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq25543 eq5879
    | exact resolve eq5879 eq25543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5879
  have eq29042 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq25543 eq11463
    | exact resolve eq11463 eq25543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11463 eq25543
  have eq29051 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq29042
  have eq29052 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq29041
  have eq29062 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq29051
       have r₂ := eq27
       grind)
    | exact resolve eq29051 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29051
  have eq29063 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq29052
       have r₂ := eq27
       grind)
    | exact resolve eq29052 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29052
  have eq31615 : y = (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq29062 eq7213
    | exact resolve eq7213 eq29062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7213 eq29062
  have eq31677 : y = (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq31615
  have eq31746 : x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq6122 eq31677
    | exact resolve eq31677 eq6122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6122 eq31677
  have eq31747 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq31746
  have eq31797 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) (M.op X0 X0))) = X0 ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq31747 eq176
    | exact resolve eq176 eq31747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41862 : x = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq13021 eq6073
    | exact resolve eq6073 eq13021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6073 eq13021
  have eq42231 : x = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq41862
  have eq42485 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq42231 eq42
    | exact resolve eq42 eq42231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42490 : x ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq42231 eq596
    | (have j0 := eq596 (M.op x y)
       grind)
    | exact resolve eq596 eq42231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596
  have eq42498 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq42485
    | exact resolve eq42485 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42485
  have eq42500 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq42498
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq42498
    | exact resolve eq42498 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42498
  have eq47976 : (σ x) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq5773 eq570
    | (have j0 := eq570 (σ x)
       grind)
    | exact resolve eq570 eq5773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570
  have eq48038 : (σ x) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq15373 eq47976
    | exact resolve eq47976 eq15373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15373 eq47976
  have eq55032 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have j0 := eq656 (σ y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656
  have eq55041 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq55032 eq142
    | exact resolve eq142 eq55032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq55032
  have eq55045 : y = (k y x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq32 eq55041
    | exact resolve eq55041 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55041
  have eq55048 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq579 eq55045
    | exact resolve eq55045 eq579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579 eq55045
  have eq55083 : x = (M.op (σ y) (M.op (M.op (σ x) (σ y)) y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq176 x
       have i₂ := eq55048
       grind)
    | exact superpose eq55048 eq176
    | exact resolve eq176 eq55048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55127 : ∀ X0 : G, (M.op x (M.op y (M.op X0 X0))) = X0 ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16 X0 x x
       have i₂ := eq55048
       grind)
    | exact superpose eq55048 eq16
    | exact resolve eq16 eq55048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55130 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq178 x x
       have i₂ := eq55048
       grind)
    | exact superpose eq55048 eq178
    | exact resolve eq178 eq55048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55136 : y = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1161 x x
       have i₂ := eq55048
       grind)
    | exact superpose eq55048 eq1161
    | exact resolve eq1161 eq55048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55048
  have eq55165 : y = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq55136
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq55136
    | exact resolve eq55136 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55136
  have eq55167 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq55130
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq55130
    | exact resolve eq55130 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55130
  have eq55207 : y = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10612 eq55165
    | exact resolve eq55165 eq10612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55165
  have eq55301 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq28 y y
       have i₂ := eq55167
       grind)
    | exact superpose eq55167 eq28
    | exact resolve eq28 eq55167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55339 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq55301
  have eq55530 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq55339
       grind)
    | exact superpose eq55339 eq41
    | exact resolve eq41 eq55339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq55339
  have eq55545 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq55530
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq55530
    | exact resolve eq55530 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55530
  have eq55548 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq55545
    | exact resolve eq55545 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55545
  have eq55947 : (M.op (M.op x y) (M.op x y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq55207 eq1161
    | exact resolve eq1161 eq55207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55999 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq55083 eq55947
    | exact resolve eq55947 eq55083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55083 eq55947
  have eq56131 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq55999
       have i₂ := eq28 sF0 sF0
       grind)
    | exact superpose eq28 eq55999
    | (have j1 := eq28 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq55999 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57065 : (M.op x y) = (M.op x (M.op y x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq55999 eq55127
    | exact resolve eq55127 eq55999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55127
  have eq57148 : (M.op x y) = (M.op x (M.op y x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq57065
  have eq57211 : (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op x y))) = (M.op y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1161 x y
       have i₂ := eq57148
       grind)
    | exact superpose eq57148 eq1161
    | exact resolve eq1161 eq57148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57148
  have eq57264 : (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) = (M.op y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10612 eq57211
    | exact resolve eq57211 eq10612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10612 eq57211
  have eq57283 : y = (M.op y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq55207 eq57264
    | exact resolve eq57264 eq55207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57264
  have eq57318 : y = (k x y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq28 x y
       have i₂ := eq57283
       grind)
    | exact superpose eq57283 eq28
    | (have j0 := eq28 x y
       grind)
    | exact resolve eq28 eq57283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57283
  have eq57369 : y = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq55167 eq57318
    | exact resolve eq57318 eq55167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57318
  have eq69975 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0)) = (M.op X2 (M.op (M.op X3 X2) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1164 (M.op X0 X0) (M.op X1 (M.op X0 X0)) X2 X3
       have i₂ := eq16 X0 (M.op X0 X0) X1
       grind)
    | exact superpose eq16 eq1164
    | exact resolve eq1164 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70053 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X1 X2))) = (M.op X2 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1164 (M.op X0 (M.op X1 X2)) (M.op X1 X2) X2 X1
       have i₂ := eq1164 (M.op X1 X2) X0 (M.op X1 X2) X0
       grind)
    | exact superpose eq1164 eq1164
    | exact resolve eq1164 eq1164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70224 : ∀ X0 X2 X3 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) = (M.op X2 (M.op (M.op X3 X2) X0)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq69975 X0 x X2 X3
       have i₂ := eq12634 X0 x
       grind)
    | exact superpose eq12634 eq69975
    | exact resolve eq69975 eq12634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12634 eq69975
  have eq103102 : ∀ X0 X1 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op X0 X0)))) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | exact superpose eq183 eq3490
    | exact resolve eq3490 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103921 : y = (k (M.op (M.op x y) (M.op x y)) y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq580 y
       have i₂ := eq55167
       grind)
    | exact superpose eq55167 eq580
    | exact resolve eq580 eq55167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580 eq55167
  have eq103990 : y = (k (k (M.op x y) (M.op x y)) y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq103921
    | (have j1 := eq28 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq103921 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103921
  have eq104014 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (k x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq56131 eq103990
    | exact resolve eq103990 eq56131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56131 eq103990
  have eq105148 : y = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ y = (k x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq104014 eq55207
    | exact resolve eq55207 eq104014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55207 eq104014
  have eq105339 : y = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ y = (k x y) := by grind
  clear eq105148
  have eq105359 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ y = (k x y) := by
    first
    | exact superpose eq55999 eq105339
    | exact resolve eq105339 eq55999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55999 eq105339
  have eq105370 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ y = (k x y) := by
    first
    | exact superpose eq57369 eq105359
    | exact resolve eq105359 eq57369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57369 eq105359
  have eq105371 : y = (k x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq105370
  have eq105378 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq105371
       grind)
    | exact superpose eq105371 eq36
    | exact resolve eq36 eq105371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq105371
  have eq105385 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq105378
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq105378
    | exact resolve eq105378 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq105378
  have eq114411 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq5773 eq1120
    | (have j0 := eq1120 (M.op (σ x) (σ y)) (σ y)
       grind)
    | exact resolve eq1120 eq5773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114422 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq105385 eq1120
    | (have j0 := eq1120 (M.op (σ x) (σ y)) (σ y)
       grind)
    | exact resolve eq1120 eq105385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1120 eq105385
  have eq114627 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq114422
    | exact resolve eq114422 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114422
  have eq114638 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq114411
    | exact resolve eq114411 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114411
  have eq114685 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq31747 eq114638
    | exact resolve eq114638 eq31747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114638
  have eq133851 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq114627 eq28
    | (have j0 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq28 eq114627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq114627
  have eq133914 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq55548 eq133851
    | exact resolve eq133851 eq55548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55548 eq133851
  have eq133932 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq133914
       have r₂ := eq27
       grind)
    | exact resolve eq133914 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133914
  have eq134145 : x = (M.op (σ y) (M.op (σ x) y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq133932 eq5112
    | exact resolve eq5112 eq133932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5112
  have eq134155 : (M.op x y) = (M.op (σ y) (M.op (σ x) x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq133932 eq6160
    | exact resolve eq6160 eq133932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6160 eq133932
  have eq134181 : (M.op x y) = (M.op (σ y) (M.op (σ x) x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31747 eq134155
    | exact resolve eq134155 eq31747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134155
  have eq134183 : x = (M.op (σ y) (M.op (σ x) x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29063 eq134145
    | exact resolve eq134145 eq29063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29063 eq134145
  have eq134237 : x = (M.op (σ y) (M.op (σ x) x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31747 eq134183
    | exact resolve eq134183 eq31747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31747 eq134183
  have eq134267 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq134181 eq134237
    | exact resolve eq134237 eq134181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134181 eq134237
  have eq134268 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq134267
  have eq162044 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 X1)) = (M.op (M.op (M.op X2 X3) (M.op X1 X1)) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3434 (M.op X0 X1) X1 X2 X3 X1
       have i₂ := eq1164 X1 X0 X1 X0
       grind)
    | exact superpose eq1164 eq3434
    | exact resolve eq3434 eq1164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq162145 : ∀ X0 X1 X2 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X2 (M.op X1 (M.op X0 X1))))) = (M.op (M.op X2 X2) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3490 X2 (M.op X1 (M.op X0 X1)) (M.op X2 X2) (M.op x x)
       have i₂ := eq3434 X1 X0 x x X2
       grind)
    | exact superpose eq3434 eq3490
    | exact resolve eq3490 eq3434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3434
  have eq227345 : (σ y) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq114685 eq31797
    | exact resolve eq31797 eq114685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31797 eq114685
  have eq227461 : (σ y) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq227345
  have eq227516 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq48038 eq227461
    | exact resolve eq227461 eq48038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48038 eq227461
  have eq227557 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq227516
       have r₂ := eq5888
       grind)
    | exact resolve eq227516 eq5888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5888 eq227516
  have eq227647 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq227557 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq227557
       grind)
    | exact resolve eq13 eq227557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq227696 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq227557 eq3458
    | exact resolve eq3458 eq227557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq227909 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq227647 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227647
  have eq230105 : (k (σ x) (σ x)) = (M.op (k (σ x) (σ x)) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq227909 eq16029
    | exact resolve eq16029 eq227909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq230189 : (σ x) = (M.op (σ x) (k (M.op (σ x) (σ x)) (σ x))) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq227909 eq1157
    | exact resolve eq1157 eq227909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq230534 : (σ x) = (M.op (k (σ x) (σ x)) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq227909 eq227696
    | exact resolve eq227696 eq227909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227696 eq227909
  have eq230608 : (σ x) = (M.op (k (σ x) (σ x)) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq230534
  have eq230851 : (k (σ x) (σ x)) = (M.op (k (σ x) (σ x)) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq230105
  have eq230946 : (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq5773 eq230608
    | exact resolve eq230608 eq5773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230608
  have eq231072 : (σ x) = (M.op (σ x) (k (σ x) (σ x))) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq227557 eq230189
    | exact resolve eq230189 eq227557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227557 eq230189
  have eq231088 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq5773 eq230851
    | exact resolve eq230851 eq5773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230851
  have eq231219 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq5773 eq231072
    | exact resolve eq231072 eq5773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5773 eq231072
  have eq231230 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq230946 eq231088
    | exact resolve eq231088 eq230946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230946 eq231088
  have eq231303 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq231219
    | exact resolve eq231219 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231219
  have eq231423 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq231230 eq32
    | exact resolve eq32 eq231230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231230
  have eq231825 : x = y ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq30 eq231423
    | exact resolve eq231423 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq231423
  have eq231826 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq231825
  have eq235937 : ∀ X0 X1 X2 X3 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op X0 X1))))) = (M.op (M.op (M.op X2 X3) (M.op (σ y) (σ y))) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq1161 eq3496
    | exact resolve eq3496 eq1161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq236260 : ∀ X0 X1 X2 : G, x = (M.op (M.op X2 (M.op X0 X1)) (M.op (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3631 (M.op X2 (M.op X0 X1)) (M.op (M.op x x) (M.op X2 X2))
       have i₂ := eq3496 X0 X1 x x X2
       grind)
    | exact superpose eq3496 eq3631
    | exact resolve eq3631 eq3496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3631
  have eq236305 : ∀ X0 X1 X2 : G, x = (M.op (M.op X2 (M.op X0 X1)) (M.op (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1 X2
    first
    | exact superpose eq231303 eq236260
    | exact resolve eq236260 eq231303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231303 eq236260
  have eq236554 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op X0 X1)) = (M.op (M.op (M.op X2 X3) (M.op (σ y) (σ y))) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq162145 eq235937
    | exact resolve eq235937 eq162145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162145 eq235937
  have eq236902 : ∀ X0 X1 X2 : G, x = (M.op (M.op X2 (M.op X0 X1)) (M.op (M.op (M.op x y) (M.op x (M.op X0 X1))) x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1 X2
    first
    | exact superpose eq7548 eq236305
    | exact resolve eq236305 eq7548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7548 eq236305
  have eq237024 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op X0 X1)) = (M.op (M.op (M.op X2 X3) (M.op (σ y) (σ y))) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq182 eq236554
    | exact resolve eq236554 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236554
  have eq237306 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26287 eq236902
    | exact resolve eq236902 eq26287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26287 eq236902
  have eq238061 : x = (M.op (σ y) (M.op (σ x) y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq237306 eq5114
    | exact resolve eq5114 eq237306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5114
  have eq238086 : (M.op x y) = (M.op (σ y) (M.op (σ x) x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq237306 eq6162
    | exact resolve eq6162 eq237306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6162
  have eq238271 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq237306 eq134268
    | exact resolve eq134268 eq237306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134268 eq237306
  have eq238312 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq238271
  have eq238412 : (M.op x y) = (M.op (σ y) (M.op (σ x) x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq238086
  have eq238437 : x = (M.op (σ y) (M.op (σ x) y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq238061
  have eq238519 : (M.op x y) = (M.op (σ x) (M.op (σ x) x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq238312 eq238412
    | exact resolve eq238412 eq238312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238412
  have eq238535 : x = (M.op (σ y) (M.op (σ x) x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq231826 eq238437
    | exact resolve eq238437 eq231826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238437
  have eq238597 : x = (M.op (σ x) (M.op (σ x) x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq238312 eq238535
    | exact resolve eq238535 eq238312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238312 eq238535
  have eq238630 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq238519 eq238597
    | exact resolve eq238597 eq238519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238519 eq238597
  have eq238631 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq238630
  have eq238654 : (M.op x y) = (τ (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq238631 eq29
    | exact resolve eq29 eq238631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq238705 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32 eq238654
    | exact resolve eq238654 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238654
  have eq238812 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6202
       have i₂ := eq238705
       grind)
    | exact superpose eq238705 eq6202
    | exact resolve eq6202 eq238705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6202 eq238705
  have eq238984 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq238812
       have r₂ := eq42490
       grind)
    | exact resolve eq238812 eq42490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42490 eq238812
  have eq239267 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (k X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq238984 eq13
    | (have j0 := eq13 X0 (M.op x y)
       grind)
    | (have r₁ := eq13 X0 (M.op x y)
       have r₂ := eq238984
       grind)
    | exact resolve eq13 eq238984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq239530 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq239267 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239267
  have eq242004 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq239530 eq238984
    | exact resolve eq238984 eq239530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238984 eq239530
  have eq242930 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq242004
  have eq244489 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq242930 eq42
    | exact resolve eq42 eq242930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq244498 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k X0 (σ (M.op x y))) = (M.op (σ (M.op x y)) X0) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq242930 eq661
    | (have j0 := eq661 (M.op x y) X0
       grind)
    | exact resolve eq661 eq242930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661 eq242930
  have eq244509 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (M.op (σ (M.op x y)) X0) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq244498 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244498
  have eq244529 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (M.op (σ (M.op x y)) X0) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq20 eq244509
    | (have j0 := eq244509 X0
       grind)
    | exact resolve eq244509 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244509
  have eq244531 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq244489
    | exact resolve eq244489 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244489
  have eq244534 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq42500 eq244531
    | exact resolve eq244531 eq42500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244531
  have eq245523 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq244529 eq16029
    | exact resolve eq16029 eq244529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16029 eq244529
  have eq246278 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq245523
  have eq246651 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq42500 eq246278
    | exact resolve eq246278 eq42500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42500 eq246278
  have eq247032 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq244534 eq246651
    | exact resolve eq246651 eq244534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244534 eq246651
  have eq247925 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq247032 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq247032
       grind)
    | exact resolve eq13 eq247032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247032
  have eq248192 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq247925 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247925
  have eq254267 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq248192 eq26
    | (have j1 := eq248192 (σ y)
       grind)
    | exact resolve eq26 eq248192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248192
  have eq256237 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq254267 eq115
    | exact resolve eq115 eq254267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq254267
  have eq256262 : (k x x) = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq231826 eq256237
    | exact resolve eq256237 eq231826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231826 eq256237
  have eq256268 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq238631 eq256262
    | exact resolve eq256262 eq238631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256262
  have eq256272 : x = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq42231 eq256268
    | exact resolve eq256268 eq42231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42231 eq256268
  have eq256275 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq238631 eq256272
    | exact resolve eq256272 eq238631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238631 eq256272
  have eq256294 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq256275 eq14
    | exact resolve eq14 eq256275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256275
  have eq256313 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq256294
    | exact resolve eq256294 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256294
  have eq256317 : (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq256313
       have r₂ := eq27
       grind)
    | exact resolve eq256313 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256313
  have eq256321 : (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq256317 eq29
    | exact resolve eq29 eq256317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq256379 : y = (M.op x y) := by
    first
    | exact superpose eq256321 eq32
    | exact resolve eq32 eq256321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq256380 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq256321 eq14
    | exact resolve eq14 eq256321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256321
  have eq256389 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq256379
       grind)
    | exact superpose eq256379 eq18
    | exact resolve eq18 eq256379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq256393 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op x y) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq175 X0
       have i₂ := eq256379
       grind)
    | exact superpose eq256379 eq175
    | exact resolve eq175 eq256379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq256399 : (σ x) = (M.op (M.op x y) (M.op (M.op x y) (σ y))) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq632
       have i₂ := eq256379
       grind)
    | exact superpose eq256379 eq632
    | exact resolve eq632 eq256379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632
  have eq256406 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op x y) (M.op (M.op x y) (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1162 X1 X0
       have i₂ := eq256379
       grind)
    | exact superpose eq256379 eq1162
    | exact resolve eq1162 eq256379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1162
  have eq256407 : ∀ X0 X1 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) = (M.op (M.op x y) (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3489 X0 X1
       have i₂ := eq256379
       grind)
    | exact superpose eq256379 eq3489
    | exact resolve eq3489 eq256379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3489
  have eq258553 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op x y) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq256393 (M.op X0 (M.op X0 X0))
       have i₂ := eq3456 X0 X0 X0
       grind)
    | exact superpose eq3456 eq256393
    | exact resolve eq256393 eq3456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256393
  have eq264965 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1157 X0
       have i₂ := eq258553 X0
       grind)
    | (have i₁ := eq1157 (M.op x y)
       have i₂ := eq258553 (M.op x y)
       grind)
    | exact superpose eq258553 eq1157
    | exact resolve eq1157 eq258553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq264978 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (M.op x y) (M.op (M.op x y) X0)))) := by
    intro X0
    first
    | (have i₁ := eq1161 X0 X0
       have i₂ := eq258553 X0
       grind)
    | (have i₁ := eq1161 (M.op x y) (M.op x y)
       have i₂ := eq258553 (M.op x y)
       grind)
    | exact superpose eq258553 eq1161
    | exact resolve eq1161 eq258553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1161
  have eq264984 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = (M.op (M.op X0 X0) (M.op (M.op x y) (M.op (M.op x y) X0))) := by
    intro X0
    first
    | (have i₁ := eq3475 X0 X0
       have i₂ := eq258553 X0
       grind)
    | (have i₁ := eq3475 (M.op x y) (M.op x y)
       have i₂ := eq258553 (M.op x y)
       grind)
    | exact superpose eq258553 eq3475
    | exact resolve eq3475 eq258553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3475
  have eq264992 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op (M.op x y) (M.op (M.op x y) X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3456 X0 X1 X0
       have i₂ := eq258553 X0
       grind)
    | (have i₁ := eq3456 (M.op x y) X1 (M.op x y)
       have i₂ := eq258553 (M.op x y)
       grind)
    | exact superpose eq258553 eq3456
    | exact resolve eq3456 eq258553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq264993 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op (M.op x y) X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3456 X0 X0 X1
       have i₂ := eq258553 X0
       grind)
    | (have i₁ := eq3456 (M.op x y) (M.op x y) x
       have i₂ := eq258553 (M.op x y)
       grind)
    | exact superpose eq258553 eq3456
    | exact resolve eq3456 eq258553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq264994 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op x y) (M.op (M.op x y) X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq3458 X0 X0
       have i₂ := eq258553 X0
       grind)
    | (have i₁ := eq3458 (M.op x y) (M.op x y)
       have i₂ := eq258553 (M.op x y)
       grind)
    | exact superpose eq258553 eq3458
    | exact resolve eq3458 eq258553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3458
  have eq265256 : (σ y) = (M.op (σ x) (M.op (M.op x y) (M.op (M.op x y) (σ y)))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq630 sF3
       have i₂ := eq258553 sF3
       grind)
    | exact superpose eq258553 eq630
    | exact resolve eq630 eq258553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq630
  have eq265274 : ∀ X0 : G, (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq183 sF4 x
       have i₂ := eq258553 sF4
       grind)
    | exact superpose eq258553 eq183
    | exact resolve eq183 eq258553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq265435 : (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (M.op (M.op x y) (M.op (M.op x y) (σ y)))) := by
    first
    | (have i₁ := eq265256
       have i₂ := eq256379
       grind)
    | exact superpose eq256379 eq265256
    | exact resolve eq265256 eq256379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265256
  have eq265510 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op (M.op x y) (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq176 eq264984
    | exact resolve eq264984 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264984
  have eq265514 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op x y) X0)))) := by
    intro X0
    first
    | exact superpose eq256407 eq264978
    | exact resolve eq264978 eq256407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264978
  have eq265573 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq256399 eq265435
    | exact resolve eq265435 eq256399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256399 eq265435
  have eq313779 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X0) (M.op (M.op x y) (M.op (M.op x y) (M.op X0 (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq264992 (M.op X0 (M.op X0 X0)) X1
       have i₂ := eq3456 X0 X0 X0
       grind)
    | exact superpose eq3456 eq264992
    | exact resolve eq264992 eq3456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264992
  have eq314509 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X0) (M.op X0 X0)) := by
    intro X0 X1
    first
    | exact superpose eq256406 eq313779
    | exact resolve eq313779 eq256406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256406 eq313779
  have eq315108 : ∀ X0 X1 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op X0 X0)))) = (M.op (M.op (M.op x y) X1) X0) := by
    intro X0 X1
    first
    | exact superpose eq264993 eq3490
    | exact resolve eq3490 eq264993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq315133 : ∀ X0 X1 X2 X3 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X3 (M.op X0 X0)))) = (M.op (M.op (M.op X1 X2) (M.op (M.op (M.op x y) (M.op (M.op x y) X3)) (M.op (M.op x y) (M.op (M.op x y) X3)))) X0) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq264993 eq3496
    | exact resolve eq3496 eq264993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3496 eq264993
  have eq315416 : ∀ X0 X1 X2 X3 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X3 (M.op X0 X0)))) = (M.op (M.op (M.op X1 X2) (M.op (M.op (M.op x y) X3) (M.op (M.op x y) (M.op (M.op x y) X3)))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq315133 X0 X1 X2 X3
       have i₂ := eq178 sF0 (M.op sF0 X3)
       grind)
    | exact superpose eq178 eq315133
    | exact resolve eq315133 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315133
  have eq315425 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op (M.op x y) (M.op X1 (M.op X0 X0)))) = (M.op (M.op (M.op x y) X1) X0) := by
    intro X0 X1
    first
    | exact superpose eq256407 eq315108
    | exact resolve eq315108 eq256407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315108
  have eq315536 : ∀ X0 X1 X2 X3 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X3 (M.op X0 X0)))) = (M.op (M.op (M.op X1 X2) (M.op X3 (M.op (M.op x y) (M.op (M.op x y) X3)))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq315416 X0 X1 X2 X2
       have i₂ := eq70053 sF0 sF0 X2
       grind)
    | exact superpose eq70053 eq315416
    | exact resolve eq315416 eq70053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70053 eq315416
  have eq315596 : ∀ X0 X1 X2 X3 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X3 (M.op X0 X0)))) = (M.op (M.op (M.op X1 X2) X3) X0) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq264965 eq315536
    | exact resolve eq315536 eq264965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315536
  have eq315623 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X3) X0) = (M.op (M.op x y) (M.op (M.op x y) (M.op X3 (M.op X0 X0)))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq256407 eq315596
    | exact resolve eq315596 eq256407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315596
  have eq315642 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X3) X0) = (M.op (M.op (M.op x y) X3) X0) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq315425 eq315623
    | exact resolve eq315623 eq315425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315623
  have eq325931 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op X0 X0)))) = (M.op (M.op (M.op x y) (M.op (σ x) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq265274 eq3490
    | exact resolve eq3490 eq265274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265274
  have eq326046 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) = (M.op (M.op (M.op x y) (M.op (σ x) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq103102 eq325931
    | exact resolve eq325931 eq103102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325931
  have eq326078 : ∀ X0 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) X0) = (M.op (M.op (M.op x y) (M.op (σ x) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq182 eq326046
    | exact resolve eq326046 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182 eq326046
  have eq327789 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 X0)) = (M.op (M.op (M.op x y) X0) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq265514 eq265514
    | exact resolve eq265514 eq265514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq327952 : ∀ X0 : G, (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op x y) X0)))) (M.op (M.op x y) (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq265510 X0
       have i₂ := eq265514 X0
       grind)
    | exact superpose eq265514 eq265510
    | exact resolve eq265510 eq265514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265510
  have eq328122 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op x y) (M.op X0 X0)))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 X0 X0
       have i₂ := eq265514 (M.op X0 X0)
       grind)
    | exact superpose eq265514 eq16
    | exact resolve eq16 eq265514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265514
  have eq328317 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) (M.op (M.op (M.op x y) (M.op x y)) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq315425 eq328122
    | exact resolve eq328122 eq315425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328122
  have eq328369 : ∀ X0 : G, (M.op (M.op (M.op x y) (M.op (M.op x y) X0)) (M.op (M.op x y) (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq264994 eq327952
    | exact resolve eq327952 eq264994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264994 eq327952
  have eq328423 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 X0)) = (M.op X0 (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq327789 x
       have i₂ := eq178 sF0 x
       grind)
    | exact superpose eq178 eq327789
    | exact resolve eq327789 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327789
  have eq328478 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq328317 X0
       have i₂ := eq70224 X0 sF0 sF0
       grind)
    | exact superpose eq70224 eq328317
    | exact resolve eq328317 eq70224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70224 eq328317
  have eq328506 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) (M.op (M.op x y) (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq328369 X0
       have i₂ := eq178 sF0 (M.op sF0 X0)
       grind)
    | exact superpose eq178 eq328369
    | exact resolve eq328369 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328369
  have eq328578 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op (M.op x y) X0) (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq328423 eq328506
    | exact resolve eq328506 eq328423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328506
  have eq328620 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq328578 x
       have i₂ := eq178 sF0 x
       grind)
    | exact superpose eq178 eq328578
    | exact resolve eq328578 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328578
  have eq328693 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op (σ x) (σ y))) (M.op X0 X0)) = (M.op (M.op (M.op X1 (M.op (σ x) (σ y))) (M.op X0 X0)) (M.op (σ y) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq328478 (M.op (M.op x sF4) (M.op X0 X0))
       have i₂ := eq16 X0 sF4 x
       grind)
    | exact superpose eq16 eq328478
    | exact resolve eq328478 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328478
  have eq329075 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) X0)) = (M.op (M.op X1 (M.op (σ x) (σ y))) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq328693 X1 x
       have i₂ := eq162044 sF3 X1 x sF4
       grind)
    | exact superpose eq162044 eq328693
    | exact resolve eq328693 eq162044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162044 eq328693
  have eq329448 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op x y) X0)) X0) ≠ X0 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | exact superpose eq328620 eq1163
    | exact resolve eq1163 eq328620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1163
  have eq351745 : (M.op (σ y) (M.op (σ y) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq26 eq314509
    | (have j0 := eq314509 (σ y) (σ x)
       grind)
    | exact resolve eq314509 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314509
  have eq352372 : (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) = (M.op (M.op x y) (M.op (M.op x y) (σ y))) := by
    first
    | (have i₁ := eq351745
       have i₂ := eq258553 sF3
       grind)
    | exact superpose eq258553 eq351745
    | exact resolve eq351745 eq258553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258553 eq351745
  have eq353206 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op (σ y) (σ y))) (M.op (M.op (σ y) (M.op (M.op x y) (M.op (M.op x y) (σ y)))) (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | exact superpose eq352372 eq3497
    | exact resolve eq3497 eq352372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3497 eq352372
  have eq353380 : ∀ X2 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (M.op (σ y) (M.op (M.op x y) (M.op (M.op x y) (σ y)))) (M.op X2 X2))) = X2 := by
    intro X2
    first
    | exact superpose eq237024 eq353206
    | exact resolve eq353206 eq237024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237024 eq353206
  have eq353418 : ∀ X2 : G, (M.op (M.op (M.op x y) (M.op (σ x) (σ y))) (M.op (M.op (σ y) (M.op (M.op x y) (M.op (M.op x y) (σ y)))) (M.op X2 X2))) = X2 := by
    intro X2
    first
    | exact superpose eq326078 eq353380
    | exact resolve eq353380 eq326078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326078 eq353380
  have eq353439 : ∀ X2 : G, (M.op (M.op (M.op x y) (M.op (σ x) (σ y))) (M.op (σ y) (M.op X2 X2))) = X2 := by
    intro X2
    first
    | exact superpose eq264965 eq353418
    | exact resolve eq353418 eq264965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264965 eq353418
  have eq353583 : (M.op (σ y) (σ y)) = (M.op (M.op (M.op x y) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | (have i₁ := eq353439 (M.op sF3 sF3)
       have i₂ := eq16 sF3 sF3 sF3
       grind)
    | exact superpose eq16 eq353439
    | exact resolve eq353439 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq353594 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X0 X0)))) := by
    intro X0
    first
    | exact superpose eq353439 eq3490
    | exact resolve eq3490 eq353439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq353725 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (σ y) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq103102 eq353594
    | exact resolve eq353594 eq103102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103102 eq353594
  have eq363252 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op (M.op x y) X1) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq176 eq315642
    | exact resolve eq315642 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq363840 : ∀ X0 : G, (M.op (M.op (σ y) (σ y)) X0) = (M.op (M.op (M.op x y) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq353583 eq315642
    | exact resolve eq315642 eq353583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315642 eq353583
  have eq365450 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (M.op x y) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq353725 eq363840
    | exact resolve eq363840 eq353725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353725 eq363840
  have eq368746 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq363252 X0 X1 X2
       have i₂ := eq363252 sF0 X1 X2
       grind)
    | exact superpose eq363252 eq363252
    | exact resolve eq363252 eq363252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq370360 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X1) = (M.op (M.op X0 (σ y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq365450 x
       have i₂ := eq363252 sF0 sF3 x
       grind)
    | exact superpose eq363252 eq365450
    | exact resolve eq365450 eq363252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365450
  have eq370396 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ y) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq353439 x
       have i₂ := eq363252 sF0 sF4 (M.op sF3 (M.op x x))
       grind)
    | exact superpose eq363252 eq353439
    | exact resolve eq353439 eq363252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq371080 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op (M.op (M.op x y) X1) (M.op (M.op x y) X1))) = (M.op (M.op X0 X1) (M.op (M.op x y) (M.op (M.op x y) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq328423 (M.op X0 X1)
       have i₂ := eq363252 X0 X1 (M.op sF0 (M.op X0 X1))
       grind)
    | exact superpose eq363252 eq328423
    | exact resolve eq328423 eq363252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328423 eq363252
  have eq371501 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op x y) (M.op (M.op x y) X1))) = (M.op (M.op x y) (M.op X1 (M.op (M.op x y) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq371080 X0 X1
       have i₂ := eq178 sF0 X1
       grind)
    | exact superpose eq178 eq371080
    | exact resolve eq371080 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq371080
  have eq372056 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op x y) (M.op (M.op x y) X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq328620 eq371501
    | exact resolve eq371501 eq328620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371501
  have eq387153 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op (M.op x y) (M.op (M.op x y) (M.op X1 (M.op X0 X0))))) := by
    intro X0 X1
    first
    | exact superpose eq183 eq372056
    | exact resolve eq372056 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq387589 : ∀ X0 : G, (M.op (σ y) (M.op X0 X0)) = (M.op X0 (M.op (M.op x y) (M.op (M.op x y) (M.op (σ y) (M.op X0 X0))))) := by
    intro X0
    first
    | exact superpose eq353439 eq372056
    | exact resolve eq372056 eq353439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353439
  have eq388202 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) X0)) = (M.op (M.op x y) (M.op (M.op x y) X0)) := by
    intro X0 X1 X2
    first
    | exact superpose eq372056 eq1164
    | exact resolve eq1164 eq372056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1164 eq372056
  have eq388446 : ∀ X0 : G, (M.op (σ y) (M.op X0 X0)) = (M.op X0 (M.op (M.op (M.op x y) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq315425 eq387589
    | exact resolve eq387589 eq315425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387589
  have eq388557 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op (M.op (M.op x y) X1) X0)) := by
    intro X0 X1
    first
    | exact superpose eq315425 eq387153
    | exact resolve eq387153 eq315425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387153
  have eq388659 : ∀ X0 : G, (M.op (σ y) (M.op X0 X0)) = (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq370360 eq388446
    | exact resolve eq388446 eq370360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370360 eq388446
  have eq388948 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op (σ x) (σ y))) (M.op (σ y) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq370396 X1 (M.op X0 (M.op X0 X0))
       have i₂ := eq3456 X0 X0 X0
       grind)
    | exact superpose eq3456 eq370396
    | exact resolve eq370396 eq3456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3456
  have eq391479 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op (σ x) (σ y))) (M.op X0 (M.op (M.op (σ x) (σ y)) X0))) = X0 := by
    intro X0 X1
    first
    | exact superpose eq388659 eq370396
    | exact resolve eq370396 eq388659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370396 eq388659
  have eq417334 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq329075 eq16
    | exact resolve eq16 eq329075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329075
  have eq503188 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op X3 (M.op X2 X1)) (M.op X0 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq388202 (M.op (M.op X3 (M.op X2 X1)) (M.op X0 X0)) X1 X2
       have i₂ := eq16 X0 (M.op X2 X1) X3
       grind)
    | exact superpose eq16 eq388202
    | exact resolve eq388202 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388202
  have eq504251 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op (M.op x y) (M.op X3 (M.op X2 X1))) X0) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq315425 eq503188
    | exact resolve eq503188 eq315425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503188
  have eq507893 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq388557 X2 X1
       have i₂ := eq368746 sF0 X1 X2 x
       grind)
    | (have i₁ := eq388557 X2 X1
       have i₂ := eq368746 X0 X1 X2 sF0
       grind)
    | exact superpose eq368746 eq388557
    | exact resolve eq388557 eq368746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388557
  have eq530129 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (σ y)) (M.op X0 X0)) (M.op (M.op (M.op X1 (σ y)) (M.op X0 X0)) (M.op (M.op X1 (σ y)) (M.op X0 X0)))) = (M.op (M.op X2 (M.op (σ x) (σ y))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq388948 (M.op (M.op X2 sF3) (M.op X0 X0)) X1
       have i₂ := eq16 X0 sF3 X2
       grind)
    | exact superpose eq16 eq388948
    | exact resolve eq388948 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388948
  have eq531262 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op (σ x) (σ y))) X0) = (M.op (M.op X0 X0) (M.op (M.op (M.op X1 (σ y)) (M.op X0 X0)) (M.op (M.op X1 (σ y)) (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq530129 X0 X1 X2
       have i₂ := eq507893 (M.op X1 sF3) (M.op X0 X0) (M.op (M.op X1 sF3) (M.op X0 X0))
       grind)
    | exact superpose eq507893 eq530129
    | exact resolve eq530129 eq507893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq507893 eq530129
  have eq531689 : ∀ X0 X1 X2 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (M.op X1 (σ y)) (M.op X0 X0)))) = (M.op (M.op X2 (M.op (σ x) (σ y))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq531262 X0 X1 X2
       have i₂ := eq3490 (M.op X1 sF3) (M.op X0 X0) (M.op X0 X0) (M.op X1 sF3)
       grind)
    | exact superpose eq3490 eq531262
    | exact resolve eq531262 eq3490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3490 eq531262
  have eq531950 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op (σ x) (σ y))) X0) = (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op X1 (σ y)) (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq256407 eq531689
    | exact resolve eq531689 eq256407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256407 eq531689
  have eq532115 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op (σ x) (σ y))) X0) = (M.op (M.op (M.op x y) (M.op X1 (σ y))) X0) := by
    intro X0 X1 X2
    first
    | exact superpose eq315425 eq531950
    | exact resolve eq531950 eq315425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315425 eq531950
  have eq558904 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X1) = (M.op (M.op X2 (M.op X3 (M.op X4 X0))) X1) := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq504251 eq368746
    | exact resolve eq368746 eq504251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368746
  have eq558947 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X3 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq504251 eq16
    | exact resolve eq16 eq504251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq504251
  have eq598757 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op X0 (σ y))) (M.op X1 (M.op (M.op (σ x) (σ y)) X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq532115 eq391479
    | exact resolve eq391479 eq532115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391479 eq532115
  have eq623516 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op x y) X0)) X1) = (M.op (M.op X2 (M.op X3 X0)) X1) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq328620 eq558904
    | exact resolve eq558904 eq328620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328620
  have eq623741 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (σ y) X0)) X1) = (M.op (M.op X2 (M.op X3 X0)) X1) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq417334 eq558904
    | exact resolve eq558904 eq417334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417334 eq558904
  have eq629216 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq558947 X0 (M.op X0 X0) X1 X2
       have i₂ := eq16 X0 X0 X0
       grind)
    | exact superpose eq16 eq558947
    | exact resolve eq558947 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558947
  have eq651028 : ∀ X0 : G, (k X0 X0) = (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) X0) ∨ (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq598757 eq1167
    | exact resolve eq1167 eq598757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1167 eq598757
  have eq651157 : ∀ X0 : G, (k X0 X0) = (M.op (M.op X0 (M.op (σ y) X0)) X0) ∨ (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq651028 x
       have i₂ := eq623741 x x x sF4
       grind)
    | exact superpose eq623741 eq651028
    | (have j0 := eq651028 X0
       grind)
    | exact resolve eq651028 eq623741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651028
  have eq651297 : ∀ X0 : G, (k X0 X0) = (M.op (M.op X0 (M.op (M.op x y) X0)) X0) ∨ (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq651157 x
       have i₂ := eq623516 x x x sF3
       grind)
    | exact superpose eq623516 eq651157
    | (have j0 := eq651157 X0
       grind)
    | exact resolve eq651157 eq623516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651157
  have eq651400 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq651297 X0
       have i₂ := eq629216 X0 X0 sF0
       grind)
    | exact superpose eq629216 eq651297
    | (have j0 := eq651297 X0
       grind)
    | exact resolve eq651297 eq629216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629216 eq651297
  have eq651453 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ y) X0)) X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq651400 x
       have i₂ := eq623741 x x x sF4
       grind)
    | exact superpose eq623741 eq651400
    | (have j0 := eq651400 X0
       grind)
    | exact resolve eq651400 eq623741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623741 eq651400
  have eq651486 : ∀ X0 : G, (M.op (M.op X0 (M.op (M.op x y) X0)) X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq651453 x
       have i₂ := eq623516 x x x sF3
       grind)
    | exact superpose eq623516 eq651453
    | (have j0 := eq651453 X0
       grind)
    | exact resolve eq651453 eq623516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623516 eq651453
  have eq651509 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq651486 X0
       have j1 := eq329448 X0 X0
       grind)
    | (have r₁ := eq651486 X0
       have r₂ := eq329448 X0 x
       grind)
    | exact resolve eq651486 eq329448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329448 eq651486
  have eq651741 : ∀ X0 : G, (M.op X0 (M.op X0 (k X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1157 X0
       have i₂ := eq651509 X0
       grind)
    | exact superpose eq651509 eq1157
    | exact resolve eq1157 eq651509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1157
  have eq652875 : (σ y) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq265573
       have i₂ := eq651509 sF2
       grind)
    | exact superpose eq651509 eq265573
    | exact resolve eq265573 eq651509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265573
  have eq653037 : (σ y) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq652875
       have i₂ := eq651509 x
       grind)
    | exact superpose eq651509 eq652875
    | exact resolve eq652875 eq651509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652875
  have eq682030 : (τ (σ y)) = (k x x) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq653037 eq98
    | exact resolve eq98 eq653037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq653037
  have eq682115 : y = (k x x) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq32 eq682030
    | exact resolve eq682030 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq682030
  have eq682142 : (M.op x y) = (k x x) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq682115
       have i₂ := eq256379
       grind)
    | exact superpose eq256379 eq682115
    | exact resolve eq682115 eq256379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256379 eq682115
  have eq682143 : (M.op x y) = (k x x) := by grind
  clear eq682142
  have eq682190 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq682143
       grind)
    | exact superpose eq682143 eq40
    | exact resolve eq40 eq682143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq682216 : x = (M.op x (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq651741 x
       have i₂ := eq682143
       grind)
    | exact superpose eq682143 eq651741
    | exact resolve eq651741 eq682143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651741 eq682143
  have eq682244 : x = (M.op x (M.op x y)) := by
    first
    | exact superpose eq256389 eq682216
    | exact resolve eq682216 eq256389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682216
  have eq682269 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq682190
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq682190
    | exact resolve eq682190 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682190
  have eq682280 : x = (M.op x y) := by
    first
    | exact superpose eq256389 eq682244
    | exact resolve eq682244 eq256389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256389 eq682244
  have eq682305 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq20 eq682269
    | exact resolve eq682269 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682269
  have eq682330 : (σ y) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq256317 eq682305
    | exact resolve eq682305 eq256317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256317 eq682305
  have eq682381 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq682280
       grind)
    | exact superpose eq682280 eq22
    | exact resolve eq22 eq682280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq682280
  have eq682769 : (σ x) = (σ y) := by
    first
    | exact superpose eq682381 eq256380
    | exact resolve eq256380 eq682381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256380
  have eq682770 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq682381 eq20
    | exact resolve eq20 eq682381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq682381
  have eq682918 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq682769 eq26
    | exact resolve eq26 eq682769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq683582 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq682918
       have i₂ := eq651509 sF2
       grind)
    | exact superpose eq651509 eq682918
    | exact resolve eq682918 eq651509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651509 eq682918
  have eq683764 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq682330 eq683582
    | exact resolve eq683582 eq682330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682330 eq683582
  have eq683891 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq682769 eq683764
    | exact resolve eq683764 eq682769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682769 eq683764
  have eq684194 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq683891 eq27
    | exact resolve eq27 eq683891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq683891
  have eq684880 : False := by grind
  exact eq684880

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_y_pyx_Equation960 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq32 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X3 ∨ (k X0 X3) = (M.op X3 X0) ∨ X0 = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 X1 X2
       have i₂ := eq14 X0 X3
       grind)
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X3
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X3 : G, X0 = X3 ∨ (k X0 X3) = (M.op X3 X0) ∨ X0 = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq41 X0 x x X3
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq41
    | (have j0 := eq41 X0 x x X3
       grind)
    | exact resolve eq41 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq44 : ∀ X0 X3 : G, (k X0 X3) = (M.op X3 X0) ∨ X0 = X3 := by
    intro X0 X3
    first
    | (have j0 := eq43 X0 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq47 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq32
    | (have j0 := eq32 X0 X1
       grind)
    | exact resolve eq32 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq49 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq47 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq47
    | (have j0 := eq47 X0 X1
       grind)
    | exact resolve eq47 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq81 : ∀ X0 X1 X2 : G, (σ X0) = (M.op X1 (M.op (M.op X2 X1) (σ (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X1 X2
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq282 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq49 X0 X1
       have i₂ := eq44 X1 X0
       grind)
    | exact superpose eq44 eq49
    | (have j0 := eq49 X0 X1
       have j1 := eq44 (M.op (σ X0) (σ X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq49 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq49
  have eq3671 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq282 x y
       grind)
    | exact superpose eq282 eq16
    | (have j1 := eq282 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq282 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq282 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq282 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282
  have eq3732 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq3671
  have eq6035 : ∀ X0 X1 : G, (σ y) = (M.op X0 (M.op (M.op X1 X0) (σ (M.op x x)))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq81 y X0 X1
       have i₂ := eq3732
       grind)
    | exact superpose eq3732 eq81
    | exact resolve eq81 eq3732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3732
  have eq6099 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq6035 x x
       have i₂ := eq81 x x x
       grind)
    | exact superpose eq81 eq6035
    | exact resolve eq6035 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq6035
  have eq6100 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq6099
  have eq6108 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq6100
       grind)
    | exact superpose eq6100 eq10
    | exact resolve eq10 eq6100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6100
  have eq6137 : x = y ∨ x = y := by
    first
    | (have i₁ := eq6108
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq6108
    | exact resolve eq6108 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6108
  have eq6138 : x = y := by grind
  clear eq6137
  have eq8409 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6138
       grind)
    | exact superpose eq6138 eq16
    | exact resolve eq16 eq6138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6138
  have eq8410 : False := by grind
  exact eq8410

/-- `Equation964`: `x = y ◇ ((z ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(X,X) = m(X,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pxy_x_pyy_pxy_Equation964 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law964 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law964.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X1) (M.op X1 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
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
  have eq76 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X2) (M.op X2 (M.op (M.op X5 (M.op X1 X2)) X3))) = (M.op X2 (M.op (M.op X0 (M.op X1 X2)) (M.op (M.op X1 X2) X3))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq62 (M.op (M.op X5 (M.op X1 X2)) X3) X2 X1 X4
       have i₂ := eq62 X3 (M.op X1 X2) X5 X0
       grind)
    | exact superpose eq62 eq62
    | exact resolve eq62 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X0 x
       have i₂ := eq62 X2 X0 X1 x
       grind)
    | exact superpose eq62 eq9
    | exact resolve eq9 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X1 (M.op X1 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1 x
       have i₂ := eq62 (M.op X1 X2) X1 x X0
       grind)
    | exact superpose eq62 eq9
    | exact resolve eq9 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X1)) (M.op (M.op X2 X1) X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq79 X1 X2 (M.op (M.op X3 (M.op X2 X1)) (M.op (M.op X2 X1) X0))
       have i₂ := eq9 X0 (M.op X2 X1) X3
       grind)
    | exact superpose eq9 eq79
    | exact resolve eq79 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 (M.op X1 X2)) X3) = (M.op X2 (M.op X2 (M.op (M.op X0 (M.op X1 X2)) (M.op (M.op X1 X2) X3)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq79 X2 X1 (M.op (M.op X4 (M.op X1 X2)) X3)
       have i₂ := eq62 X3 (M.op X1 X2) X4 X0
       grind)
    | exact superpose eq62 eq79
    | exact resolve eq79 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 X0)) = (M.op (M.op X2 X1) (M.op (M.op X3 (M.op X2 X1)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq79 X1 X2 (M.op (M.op X2 X1) (M.op (M.op X3 (M.op X2 X1)) X0))
       have i₂ := eq79 (M.op X2 X1) X3 X0
       grind)
    | exact superpose eq79 eq79
    | exact resolve eq79 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X2) X0) = (M.op X2 (M.op (M.op X4 X2) (M.op X2 (M.op (M.op X3 X2) X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq62 (M.op X2 (M.op (M.op X3 X2) X0)) X2 X4 X1
       have i₂ := eq79 X2 X3 X0
       grind)
    | exact superpose eq79 eq62
    | exact resolve eq62 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X0) = (M.op (M.op X3 X2) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq101 X0 X1 X2 X3 x
       have i₂ := eq9 (M.op (M.op X3 X2) X0) X2 x
       grind)
    | exact superpose eq9 eq101
    | exact resolve eq101 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq112 : ∀ X1 X2 X3 X4 : G, (M.op (M.op X4 (M.op X1 X2)) X3) = (M.op X2 (M.op X2 (M.op X2 (M.op X2 X3)))) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq94 x X1 X2 X3 X4
       have i₂ := eq93 X3 X2 X1 x
       grind)
    | exact superpose eq93 eq94
    | exact resolve eq94 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq115 : ∀ X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X2) (M.op X2 (M.op (M.op X5 (M.op X1 X2)) X3))) = (M.op X2 (M.op X2 (M.op X2 X3))) := by
    intro X1 X2 X3 X4 X5
    first
    | (have i₁ := eq76 x X1 X2 X3 X4 X5
       have i₂ := eq93 X3 X2 X1 x
       grind)
    | exact superpose eq93 eq76
    | exact resolve eq76 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq149 : ∀ X0 X2 X3 X4 : G, (M.op (M.op X2 (M.op X2 X0)) (M.op (M.op X4 (M.op X2 (M.op X2 X0))) X3)) = (M.op X0 (M.op (M.op X2 (M.op X2 X0)) X3)) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq62 X3 (M.op X2 (M.op X2 X0)) X4 (M.op x X2)
       have i₂ := eq83 x X2 X0
       grind)
    | exact superpose eq83 eq62
    | exact resolve eq62 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq151 : ∀ X0 X2 X3 : G, (M.op (M.op X2 X0) (M.op (M.op X2 X0) X3)) = (M.op X0 (M.op (M.op X2 (M.op X2 X0)) X3)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq149 X0 X2 X3 x
       have i₂ := eq95 X3 (M.op X2 X0) X2 x
       grind)
    | exact superpose eq95 eq149
    | exact resolve eq149 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq188 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op X1 (M.op X2 (M.op X2 X0))) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq104 X3 X1 (M.op X2 (M.op X2 X0)) (M.op x X2)
       have i₂ := eq83 x X2 X0
       grind)
    | exact superpose eq83 eq104
    | exact resolve eq104 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq224 : ∀ X0 X1 X2 X3 : G, (M.op X3 X1) ≠ (M.op (M.op X0 X1) X2) ∨ (k X2 (M.op X3 X1)) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X2 (M.op X3 X1)
       have i₂ := eq104 X2 X3 X1 X0
       grind)
    | (have i₁ := eq12 X2 (M.op X3 X1)
       have i₂ := eq104 X2 X0 X1 X3
       grind)
    | exact superpose eq104 eq12
    | (have j0 := eq12 X2 (M.op X3 X1)
       grind)
    | (have r₁ := eq12 X0 (M.op (M.op X3 X0) X0)
       have r₂ := eq104 X0 (M.op X3 X0) X0 X3
       grind)
    | (have r₁ := eq12 X0 (M.op (M.op X1 X0) X0)
       have r₂ := eq104 X0 X1 X0 (M.op X1 X0)
       grind)
    | exact resolve eq12 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq226 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X1) (M.op (M.op X5 (M.op X4 X1)) X2)) = (M.op (M.op X3 (M.op X4 X1)) (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq62 X2 (M.op X4 X1) X5 X3
       have i₂ := eq104 X2 X4 X1 X0
       grind)
    | (have i₁ := eq62 X2 (M.op X4 X1) X5 X3
       have i₂ := eq104 X2 X0 X1 X4
       grind)
    | exact superpose eq104 eq62
    | exact resolve eq62 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq233 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X1) (M.op (M.op X2 (M.op X3 X1)) X4)) = (M.op (M.op X5 (M.op X3 X1)) (M.op (M.op X3 X1) X4)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq62 X4 (M.op X3 X1) X2 X5
       have i₂ := eq104 (M.op (M.op X2 (M.op X3 X1)) X4) X3 X1 X0
       grind)
    | (have i₁ := eq62 X4 (M.op X3 X1) X2 X5
       have i₂ := eq104 (M.op (M.op X2 (M.op X3 X1)) X4) X0 X1 X3
       grind)
    | exact superpose eq104 eq62
    | exact resolve eq62 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq237 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X1 X4)) = (M.op (M.op X0 X1) (M.op (M.op X2 (M.op X3 X1)) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq233 X0 X1 X2 X3 X4 x
       have i₂ := eq93 X4 X1 X3 x
       grind)
    | exact superpose eq93 eq233
    | exact resolve eq233 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq233
  have eq240 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X1 X2)) = (M.op (M.op X3 (M.op X4 X1)) (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq226 X0 X1 X2 X3 X4 x
       have i₂ := eq95 X2 X1 X4 x
       grind)
    | exact superpose eq95 eq226
    | exact resolve eq226 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq226
  have eq1331 : ∀ X0 X1 : G, (k X0 (M.op (M.op X1 X0) X0)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq224 X0 X0 X0 (M.op X1 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq1367 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op X1 (τ X0)) (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (M.op (M.op X1 (τ X0)) (τ X0))
       have i₂ := eq1331 (τ X0) X1
       grind)
    | exact superpose eq1331 eq17
    | exact resolve eq17 eq1331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1331
  have eq1372 : ∀ X0 X1 : G, (k X0 (σ (M.op (M.op X1 (τ X0)) (τ X0)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1367 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1367
    | exact resolve eq1367 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1367
  have eq1622 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq1639 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op (M.op X3 (M.op X0 (M.op X0 X0))) X2) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq188 X1 X3 X0 X2
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq188 X0 X1 X0 X3
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq188
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq188 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1666 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1622 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1622
  have eq1667 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1666 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1666
  have eq1676 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X2) = (M.op X1 X2) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1639 X0 X1 X2 x
       have i₂ := eq188 X0 x X0 X2
       grind)
    | exact superpose eq188 eq1639
    | (have j0 := eq1639 X0 X1 X2 x
       grind)
    | exact resolve eq1639 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188 eq1639
  have eq2005 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 (M.op X1 (M.op X2 X3))) X4) = (M.op (M.op X5 X3) (M.op (M.op X2 X3) (M.op (M.op X2 X3) (M.op (M.op X2 X3) X4)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq104 (M.op (M.op X2 X3) (M.op (M.op X2 X3) (M.op (M.op X2 X3) X4))) X5 X3 X2
       have i₂ := eq112 X1 (M.op X2 X3) X4 X0
       grind)
    | exact superpose eq112 eq104
    | exact resolve eq104 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq2016 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 (M.op X1 (M.op X2 X3))) X4) = (M.op (M.op X5 X3) (M.op X3 (M.op (M.op X2 (M.op X2 X3)) (M.op (M.op X2 X3) X4)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq2005 X0 X1 X2 X3 X4 X5
       have i₂ := eq151 X3 X2 (M.op (M.op X2 X3) X4)
       grind)
    | exact superpose eq151 eq2005
    | exact resolve eq2005 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151 eq2005
  have eq2142 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 (M.op X2 X3))) X4) = (M.op X3 (M.op X3 (M.op X3 (M.op (M.op X2 X3) X4)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2016 X0 X1 X2 X3 X4 x
       have i₂ := eq115 X2 X3 (M.op (M.op X2 X3) X4) x X2
       grind)
    | exact superpose eq115 eq2016
    | exact resolve eq2016 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq2016
  have eq2212 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X4) = (M.op (M.op X0 (M.op X1 (M.op X2 X3))) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2142 X0 X1 X2 X3 X4
       have i₂ := eq79 X3 X2 X4
       grind)
    | exact superpose eq79 eq2142
    | exact resolve eq2142 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2142
  have eq6572 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1667 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1667
  have eq6577 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq6572 X0 X1
       have j1 := eq1676 X0 X1 x
       grind)
    | (have r₁ := eq6572 X0 X1
       have r₂ := eq1676 X0 X1 X1
       grind)
    | (have r₁ := eq6572 X1 X0
       have r₂ := eq1676 X0 X1 X0
       grind)
    | (have r₁ := eq6572 (M.op X0 X0) X0
       have r₂ := eq1676 X0 (M.op X0 X0) x
       grind)
    | exact resolve eq6572 eq1676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1676 eq6572
  have eq6626 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq6577 (σ X0) (σ X1)
       grind)
    | exact superpose eq6577 eq15
    | (have j1 := eq6577 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq6577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6627 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (M.op X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq6577 (σ X0) X1
       grind)
    | exact superpose eq6577 eq28
    | (have j1 := eq6577 (σ X0) X1
       grind)
    | exact resolve eq28 eq6577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6633 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X1 X0
       have i₂ := eq6577 (τ X0) (τ X1)
       grind)
    | exact superpose eq6577 eq31
    | (have j1 := eq6577 (τ X0) (τ X1)
       grind)
    | exact resolve eq31 eq6577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6641 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6627 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6627
    | exact resolve eq6627 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6627
  have eq6688 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6641 X0 X1
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq6641
    | (have j0 := eq6641 X0 X1
       grind)
    | exact resolve eq6641 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6641
  have eq8089 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (τ X1)) X3) = (M.op (τ (k X0 X1)) X3) ∨ (τ X1) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq104 X3 X2 (τ X1) (τ X0)
       have i₂ := eq6633 X0 X1
       grind)
    | exact superpose eq6633 eq104
    | (have j1 := eq6633 X0 X1
       grind)
    | exact resolve eq104 eq6633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8122 : ∀ X0 X1 : G, (k X1 (σ (M.op (τ X0) (τ X1)))) = X1 ∨ (τ (k X1 X0)) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1372 X1 (τ X0)
       have i₂ := eq6633 X1 X0
       grind)
    | exact superpose eq6633 eq1372
    | (have j1 := eq6633 X1 X0
       grind)
    | exact resolve eq1372 eq6633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1372
  have eq8126 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X1) = (k (τ X1) (τ X0)) ∨ (τ (k X1 X0)) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (τ X1) (τ X0)
       have i₂ := eq6633 X1 X0
       grind)
    | exact superpose eq6633 eq12
    | (have j0 := eq12 (τ X1) (τ X0)
       have j1 := eq6633 X1 X0
       grind)
    | (have r₁ := eq12 (τ X0) (τ X1)
       have r₂ := eq6633 X0 X1
       grind)
    | exact resolve eq12 eq6633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8173 : ∀ X0 X1 : G, (τ X1) = (k (τ X1) (τ X0)) ∨ (τ (k X1 X0)) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq8126 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8126
  have eq8181 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X1) (τ X0)) ∨ (τ X1) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8173 X0 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq8173
    | (have j0 := eq8173 X0 X1
       grind)
    | exact resolve eq8173 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8173
  have eq8194 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op X0 (τ X1)) ∨ (τ (k (σ X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8181 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8181
    | exact resolve eq8181 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8213 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (τ (k X1 X0)) = (M.op (τ X1) (τ X0)) ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6633 X1 X0
       have i₂ := eq8181 X1 X0
       grind)
    | exact superpose eq8181 eq6633
    | (have j0 := eq6633 X1 X0
       have j1 := eq8181 X0 X1
       grind)
    | exact resolve eq6633 eq8181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8181
  have eq8273 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X1) (τ X0)) ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq8213 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8213
  have eq8280 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op X0 (τ X1)) ∨ (τ (k (σ X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8194 X0 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq8194
    | (have j0 := eq8194 X0 X1
       grind)
    | exact resolve eq8194 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8194
  have eq8282 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op X0 (τ X1)) ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8280 X0 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq8280
    | (have j0 := eq8280 X0 X1
       grind)
    | exact resolve eq8280 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8280
  have eq8298 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq8282 X0 X1
       grind)
    | exact superpose eq8282 eq18
    | (have j1 := eq8282 X0 X1
       grind)
    | exact resolve eq18 eq8282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8282
  have eq9382 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (τ X1))) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (τ X1)
       have i₂ := eq8298 (τ X0) X1
       grind)
    | exact superpose eq8298 eq17
    | (have j1 := eq8298 (τ X0) X1
       grind)
    | exact resolve eq17 eq8298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq8298
  have eq9397 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9382 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq9382
    | (have j0 := eq9382 X0 X1
       grind)
    | exact resolve eq9382 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9382
  have eq9414 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9397 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq9397
    | (have j0 := eq9397 X0 X1
       grind)
    | exact resolve eq9397 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9397
  have eq9424 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9414 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq9414
    | (have j0 := eq9414 X0 X1
       grind)
    | exact resolve eq9414 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9414
  have eq9520 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (k X0 X1) = X0 ∨ (τ (k X1 X0)) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9424 X0 X1
       have i₂ := eq6633 X1 X0
       grind)
    | exact superpose eq6633 eq9424
    | (have j0 := eq9424 X0 X1
       have j1 := eq6633 X1 X0
       grind)
    | exact resolve eq9424 eq6633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6633 eq9424
  have eq9541 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k X0 X1) = X0 ∨ (τ (k X1 X0)) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9520 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq9520
    | (have j0 := eq9520 X0 X1
       grind)
    | exact resolve eq9520 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9520
  have eq9542 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X1) (τ X0)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq9541 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9541
  have eq9737 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op X0 (τ X1)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9542 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9542
    | (have j0 := eq9542 X1 (σ X0)
       grind)
    | exact resolve eq9542 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9776 : ∀ X0 X1 X2 : G, (τ X1) = (M.op (τ X0) (M.op (M.op X2 (τ X0)) (τ (k X0 X1)))) ∨ (k X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (τ X1) (τ X0) X2
       have i₂ := eq9542 X1 X0
       grind)
    | exact superpose eq9542 eq9
    | (have j1 := eq9542 X1 X0
       grind)
    | exact resolve eq9 eq9542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9542
  have eq9836 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op X0 (τ X1)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9737 X0 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq9737
    | (have j0 := eq9737 X0 X1
       grind)
    | exact resolve eq9737 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9737
  have eq10244 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9836 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9836
    | (have j0 := eq9836 X1 (σ X0)
       grind)
    | exact resolve eq9836 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9836
  have eq10308 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10244 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq10244
    | (have j0 := eq10244 X0 X1
       grind)
    | exact resolve eq10244 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10244
  have eq10356 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq10308 X0 X1
       grind)
    | exact superpose eq10308 eq10
    | (have j1 := eq10308 X0 X1
       grind)
    | exact resolve eq10 eq10308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10308
  have eq10376 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10356 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq10356
    | (have j0 := eq10356 X0 X1
       grind)
    | exact resolve eq10356 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10356
  have eq10447 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ X1)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq10376 (σ X0) X1
       grind)
    | exact superpose eq10376 eq28
    | (have j1 := eq10376 (σ X0) X1
       grind)
    | exact resolve eq28 eq10376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10515 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10447 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq10447
    | (have j0 := eq10447 X0 X1
       grind)
    | exact resolve eq10447 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10447
  have eq10818 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10515 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq10515
    | (have j0 := eq10515 X1 (σ X0)
       grind)
    | exact resolve eq10515 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10859 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = X0 ∨ (τ X1) = (k (τ X1) X0) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10376 (τ X1) X0
       have i₂ := eq10515 X0 X1
       grind)
    | exact superpose eq10515 eq10376
    | (have j0 := eq10376 (τ X1) X0
       have j1 := eq10515 X0 X1
       grind)
    | exact resolve eq10376 eq10515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10515
  have eq10890 : ∀ X0 X1 : G, (τ X1) = (k (τ X1) X0) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq10859 X0 X1
       have j1 := eq12 (τ X1) X0
       grind)
    | (have r₁ := eq10859 X1 X1
       have r₂ := eq12 (τ X1) X1
       grind)
    | exact resolve eq10859 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10859
  have eq10903 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10818 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq10818
    | (have j0 := eq10818 X0 X1
       grind)
    | exact resolve eq10818 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10818
  have eq11149 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10903 X0 X1
       have i₂ := eq10376 X1 X0
       grind)
    | exact superpose eq10376 eq10903
    | (have j0 := eq10903 X0 X1
       have j1 := eq10376 X1 X0
       grind)
    | exact resolve eq10903 eq10376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10903
  have eq11217 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11149 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11149
  have eq11485 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11217 x y
       grind)
    | exact superpose eq11217 eq16
    | (have j1 := eq11217 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq11217 x y
       grind)
    | exact resolve eq16 eq11217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11217
  have eq11561 : y = (k y x) := by grind
  clear eq11485
  have eq11584 : y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6577 y x
       have i₂ := eq11561
       grind)
    | exact superpose eq11561 eq6577
    | (have j0 := eq6577 x y
       grind)
    | exact resolve eq6577 eq11561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6577
  have eq11585 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6626 y x
       have i₂ := eq11561
       grind)
    | exact superpose eq11561 eq6626
    | (have j0 := eq6626 x y
       grind)
    | exact resolve eq6626 eq11561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6626
  have eq11588 : y = (M.op y x) ∨ x = (k x y) := by
    first
    | (have i₁ := eq10376 x y
       have i₂ := eq11561
       grind)
    | exact superpose eq11561 eq10376
    | (have j0 := eq10376 x y
       grind)
    | exact resolve eq10376 eq11561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11561
  have eq11590 : x = (k x y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq11588
       have r₂ := eq12 x y
       grind)
    | exact resolve eq11588 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11588
  have eq11852 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op X0 x) X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq104 X1 X0 x y
       have i₂ := eq11584
       grind)
    | exact superpose eq11584 eq104
    | exact resolve eq104 eq11584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13207 : ∀ X0 X1 X2 : G, y = (M.op (M.op X0 x) (M.op x x)) ∨ (M.op y X1) = (M.op (M.op X2 x) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq83 X0 x y
       have i₂ := eq11852 X2 X1
       grind)
    | exact superpose eq11852 eq83
    | (have j1 := eq11852 X2 X1
       grind)
    | exact resolve eq83 eq11852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11852
  have eq18983 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) (M.op (σ x) X0))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq9 X0 (σ x) (σ y)
       have i₂ := eq11585
       grind)
    | exact superpose eq11585 eq9
    | exact resolve eq9 eq11585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11585
  have eq33652 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X1)) ∨ (τ X1) = (k (τ X1) (τ X0)) ∨ (τ X1) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (τ X1) (τ X0)
       have i₂ := eq8273 X1 X0
       grind)
    | exact superpose eq8273 eq12
    | (have j0 := eq12 (τ X1) (τ X0)
       have j1 := eq8273 X1 X0
       grind)
    | exact resolve eq12 eq8273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8273
  have eq33724 : ∀ X0 X1 : G, (τ X1) = (τ (k X1 X0)) ∨ (τ X0) ≠ (τ (k X0 X1)) ∨ (τ X1) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq33652 X0 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq33652
    | (have j0 := eq33652 X0 X1
       grind)
    | exact resolve eq33652 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33652
  have eq33725 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X1)) ∨ (τ X1) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq33724 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33724
  have eq33809 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (τ (σ (k X0 X1))) ∨ (τ (σ X1)) = (τ (k (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq33725 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq33725
    | (have j0 := eq33725 (σ X0) (σ X1)
       grind)
    | exact resolve eq33725 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33814 : ∀ X0 X1 : G, (τ (τ X0)) ≠ (τ (τ X0)) ∨ (τ X1) = (τ (k X1 (τ X0))) ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq33725 (τ X0) X1
       have i₂ := eq10890 X1 X0
       grind)
    | exact superpose eq10890 eq33725
    | (have j0 := eq33725 (τ X0) X1
       have j1 := eq10890 X1 X0
       grind)
    | exact resolve eq33725 eq10890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10890 eq33725
  have eq33891 : ∀ X0 X1 : G, (τ X1) = (τ (k X1 (τ X0))) ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq33814 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33814
  have eq33929 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (k X0 X1) ∨ (τ (σ X1)) = (τ (k (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq33809 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq33809
    | (have j0 := eq33809 X0 X1
       grind)
    | exact resolve eq33809 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33809
  have eq33940 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (τ (σ X1)) = (τ (k (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq33929 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq33929
    | (have j0 := eq33929 X0 X1
       grind)
    | exact resolve eq33929 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33929
  have eq33949 : ∀ X0 X1 : G, (τ (σ X1)) = (k (τ (σ X1)) X0) ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq33940 X0 X1
       have i₂ := eq22 (σ X1) X0
       grind)
    | exact superpose eq22 eq33940
    | (have j0 := eq33940 X0 X1
       grind)
    | exact resolve eq33940 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33940
  have eq33952 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq33949 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq33949
    | (have j0 := eq33949 X0 X1
       grind)
    | exact resolve eq33949 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33949
  have eq51359 : ∀ X0 X1 : G, (τ (τ X0)) = (τ (τ (k X0 X1))) ∨ (k X1 (σ (τ X0))) = (M.op X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq33891 X1 (τ X0)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq33891
    | (have j0 := eq33891 X1 (τ X0)
       grind)
    | exact resolve eq33891 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33891
  have eq51519 : ∀ X0 X1 : G, (τ (τ X0)) = (τ (τ (k X0 X1))) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq51359 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq51359
    | (have j0 := eq51359 X0 X1
       grind)
    | exact resolve eq51359 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51359
  have eq51577 : ∀ X0 X1 : G, (τ (τ X0)) = (τ (τ (M.op X0 X1))) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq51519 X0 X1
       have i₂ := eq6688 X0 X1
       grind)
    | exact superpose eq6688 eq51519
    | (have j0 := eq51519 X0 X1
       have j1 := eq6688 X0 X1
       grind)
    | exact resolve eq51519 eq6688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6688 eq51519
  have eq270126 : ∀ X0 X1 : G, (k X1 (σ (M.op X0 (τ X1)))) = X1 ∨ (τ (k X1 (σ X0))) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8122 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8122
    | exact resolve eq8122 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8122
  have eq270158 : ∀ X0 X1 : G, (k X1 (σ (M.op X0 (τ X1)))) = X1 ∨ (k (τ X1) X0) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq270126 X0 X1
       have i₂ := eq22 X1 X0
       grind)
    | exact superpose eq22 eq270126
    | (have j0 := eq270126 X0 X1
       grind)
    | exact resolve eq270126 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270126
  have eq270200 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ (M.op X1 (τ (σ X0)))))) ∨ (k (τ (σ X0)) X1) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (σ (M.op X1 (τ (σ X0))))
       have i₂ := eq270158 X1 (σ X0)
       grind)
    | exact superpose eq270158 eq28
    | (have j1 := eq270158 X1 (σ X0)
       grind)
    | exact resolve eq28 eq270158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270158
  have eq270204 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (M.op X1 (τ (σ X0)))) ∨ (k (τ (σ X0)) X1) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq270200 X0 X1
       have i₂ := eq10 (M.op X1 (τ (σ X0)))
       grind)
    | exact superpose eq10 eq270200
    | (have j0 := eq270200 X0 X1
       grind)
    | exact resolve eq270200 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270200
  have eq270231 : ∀ X0 X1 : G, (k X0 (M.op X1 X0)) = X0 ∨ (k (τ (σ X0)) X1) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq270204 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq270204
    | (have j0 := eq270204 X0 X1
       grind)
    | exact resolve eq270204 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270204
  have eq270239 : ∀ X0 X1 : G, (k X0 (M.op X1 X0)) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq270231 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq270231
    | (have j0 := eq270231 X0 X1
       grind)
    | exact resolve eq270231 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270231
  have eq270288 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k (M.op X1 X0) X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq33952 X0 (M.op X1 X0)
       have i₂ := eq270239 X0 X1
       grind)
    | exact superpose eq270239 eq33952
    | (have j0 := eq33952 X0 (M.op X1 X0)
       have j1 := eq270239 X0 X1
       grind)
    | (have r₁ := eq33952 X0 (M.op X1 X0)
       have r₂ := eq270239 X0 X1
       grind)
    | exact resolve eq33952 eq270239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270239
  have eq270305 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X1 X0) X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq270288 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270288
  have eq280374 : ∀ X0 X1 X2 : G, (τ X1) = (M.op (τ (σ X0)) (M.op (M.op X2 (τ (σ X0))) (k X0 (τ X1)))) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9776 (σ X0) X1 X2
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq9776
    | (have j0 := eq9776 (σ X0) X1 X2
       grind)
    | exact resolve eq9776 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq9776
  have eq280415 : ∀ X0 X1 X2 : G, (τ X1) = (M.op X0 (M.op (M.op X2 X0) (k X0 (τ X1)))) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq280374 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq280374
    | (have j0 := eq280374 X0 X1 X2
       grind)
    | exact resolve eq280374 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280374
  have eq280440 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (k X1 X0))) = X0 ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq280415 X0 (σ X0) X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq280415
    | (have j0 := eq280415 X1 (σ X0) X2
       grind)
    | exact resolve eq280415 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280415
  have eq280494 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (k X1 X0))) = X0 ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq280440 X0 X1 X2
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq280440
    | (have j0 := eq280440 X0 X1 X2
       grind)
    | exact resolve eq280440 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280440
  have eq280599 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 (k X2 X0))) = X0 ∨ (σ X0) = (σ (k X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 (k X2 X0) X2 x X1
       have i₂ := eq280494 X0 X2 x
       grind)
    | exact superpose eq280494 eq62
    | (have j1 := eq280494 X0 X2 X2
       grind)
    | exact resolve eq62 eq280494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280494
  have eq280745 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (M.op X1 (k X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq79 X1 x (M.op X1 (k X1 X0))
       have i₂ := eq280599 X0 x X1
       grind)
    | exact superpose eq280599 eq79
    | (have j1 := eq280599 X0 X1 X1
       grind)
    | exact resolve eq79 eq280599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280599
  have eq280907 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (M.op X1 (M.op X1 X0)) = (M.op X1 (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq280745 X0 X1
       grind)
    | exact superpose eq280745 eq10
    | (have j1 := eq280745 X0 X1
       grind)
    | exact resolve eq10 eq280745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280745
  have eq280919 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (M.op X1 (k X1 X0)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq280907 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq280907
    | (have j0 := eq280907 X0 X1
       grind)
    | exact resolve eq280907 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280907
  have eq280943 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X0) (M.op X0 (M.op X0 X1))) = (M.op X0 (M.op (M.op X3 X0) (k X0 X1))) ∨ (k X1 X0) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq62 (k X0 X1) X0 X3 X2
       have i₂ := eq280919 X1 X0
       grind)
    | exact superpose eq280919 eq62
    | (have j1 := eq280919 X1 X0
       grind)
    | exact resolve eq62 eq280919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280919
  have eq280984 : ∀ X0 X1 X3 : G, (M.op X0 (M.op (M.op X3 X0) (k X0 X1))) = X1 ∨ (k X1 X0) = X1 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq280943 X0 X1 x X3
       have i₂ := eq83 x X0 X1
       grind)
    | exact superpose eq83 eq280943
    | (have j0 := eq280943 X0 X1 x X3
       grind)
    | exact resolve eq280943 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280943
  have eq281287 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (k (M.op X2 X1) X0))) = X0 ∨ (k X0 (M.op X2 X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq237 X2 X1 x X2 (k (M.op X2 X1) X0)
       have i₂ := eq280984 (M.op X2 X1) X0 x
       grind)
    | exact superpose eq280984 eq237
    | (have j1 := eq280984 (M.op X2 X1) X0 x
       grind)
    | exact resolve eq237 eq280984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237 eq280984
  have eq283092 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X0) = (k (M.op X3 X2) X0) ∨ (k X0 (M.op X3 X2)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq83 X1 X2 (k (M.op X3 X2) X0)
       have i₂ := eq281287 X0 X2 X3
       grind)
    | exact superpose eq281287 eq83
    | (have j1 := eq281287 X0 X2 X3
       grind)
    | exact resolve eq83 eq281287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281287
  have eq284018 : ∀ X0 X1 X2 X3 : G, X0 ≠ X0 ∨ (M.op X1 X2) = (k (M.op X1 X2) X0) ∨ (M.op (M.op X3 X2) X0) = (k (M.op X1 X2) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq33952 X0 (M.op X1 X2)
       have i₂ := eq283092 X0 X3 X2 X1
       grind)
    | exact superpose eq283092 eq33952
    | (have j0 := eq33952 X0 (M.op X1 X2)
       have j1 := eq283092 X0 X3 X2 X1
       grind)
    | (have r₁ := eq33952 (M.op (M.op X1 X0) X0) X0
       have r₂ := eq283092 X0 X1 X0 (M.op X1 X0)
       grind)
    | (have r₁ := eq33952 X0 (M.op X3 X2)
       have r₂ := eq283092 X0 X1 X2 X3
       grind)
    | exact resolve eq33952 eq283092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33952 eq283092
  have eq284022 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (k (M.op X1 X2) X0) ∨ (M.op (M.op X3 X2) X0) = (k (M.op X1 X2) X0) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq284018 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284018
  have eq324654 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op (M.op X3 X1) X2) ∨ (M.op (M.op X3 X1) X2) = (k (M.op X0 X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq284022 X2 X0 X1 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284022
  have eq345918 : ∀ X0 X2 X3 X4 : G, (M.op (M.op X3 (M.op X2 (M.op X2 X0))) X4) ≠ X0 ∨ (M.op (M.op X3 (M.op X2 (M.op X2 X0))) X4) = (k X0 X4) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq324654 (M.op X0 x) (M.op x (M.op x X2)) X2 X3
       have i₂ := eq83 X0 x X2
       grind)
    | exact superpose eq83 eq324654
    | (have r₁ := eq324654 X0 x (M.op x (M.op x (M.op X0 x))) X0
       have r₂ := eq83 X0 x (M.op X0 x)
       grind)
    | exact resolve eq324654 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324654
  have eq345989 : ∀ X0 X2 X3 X4 : G, (M.op X0 X4) ≠ X0 ∨ (M.op (M.op X3 (M.op X2 (M.op X2 X0))) X4) = (k X0 X4) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq345918 X0 X2 X3 X4
       have i₂ := eq2212 X3 X2 X2 X0 X4
       grind)
    | exact superpose eq2212 eq345918
    | (have j0 := eq345918 X0 X2 X3 X4
       grind)
    | exact resolve eq345918 eq2212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345918
  have eq345990 : ∀ X0 X4 : G, (M.op X0 X4) ≠ X0 ∨ (M.op X0 X4) = (k X0 X4) := by
    intro X0 X4
    first
    | (have i₁ := eq345989 X0 x x X4
       have i₂ := eq2212 x x x X0 X4
       grind)
    | exact superpose eq2212 eq345989
    | (have j0 := eq345989 X0 x x X4
       grind)
    | (have r₁ := eq345989 (M.op x (M.op x (M.op x x))) x x (M.op x (M.op x x))
       have r₂ := eq2212 x x x x (M.op x (M.op x x))
       grind)
    | exact resolve eq345989 eq2212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2212 eq345989
  have eq401318 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) X2) = (M.op (τ (k X3 (σ X0))) X2) ∨ (M.op X0 (τ X3)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8089 X0 (σ X0) X2 X3
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8089
    | exact resolve eq8089 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8089
  have eq401360 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) X2) = (M.op (k (τ X3) X0) X2) ∨ (M.op X0 (τ X3)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq401318 X0 X1 X2 X3
       have i₂ := eq22 X3 X0
       grind)
    | exact superpose eq22 eq401318
    | (have j0 := eq401318 X0 X1 X2 X3
       grind)
    | exact resolve eq401318 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq401318
  have eq401407 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X3) = (M.op (k X0 X2) X3) ∨ (M.op X2 X0) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq401360 X0 X1 X2 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq401360
    | exact resolve eq401360 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401360
  have eq401786 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X3) = (M.op X0 X3) ∨ (M.op X2 X0) = X2 ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq401407 X0 X1 X2 X3
       have i₂ := eq10376 X0 X2
       grind)
    | exact superpose eq10376 eq401407
    | (have j0 := eq401407 X0 X1 X2 X3
       have j1 := eq10376 X0 X2
       grind)
    | exact resolve eq401407 eq10376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10376 eq401407
  have eq402486 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X3) = (M.op X0 X3) ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq401786 X0 X1 X2 X3
       have j1 := eq345990 X2 X0
       grind)
    | (have r₁ := eq401786 X1 X1 X2 X2
       have r₂ := eq345990 (M.op X1 X2) X2
       grind)
    | (have r₁ := eq401786 (M.op (M.op X1 X2) x) X1 X2 x
       have r₂ := eq345990 (M.op (M.op X1 X2) x) x
       grind)
    | (have r₁ := eq401786 x X1 X0 X3
       have r₂ := eq345990 X0 x
       grind)
    | exact resolve eq401786 eq345990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401786
  have eq406585 : ∀ X0 X1 X2 X3 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op (M.op X2 X0) X3) = (M.op (τ X1) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq402486 (τ X1) X2 X0 X3
       grind)
    | exact superpose eq402486 eq18
    | (have j1 := eq402486 (τ X1) X2 X0 X3
       grind)
    | exact resolve eq18 eq402486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq402486
  have eq429463 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X3) = (M.op X0 X3) ∨ (k (σ X2) (σ X0)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq406585 X0 (σ X0) X2 X3
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq406585
    | exact resolve eq406585 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406585
  have eq429505 : ∀ X0 X1 X2 X3 : G, (σ (k X2 X0)) = (σ (M.op X2 X0)) ∨ (M.op (M.op X1 X2) X3) = (M.op X0 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq429463 X0 X1 X2 X3
       have i₂ := eq15 X2 X0
       grind)
    | exact superpose eq15 eq429463
    | (have j0 := eq429463 X0 X1 X2 X3
       grind)
    | exact resolve eq429463 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429463
  have eq429558 : ∀ X0 X1 : G, (σ (M.op x y)) = (σ x) ∨ (M.op y X1) = (M.op (M.op X0 x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq429505 y X0 x X1
       have i₂ := eq11590
       grind)
    | exact superpose eq11590 eq429505
    | (have j0 := eq429505 y X0 x X1
       grind)
    | exact resolve eq429505 eq11590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11590 eq429505
  have eq480123 : ∀ X0 X1 : G, (τ (M.op X0 X1)) = (σ (τ (τ X0))) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (τ (M.op X0 X1))
       have i₂ := eq51577 X0 X1
       grind)
    | exact superpose eq51577 eq11
    | (have j1 := eq51577 X0 X1
       grind)
    | exact resolve eq11 eq51577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51577
  have eq480124 : ∀ X0 X1 : G, (τ (M.op X0 X1)) = (σ (τ (τ X0))) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq480123 X0 X1
       have j1 := eq345990 X1 X0
       grind)
    | (have r₁ := eq480123 x X0
       have r₂ := eq345990 X0 x
       grind)
    | exact resolve eq480123 eq345990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345990 eq480123
  have eq480125 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X1)) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq480124 X0 X1
       have i₂ := eq11 (τ X0)
       grind)
    | exact superpose eq11 eq480124
    | (have j0 := eq480124 X0 X1
       grind)
    | exact resolve eq480124 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480124
  have eq480150 : ∀ X0 X1 X2 : G, (k (τ X0) (τ X2)) = (τ (k (M.op X0 X1) X2)) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31 X2 (M.op X0 X1)
       have i₂ := eq480125 X0 X1
       grind)
    | exact superpose eq480125 eq31
    | (have j1 := eq480125 X0 X1
       grind)
    | exact resolve eq31 eq480125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480125
  have eq480159 : ∀ X0 X1 X2 : G, (τ (k X0 X2)) = (τ (k (M.op X0 X1) X2)) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq480150 X0 X1 X2
       have i₂ := eq31 X2 X0
       grind)
    | exact superpose eq31 eq480150
    | (have j0 := eq480150 X0 X1 X2
       grind)
    | exact resolve eq480150 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq480150
  have eq480184 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (k (M.op X0 X2) X1) ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 (k (M.op X0 X2) X1)
       have i₂ := eq480159 X0 X2 X1
       grind)
    | exact superpose eq480159 eq11
    | (have j1 := eq480159 X0 X2 X2
       grind)
    | exact resolve eq11 eq480159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480159
  have eq480185 : ∀ X0 X1 X2 : G, (k X0 X1) = (k (M.op X0 X2) X1) ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq480184 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq480184
    | (have j0 := eq480184 X0 X1 X2
       grind)
    | exact resolve eq480184 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480184
  have eq480222 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq270305 X1 X0
       have i₂ := eq480185 X0 X1 X1
       grind)
    | exact superpose eq480185 eq270305
    | (have j0 := eq270305 X0 X1
       have j1 := eq480185 X1 X1 X0
       grind)
    | exact resolve eq270305 eq480185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270305 eq480185
  have eq480273 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq480222 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480222
  have eq480350 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq480273 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480273
  have eq480351 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq480350 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480350
  have eq486518 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq480351 (σ X0)
       grind)
    | exact superpose eq480351 eq15
    | exact resolve eq15 eq480351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq486699 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq486518 X0
       have i₂ := eq480351 X0
       grind)
    | exact superpose eq480351 eq486518
    | exact resolve eq486518 eq480351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480351 eq486518
  have eq490621 : (σ x) = (M.op (σ x) (M.op (σ y) (σ (M.op x x)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18983 (σ x)
       have i₂ := eq486699 x
       grind)
    | exact superpose eq486699 eq18983
    | exact resolve eq18983 eq486699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18983
  have eq490822 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq486699 X0
       grind)
    | exact superpose eq486699 eq9
    | exact resolve eq9 eq486699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq490837 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (σ X0)) X2) = (M.op (σ (M.op X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq104 X2 X1 (σ X0) (σ X0)
       have i₂ := eq486699 X0
       grind)
    | exact superpose eq486699 eq104
    | exact resolve eq104 eq486699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq497337 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq490822 X0 (σ X0)
       have i₂ := eq486699 X0
       grind)
    | exact superpose eq486699 eq490822
    | exact resolve eq490822 eq486699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490822
  have eq497396 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq497337 X0
       have i₂ := eq486699 (M.op X0 X0)
       grind)
    | exact superpose eq486699 eq497337
    | exact resolve eq497337 eq486699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486699 eq497337
  have eq497995 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 (M.op (M.op X1 X0) X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq497396 X0
       have i₂ := eq62 X0 X0 X1 X0
       grind)
    | exact superpose eq62 eq497396
    | exact resolve eq497396 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq498008 : ∀ X0 X1 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (M.op X1 x) X0) = (M.op y X0) := by
    intro X0 X1
    first
    | (have i₁ := eq497396 x
       have i₂ := eq13207 x X0 X1
       grind)
    | exact superpose eq13207 eq497396
    | (have j1 := eq13207 X0 X0 X1
       grind)
    | exact resolve eq497396 eq13207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13207 eq497396
  have eq519434 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (σ x) ∨ (M.op y X1) = (M.op (M.op X0 x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16
       have i₂ := eq498008 X1 X0
       grind)
    | exact superpose eq498008 eq16
    | (have j1 := eq498008 X1 X0
       grind)
    | exact resolve eq16 eq498008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498008
  have eq519543 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op X0 x) X1) := by
    intro X0 X1
    first
    | (have j0 := eq519434 X0 X1
       have j1 := eq429558 X0 X1
       grind)
    | (have r₁ := eq519434 X0 X1
       have r₂ := eq429558 X0 X1
       grind)
    | exact resolve eq519434 eq429558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429558 eq519434
  have eq524482 : (σ x) = (M.op (σ x) (σ (M.op x (M.op y x)))) := by
    first
    | (have i₁ := eq497995 x x
       have i₂ := eq519543 x x
       grind)
    | exact superpose eq519543 eq497995
    | exact resolve eq497995 eq519543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq524487 : ∀ X0 : G, (M.op x (M.op x (M.op y X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq79 x x X0
       have i₂ := eq519543 x X0
       grind)
    | exact superpose eq519543 eq79
    | exact resolve eq79 eq519543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq524498 : ∀ X0 X1 X2 : G, (M.op x (M.op x X0)) = (M.op (M.op X1 (M.op X2 x)) (M.op y X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq240 x x X0 X1 X2
       have i₂ := eq519543 x X0
       grind)
    | exact superpose eq519543 eq240
    | exact resolve eq240 eq519543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240 eq519543
  have eq531949 : ∀ X0 X1 : G, (M.op x (M.op x X0)) = (M.op y (M.op (M.op X1 y) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq524487 (M.op y (M.op (M.op X1 y) X0))
       have i₂ := eq79 y X1 X0
       grind)
    | exact superpose eq79 eq524487
    | exact resolve eq524487 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq524487
  have eq538369 : ∀ X0 : G, (M.op (σ x) (M.op (M.op X0 (σ x)) (σ x))) = (σ (M.op x (M.op y x))) := by
    intro X0
    first
    | (have i₁ := eq9 (σ (M.op x (M.op y x))) (σ x) X0
       have i₂ := eq524482
       grind)
    | exact superpose eq524482 eq9
    | exact resolve eq9 eq524482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524482
  have eq538989 : (σ y) = (M.op (σ y) (σ (M.op x (M.op x y)))) := by
    first
    | (have i₁ := eq497995 y x
       have i₂ := eq531949 y x
       grind)
    | exact superpose eq531949 eq497995
    | exact resolve eq497995 eq531949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531949
  have eq548652 : (σ (M.op y x)) = (M.op (σ (M.op y x)) (σ (M.op (M.op y x) (M.op x (M.op x x))))) := by
    first
    | (have i₁ := eq497995 (M.op y x) x
       have i₂ := eq524498 x x y
       grind)
    | exact superpose eq524498 eq497995
    | exact resolve eq497995 eq524498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497995 eq524498
  have eq548772 : (σ (M.op y x)) = (M.op (σ (M.op y x)) (σ x)) := by
    first
    | (have i₁ := eq548652
       have i₂ := eq83 y x x
       grind)
    | exact superpose eq83 eq548652
    | exact resolve eq548652 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq548652
  have eq548918 : ∀ X0 : G, (M.op (σ (M.op y x)) X0) = (M.op (σ (M.op x x)) X0) := by
    intro X0
    first
    | (have i₁ := eq490837 x (σ (M.op y x)) X0
       have i₂ := eq548772
       grind)
    | exact superpose eq548772 eq490837
    | exact resolve eq490837 eq548772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq549168 : (σ (M.op y x)) = (M.op (σ (M.op x x)) (σ x)) := by
    first
    | (have i₁ := eq548772
       have i₂ := eq548918 (σ x)
       grind)
    | exact superpose eq548918 eq548772
    | exact resolve eq548772 eq548918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548772 eq548918
  have eq549835 : ∀ X0 : G, (σ (M.op y x)) = (M.op (M.op X0 (σ x)) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq490837 x X0 (σ x)
       have i₂ := eq549168
       grind)
    | exact superpose eq549168 eq490837
    | exact resolve eq490837 eq549168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490837 eq549168
  have eq550040 : (M.op (σ x) (σ (M.op y x))) = (σ (M.op x (M.op y x))) := by
    first
    | (have i₁ := eq538369 x
       have i₂ := eq549835 x
       grind)
    | exact superpose eq549835 eq538369
    | exact resolve eq538369 eq549835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538369 eq549835
  have eq553895 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq550040
       have i₂ := eq11584
       grind)
    | exact superpose eq11584 eq550040
    | exact resolve eq550040 eq11584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11584 eq550040
  have eq553939 : x = (M.op x y) := by
    first
    | (have r₁ := eq553895
       have r₂ := eq16
       grind)
    | exact resolve eq553895 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553895
  have eq564187 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq553939
       grind)
    | exact superpose eq553939 eq16
    | exact resolve eq16 eq553939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq564282 : (σ y) = (M.op (σ y) (σ (M.op x x))) := by
    first
    | (have i₁ := eq538989
       have i₂ := eq553939
       grind)
    | exact superpose eq553939 eq538989
    | exact resolve eq538989 eq553939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538989 eq553939
  have eq565945 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq490621
       have i₂ := eq564282
       grind)
    | exact superpose eq564282 eq490621
    | exact resolve eq490621 eq564282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490621 eq564282
  have eq565955 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq565945
  have eq566653 : False := by grind
  exact eq566653

/-- `Equation964`: `x = y ◇ ((z ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(Y,Y) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_x_pyx_pxx_pyx_Equation964 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law964 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law964.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq74 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X4 X2) (M.op (M.op X3 X2) (M.op X2 X0)))) = (M.op (M.op X1 X2) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq63 (M.op (M.op X3 X2) (M.op X2 X0)) X2 X4 X1
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq63
    | exact resolve eq63 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X0) (M.op (M.op X5 (M.op X4 X0)) (M.op X0 X2))) = (M.op (M.op X3 (M.op X4 X0)) (M.op X0 (M.op (M.op X1 X0) X2))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq63 (M.op X0 X2) (M.op X4 X0) X5 X3
       have i₂ := eq63 X2 X0 X1 X4
       grind)
    | exact superpose eq63 eq63
    | exact resolve eq63 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq63 (M.op X2 X0) X2 x X1
       have i₂ := eq9 X0 X2 x
       grind)
    | exact superpose eq9 eq63
    | exact resolve eq63 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
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
  have eq101 : ∀ X0 X2 X3 : G, (M.op X0 (M.op (M.op X2 (M.op X2 X0)) (M.op (M.op X2 (M.op X2 X0)) X3))) = X3 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq84 X3 (M.op x X2) (M.op X2 (M.op X2 X0))
       have i₂ := eq84 X0 x X2
       grind)
    | exact superpose eq84 eq84
    | exact resolve eq84 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X1) X2) = (M.op (M.op X3 X1) (M.op X1 (M.op (M.op X0 X1) (M.op X1 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq84 (M.op (M.op X4 X1) X2) X3 X1
       have i₂ := eq63 X2 X1 X4 X0
       grind)
    | exact superpose eq63 eq84
    | exact resolve eq84 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 X0)) = (M.op (M.op X1 (M.op X2 X3)) (M.op (M.op X2 X3) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq84 (M.op X3 (M.op X3 X0)) X1 (M.op X2 X3)
       have i₂ := eq84 X0 X2 X3
       grind)
    | exact superpose eq84 eq84
    | exact resolve eq84 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 X1 X3 : G, (M.op (M.op X1 (M.op X1 X0)) (M.op X0 (M.op (M.op X1 (M.op X1 X0)) X3))) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq9 X3 (M.op X1 (M.op X1 X0)) (M.op x X1)
       have i₂ := eq84 X0 x X1
       grind)
    | exact superpose eq84 eq9
    | exact resolve eq9 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X0)) = (M.op (M.op X1 X2) (M.op (M.op X3 (M.op X1 X2)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op X2 X0)) (M.op X1 X2) X3
       have i₂ := eq84 X0 X1 X2
       grind)
    | exact superpose eq84 eq9
    | exact resolve eq9 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X1 X2 X3 X4 : G, (M.op (M.op X3 X1) X2) = (M.op (M.op X4 X1) X2) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq103 x X1 X2 X4 X3
       have i₂ := eq9 X2 X1 x
       grind)
    | exact superpose eq9 eq103
    | exact resolve eq103 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq149 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq14 (M.op (M.op X1 X1) X0) X1
       have r₂ := eq12 X0 (M.op X1 X1)
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X1) (M.op (M.op X0 X1) (M.op (M.op X2 (M.op X3 X1)) X4))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq86 (M.op X3 X1) X2 X4
       have i₂ := eq116 X1 (M.op (M.op X2 (M.op X3 X1)) X4) X3 X0
       grind)
    | (have i₁ := eq86 (M.op X3 X1) X2 X4
       have i₂ := eq116 X1 (M.op (M.op X2 (M.op X3 X1)) X4) X0 X3
       grind)
    | exact superpose eq116 eq86
    | exact resolve eq86 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq200 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 (M.op X2 X1)) (M.op (M.op X0 X1) (M.op (M.op X2 X1) X3))) = X3 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq84 X3 X4 (M.op X2 X1)
       have i₂ := eq116 X1 (M.op (M.op X2 X1) X3) X2 X0
       grind)
    | (have i₁ := eq84 X3 X4 (M.op X2 X1)
       have i₂ := eq116 X1 (M.op (M.op X2 X1) X3) X0 X2
       grind)
    | exact superpose eq116 eq84
    | exact resolve eq84 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq230 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq149 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq149
    | (have j0 := eq149 (σ X0) (σ X1)
       grind)
    | exact resolve eq149 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq355 : ∀ X0 X1 : G, (k (M.op X0 (M.op (M.op X1 X0) X0)) (M.op X0 X0)) = (M.op (M.op X0 (M.op (M.op X1 X0) X0)) (M.op X0 (M.op (M.op X1 X0) X0))) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 (M.op (M.op X1 X0) X0))) := by
    intro X0 X1
    grind
  have eq365 : ∀ X0 : G, (M.op X0 (k (M.op X0 X0) X0)) = X0 ∨ (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    grind
  have eq374 : ∀ X0 : G, (M.op X0 X0) ≠ (k (M.op X0 X0) X0) ∨ (k (M.op X0 X0) X0) = (k (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    grind
  have eq840 : ∀ X0 X1 : G, (k (M.op X0 X0) X0) = (M.op (M.op X1 X0) (M.op X0 X0)) ∨ (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq84 (k (M.op X0 X0) X0) X1 X0
       have i₂ := eq365 X0
       grind)
    | exact superpose eq365 eq84
    | (have j1 := eq365 X0
       grind)
    | exact resolve eq84 eq365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365
  have eq1487 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 (M.op X1 X2)) (M.op (M.op X0 (M.op X1 X2)) X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq101 X2 X1 X3
       have i₂ := eq116 (M.op X1 X2) X3 X1 X0
       grind)
    | (have i₁ := eq101 X2 X1 X3
       have i₂ := eq116 (M.op X1 X2) X3 X0 X1
       grind)
    | exact superpose eq116 eq101
    | exact resolve eq101 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq1602 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X1 X2)) = (M.op (M.op X3 (M.op X4 X1)) (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq105 X2 X3 X4 X1
       have i₂ := eq116 X1 X2 X4 X0
       grind)
    | (have i₁ := eq105 X2 X3 X4 X1
       have i₂ := eq116 X1 X2 X0 X4
       grind)
    | exact superpose eq116 eq105
    | exact resolve eq105 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq1715 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X1 X2)) (M.op X2 (M.op (M.op X0 (M.op X1 X2)) X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq109 X2 X1 X3
       have i₂ := eq116 (M.op X1 X2) X3 X1 X0
       grind)
    | (have i₁ := eq109 X2 X1 X3
       have i₂ := eq116 (M.op X1 X2) X3 X0 X1
       grind)
    | exact superpose eq116 eq109
    | exact resolve eq109 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq1814 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq230 X1 X0
       have i₂ := eq149 X1 X0
       grind)
    | exact superpose eq149 eq230
    | (have j0 := eq230 X1 X0
       have j1 := eq149 (σ X1) (σ X0)
       grind)
    | exact resolve eq230 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1843 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq230 X1 X0
       grind)
    | exact superpose eq230 eq10
    | (have j1 := eq230 X1 X0
       grind)
    | exact resolve eq10 eq230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230
  have eq1960 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op (M.op X2 (M.op X3 X1)) X4)) = (M.op X1 (M.op X1 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq110 X4 X3 X1 X2
       have i₂ := eq116 X1 (M.op (M.op X2 (M.op X3 X1)) X4) X3 X0
       grind)
    | (have i₁ := eq110 X4 X3 X1 X2
       have i₂ := eq116 X1 (M.op (M.op X2 (M.op X3 X1)) X4) X0 X3
       grind)
    | exact superpose eq116 eq110
    | exact resolve eq110 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq2933 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X1 (M.op X2 X3)) X0) = (M.op (M.op X5 (M.op X4 X3)) X0) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq200 X4 X3 X2 (M.op (M.op X5 (M.op X4 X3)) X0) X1
       have i₂ := eq197 X2 X3 X5 X4 X0
       grind)
    | exact superpose eq197 eq200
    | exact resolve eq200 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197 eq200
  have eq4101 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X0 (M.op X1 X2)) (M.op (M.op X3 (M.op X1 X2)) X4))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1487 X3 X1 X2 X4
       have i₂ := eq116 (M.op X1 X2) (M.op (M.op X3 (M.op X1 X2)) X4) X1 X0
       grind)
    | (have i₁ := eq1487 X3 X1 X2 X4
       have i₂ := eq116 (M.op X1 X2) (M.op (M.op X3 (M.op X1 X2)) X4) X0 X1
       grind)
    | exact superpose eq116 eq1487
    | exact resolve eq1487 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1487
  have eq5348 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X0) X0)) ≠ (k (M.op X0 (M.op (M.op X1 X0) X0)) (M.op X0 X0)) ∨ (k (M.op X0 (M.op (M.op X1 X0) X0)) (M.op X0 X0)) = (k (M.op X0 (M.op (M.op X1 X0) X0)) (M.op X0 (M.op (M.op X1 X0) X0))) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 (M.op (M.op X1 X0) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq374 (M.op X0 X0)
       have i₂ := eq63 X0 X0 x X0
       grind)
    | exact superpose eq63 eq374
    | exact resolve eq374 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374
  have eq5446 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 (M.op X1 X2)) (M.op X2 (M.op (M.op X3 (M.op X4 X2)) X5))) = X5 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq1715 X3 X4 X2 X5
       have i₂ := eq2933 (M.op X2 (M.op (M.op X3 (M.op X4 X2)) X5)) X4 X4 X2 X1 X0
       grind)
    | (have i₁ := eq1715 X3 X4 X2 X5
       have i₂ := eq2933 (M.op X2 (M.op (M.op X3 (M.op X4 X2)) X5)) X0 X1 X2 X4 X4
       grind)
    | exact superpose eq2933 eq1715
    | exact resolve eq1715 eq2933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1715 eq2933
  have eq7566 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X2 (M.op (M.op X0 (M.op X1 X2)) X3)) = (M.op (M.op X4 X2) (M.op X2 (M.op (M.op X5 (M.op X1 X2)) (M.op (M.op X6 (M.op X1 X2)) (M.op (M.op X1 X2) X3))))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq63 (M.op (M.op X5 (M.op X1 X2)) (M.op (M.op X6 (M.op X1 X2)) (M.op (M.op X1 X2) X3))) X2 X1 X4
       have i₂ := eq74 X3 X0 (M.op X1 X2) X6 X5
       grind)
    | exact superpose eq74 eq63
    | exact resolve eq63 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7820 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X0 (M.op X1 X2)) X3)) = (M.op (M.op X4 X2) (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq7566 X0 X1 X2 X3 X4 x x
       have i₂ := eq4101 x X1 X2 x (M.op (M.op X1 X2) X3)
       grind)
    | exact superpose eq4101 eq7566
    | exact resolve eq7566 eq4101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4101 eq7566
  have eq15407 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X5 X1) (M.op (M.op X0 X1) X2)) = (M.op X1 (M.op (M.op X3 (M.op X4 X1)) X2)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq7820 X3 X4 X1 X2 X5
       have i₂ := eq116 X1 X2 X4 X0
       grind)
    | (have i₁ := eq7820 X3 X4 X1 X2 X5
       have i₂ := eq116 X1 X2 X0 X4
       grind)
    | exact superpose eq116 eq7820
    | exact resolve eq7820 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15526 : ∀ X0 X1 X2 X3 X5 : G, (M.op X0 (M.op X0 (M.op (M.op X1 (M.op X2 X0)) (M.op X0 X3)))) = (M.op (M.op X5 X0) X3) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq74 X3 X5 X0 X2 x
       have i₂ := eq7820 X1 X2 X0 (M.op X0 X3) x
       grind)
    | exact superpose eq7820 eq74
    | exact resolve eq74 eq7820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq7820
  have eq20532 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 X1) (M.op (M.op X0 X1) X2)) = (M.op (M.op X4 (M.op X5 X1)) (M.op X1 X2)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq84 (M.op (M.op X4 (M.op X5 X1)) (M.op X1 X2)) X3 X1
       have i₂ := eq15526 X1 X4 X5 X2 X0
       grind)
    | exact superpose eq15526 eq84
    | exact resolve eq84 eq15526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15526
  have eq26047 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1814 x y
       grind)
    | exact superpose eq1814 eq16
    | (have j1 := eq1814 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1814 x y
       grind)
    | exact resolve eq16 eq1814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1814
  have eq26135 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq26047
  have eq26157 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1843 x x
       have i₂ := eq26135
       grind)
    | exact superpose eq26135 eq1843
    | exact resolve eq1843 eq26135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1843
  have eq26173 : (σ x) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 (σ x) (σ x)
       have i₂ := eq26135
       grind)
    | exact superpose eq26135 eq12
    | exact resolve eq12 eq26135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26135
  have eq26233 : (σ x) ≠ (σ y) ∨ (σ y) = (σ (k x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq26173
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq26173
    | exact resolve eq26173 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26173
  have eq26243 : y = (k x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq26157
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq26157
    | exact resolve eq26157 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26157
  have eq62623 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 (M.op X4 X0)) (M.op X0 (M.op (M.op X1 X0) X2))) = (M.op X0 (M.op X0 (M.op X0 X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq76 X0 X1 X2 X3 X4 x
       have i₂ := eq1960 X4 X0 x X4 (M.op X0 X2)
       grind)
    | exact superpose eq1960 eq76
    | exact resolve eq76 eq1960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq154344 : ∀ X0 X1 : G, (k (M.op X0 (M.op (M.op X1 X0) X0)) (M.op X0 X0)) = (M.op X0 (M.op X0 (M.op X0 X0))) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 (M.op (M.op X1 X0) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq355 X0 X1
       have i₂ := eq62623 X0 X1 X0 X0 (M.op X1 X0)
       grind)
    | exact superpose eq62623 eq355
    | (have j0 := eq355 X0 X1
       grind)
    | exact resolve eq355 eq62623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355 eq62623
  have eq170471 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X0) X0)) ≠ (M.op X0 (M.op X0 (M.op X0 X0))) ∨ (k (M.op X0 (M.op (M.op X1 X0) X0)) (M.op X0 X0)) = (k (M.op X0 (M.op (M.op X1 X0) X0)) (M.op X0 (M.op (M.op X1 X0) X0))) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 (M.op (M.op X1 X0) X0))) := by
    intro X0 X1
    first
    | exact superpose eq154344 eq5348
    | (have j0 := eq5348 X0 X1
       have j1 := eq154344 X0 X1
       grind)
    | exact resolve eq5348 eq154344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5348
  have eq170472 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X0) X0)) ≠ (M.op X0 (M.op X0 (M.op X0 X0))) ∨ (M.op X0 (M.op X0 (M.op X0 X0))) = (k (M.op X0 (M.op (M.op X1 X0) X0)) (M.op X0 (M.op (M.op X1 X0) X0))) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 (M.op (M.op X1 X0) X0))) := by
    intro X0 X1
    first
    | exact superpose eq154344 eq170471
    | (have j0 := eq170471 X0 X1
       have j1 := eq154344 X0 X1
       grind)
    | exact resolve eq170471 eq154344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154344 eq170471
  have eq170629 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X3 X2) X2) (M.op (M.op X4 (M.op (M.op X3 X2) X2)) (M.op (M.op X3 X2) X2))) ≠ (M.op (M.op (M.op X3 X2) X2) (M.op (M.op (M.op X3 X2) X2) (M.op (M.op X0 (M.op X1 X2)) (M.op X2 X2)))) ∨ (M.op (M.op (M.op X3 X2) X2) (M.op (M.op (M.op X3 X2) X2) (M.op (M.op X0 (M.op X1 X2)) (M.op X2 X2)))) = (k (M.op (M.op (M.op X3 X2) X2) (M.op (M.op X4 (M.op (M.op X3 X2) X2)) (M.op (M.op X3 X2) X2))) (M.op (M.op (M.op X3 X2) X2) (M.op (M.op X4 (M.op (M.op X3 X2) X2)) (M.op (M.op X3 X2) X2)))) ∨ (M.op (M.op X0 (M.op X1 X2)) (M.op X2 X2)) = (M.op (M.op (M.op X0 (M.op X1 X2)) (M.op X2 X2)) (M.op (M.op (M.op X3 X2) X2) (M.op (M.op X4 (M.op (M.op X3 X2) X2)) (M.op (M.op X3 X2) X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq170472 (M.op (M.op X0 X2) X2) X1
       have i₂ := eq20532 X0 X2 X2 (M.op X0 X2) X4 x
       grind)
    | exact superpose eq20532 eq170472
    | exact resolve eq170472 eq20532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20532 eq170472
  have eq170781 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X3 X2) X2) (M.op (M.op X4 (M.op (M.op X3 X2) X2)) (M.op (M.op X3 X2) X2))) ≠ (M.op (M.op (M.op X3 X2) X2) (M.op X2 (M.op X2 (M.op X2 X2)))) ∨ (M.op (M.op (M.op X3 X2) X2) (M.op (M.op (M.op X3 X2) X2) (M.op (M.op X0 (M.op X1 X2)) (M.op X2 X2)))) = (k (M.op (M.op (M.op X3 X2) X2) (M.op (M.op X4 (M.op (M.op X3 X2) X2)) (M.op (M.op X3 X2) X2))) (M.op (M.op (M.op X3 X2) X2) (M.op (M.op X4 (M.op (M.op X3 X2) X2)) (M.op (M.op X3 X2) X2)))) ∨ (M.op (M.op X0 (M.op X1 X2)) (M.op X2 X2)) = (M.op (M.op (M.op X0 (M.op X1 X2)) (M.op X2 X2)) (M.op (M.op (M.op X3 X2) X2) (M.op (M.op X4 (M.op (M.op X3 X2) X2)) (M.op (M.op X3 X2) X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq170629 X0 X1 X2 X3 X4
       have i₂ := eq1960 (M.op X3 X2) X2 X0 X1 (M.op X2 X2)
       grind)
    | exact superpose eq1960 eq170629
    | (have j0 := eq170629 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq170629 eq1960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170629
  have eq170975 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X2) ≠ (M.op (M.op (M.op X3 X2) X2) (M.op (M.op X4 (M.op (M.op X3 X2) X2)) (M.op (M.op X3 X2) X2))) ∨ (M.op (M.op (M.op X3 X2) X2) (M.op (M.op (M.op X3 X2) X2) (M.op (M.op X0 (M.op X1 X2)) (M.op X2 X2)))) = (k (M.op (M.op (M.op X3 X2) X2) (M.op (M.op X4 (M.op (M.op X3 X2) X2)) (M.op (M.op X3 X2) X2))) (M.op (M.op (M.op X3 X2) X2) (M.op (M.op X4 (M.op (M.op X3 X2) X2)) (M.op (M.op X3 X2) X2)))) ∨ (M.op (M.op X0 (M.op X1 X2)) (M.op X2 X2)) = (M.op (M.op (M.op X0 (M.op X1 X2)) (M.op X2 X2)) (M.op (M.op (M.op X3 X2) X2) (M.op (M.op X4 (M.op (M.op X3 X2) X2)) (M.op (M.op X3 X2) X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq170781 X0 X1 X2 X3 X4
       have i₂ := eq84 (M.op X2 X2) (M.op X3 X2) X2
       grind)
    | exact superpose eq84 eq170781
    | (have j0 := eq170781 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq170781 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170781
  have eq171163 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X2) ≠ (M.op X2 (M.op X2 (M.op (M.op X3 X2) X2))) ∨ (M.op (M.op (M.op X3 X2) X2) (M.op (M.op (M.op X3 X2) X2) (M.op (M.op X0 (M.op X1 X2)) (M.op X2 X2)))) = (k (M.op (M.op (M.op X3 X2) X2) (M.op (M.op X4 (M.op (M.op X3 X2) X2)) (M.op (M.op X3 X2) X2))) (M.op (M.op (M.op X3 X2) X2) (M.op (M.op X4 (M.op (M.op X3 X2) X2)) (M.op (M.op X3 X2) X2)))) ∨ (M.op (M.op X0 (M.op X1 X2)) (M.op X2 X2)) = (M.op (M.op (M.op X0 (M.op X1 X2)) (M.op X2 X2)) (M.op (M.op (M.op X3 X2) X2) (M.op (M.op X4 (M.op (M.op X3 X2) X2)) (M.op (M.op X3 X2) X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq170975 X0 X1 X2 X3 X4
       have i₂ := eq1960 (M.op X3 X2) X2 X4 (M.op X3 X2) (M.op (M.op X3 X2) X2)
       grind)
    | exact superpose eq1960 eq170975
    | (have j0 := eq170975 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq170975 eq1960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170975
  have eq171343 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X2) ≠ X2 ∨ (M.op (M.op (M.op X3 X2) X2) (M.op (M.op (M.op X3 X2) X2) (M.op (M.op X0 (M.op X1 X2)) (M.op X2 X2)))) = (k (M.op (M.op (M.op X3 X2) X2) (M.op (M.op X4 (M.op (M.op X3 X2) X2)) (M.op (M.op X3 X2) X2))) (M.op (M.op (M.op X3 X2) X2) (M.op (M.op X4 (M.op (M.op X3 X2) X2)) (M.op (M.op X3 X2) X2)))) ∨ (M.op (M.op X0 (M.op X1 X2)) (M.op X2 X2)) = (M.op (M.op (M.op X0 (M.op X1 X2)) (M.op X2 X2)) (M.op (M.op (M.op X3 X2) X2) (M.op (M.op X4 (M.op (M.op X3 X2) X2)) (M.op (M.op X3 X2) X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq171163 X0 X1 X2 X3 X4
       have i₂ := eq86 X2 X3 X2
       grind)
    | exact superpose eq86 eq171163
    | (have j0 := eq171163 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq171163 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171163
  have eq171498 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X3 X2) X2) (M.op (M.op (M.op X3 X2) X2) (M.op (M.op X0 (M.op X1 X2)) (M.op X2 X2)))) = (k (M.op X2 (M.op X2 (M.op (M.op X3 X2) X2))) (M.op X2 (M.op X2 (M.op (M.op X3 X2) X2)))) ∨ (M.op X2 X2) ≠ X2 ∨ (M.op (M.op X0 (M.op X1 X2)) (M.op X2 X2)) = (M.op (M.op (M.op X0 (M.op X1 X2)) (M.op X2 X2)) (M.op (M.op (M.op X3 X2) X2) (M.op (M.op X4 (M.op (M.op X3 X2) X2)) (M.op (M.op X3 X2) X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq171343 X0 X1 X1 X3 X2
       have i₂ := eq1960 (M.op X3 X1) X1 X2 (M.op X3 X1) (M.op (M.op X3 X1) X1)
       grind)
    | exact superpose eq1960 eq171343
    | (have j0 := eq171343 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq171343 eq1960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171343
  have eq171634 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X3 X2) X2) (M.op (M.op (M.op X3 X2) X2) (M.op (M.op X0 (M.op X1 X2)) (M.op X2 X2)))) = (k X2 X2) ∨ (M.op X2 X2) ≠ X2 ∨ (M.op (M.op X0 (M.op X1 X2)) (M.op X2 X2)) = (M.op (M.op (M.op X0 (M.op X1 X2)) (M.op X2 X2)) (M.op (M.op (M.op X3 X2) X2) (M.op (M.op X4 (M.op (M.op X3 X2) X2)) (M.op (M.op X3 X2) X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq171498 X0 X1 X2 X1 X4
       have i₂ := eq86 X2 X1 X2
       grind)
    | exact superpose eq86 eq171498
    | (have j0 := eq171498 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq171498 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171498
  have eq171725 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X3 X2) X2) (M.op X2 (M.op X2 (M.op X2 X2)))) = (k X2 X2) ∨ (M.op X2 X2) ≠ X2 ∨ (M.op (M.op X0 (M.op X1 X2)) (M.op X2 X2)) = (M.op (M.op (M.op X0 (M.op X1 X2)) (M.op X2 X2)) (M.op (M.op (M.op X3 X2) X2) (M.op (M.op X4 (M.op (M.op X3 X2) X2)) (M.op (M.op X3 X2) X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq171634 X0 X1 X2 X3 X4
       have i₂ := eq1960 (M.op X3 X2) X2 X0 X1 (M.op X2 X2)
       grind)
    | exact superpose eq1960 eq171634
    | (have j0 := eq171634 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq171634 eq1960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1960 eq171634
  have eq171788 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X2) = (k X2 X2) ∨ (M.op X2 X2) ≠ X2 ∨ (M.op (M.op X0 (M.op X1 X2)) (M.op X2 X2)) = (M.op (M.op (M.op X0 (M.op X1 X2)) (M.op X2 X2)) (M.op (M.op (M.op X3 X2) X2) (M.op (M.op X4 (M.op (M.op X3 X2) X2)) (M.op (M.op X3 X2) X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq171725 X0 X1 X2 X3 X4
       have i₂ := eq84 (M.op X2 X2) (M.op X3 X2) X2
       grind)
    | exact superpose eq84 eq171725
    | (have j0 := eq171725 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq171725 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq171725
  have eq171836 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X2) = (k X2 X2) ∨ (M.op (M.op X0 (M.op X1 X2)) (M.op X2 X2)) = (M.op (M.op (M.op X0 (M.op X1 X2)) (M.op X2 X2)) (M.op (M.op (M.op X3 X2) X2) (M.op (M.op X4 (M.op (M.op X3 X2) X2)) (M.op (M.op X3 X2) X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have j0 := eq171788 X0 X1 X2 X3 X4
       have j1 := eq149 X2 X2
       grind)
    | (have r₁ := eq171788 X0 X1 X0 X3 X4
       have r₂ := eq149 X0 X0
       grind)
    | (have r₁ := eq171788 X0 X1 (M.op X1 X1) X3 X4
       have r₂ := eq149 (M.op (M.op X1 X1) (M.op X1 X1)) X1
       grind)
    | exact resolve eq171788 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171788
  have eq171864 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 X2)) (M.op X2 X2)) = (M.op X2 (M.op X2 (M.op (M.op X4 (M.op (M.op X3 X2) X2)) (M.op (M.op X3 X2) X2)))) ∨ (M.op X2 X2) = (k X2 X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq171836 X0 X1 X2 X3 X4
       have i₂ := eq1602 (M.op X3 X2) X2 (M.op (M.op X4 (M.op (M.op X3 X2) X2)) (M.op (M.op X3 X2) X2)) (M.op X0 (M.op X1 X2)) X2
       grind)
    | exact superpose eq1602 eq171836
    | (have j0 := eq171836 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq171836 eq1602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171836
  have eq171883 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X2)) (M.op X2 X2)) = (M.op X2 (M.op X2 (M.op X2 (M.op X2 X2)))) ∨ (M.op X2 X2) = (k X2 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq171864 X0 X1 X2 x x
       have i₂ := eq1602 x X2 X2 x (M.op x X2)
       grind)
    | exact superpose eq1602 eq171864
    | (have j0 := eq171864 X0 X1 X2 x x
       grind)
    | exact resolve eq171864 eq1602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171864
  have eq171899 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X2)) X2) = (M.op X2 (M.op X2 (M.op X2 X2))) ∨ (M.op X2 X2) = (k X2 X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq149 eq171883
    | (have j0 := eq171883 X0 X1 X2
       have j1 := eq149 X2 X2
       grind)
    | exact resolve eq171883 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171883
  have eq171909 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X2)) = (M.op (M.op X0 (M.op X1 X2)) X2) ∨ (M.op X2 X2) = (k X2 X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq149 eq171899
    | (have j0 := eq171899 X0 X1 X2
       have j1 := eq149 X2 X2
       grind)
    | exact resolve eq171899 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171899
  have eq171917 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X0 (M.op X1 X2)) X2) ∨ (M.op X2 X2) = (k X2 X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq149 eq171909
    | (have j0 := eq171909 X0 X1 X2
       have j1 := eq149 X2 X2
       grind)
    | exact resolve eq171909 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171909
  have eq171925 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X2)) X2) = X2 ∨ (M.op X2 X2) = (k X2 X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq149 eq171917
    | (have j0 := eq171917 X0 X1 X2
       have j1 := eq149 X2 X2
       grind)
    | exact resolve eq171917 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171917
  have eq172253 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq840 X0 (M.op x (M.op x X0))
       have i₂ := eq171925 x x X0
       grind)
    | exact superpose eq171925 eq840
    | (have j0 := eq840 X0 x
       have j1 := eq171925 X0 x X0
       grind)
    | exact resolve eq840 eq171925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq840 eq171925
  have eq172550 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq172253 X0
       have j1 := eq12 (M.op X0 X0) X0
       grind)
    | (have r₁ := eq172253 x
       have r₂ := eq12 (M.op x x) x
       grind)
    | exact resolve eq172253 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172253
  have eq172779 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | exact superpose eq149 eq172550
    | (have j0 := eq172550 X0
       have j1 := eq149 X0 X0
       grind)
    | exact resolve eq172550 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149 eq172550
  have eq172780 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq172779 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172779
  have eq173044 : (σ y) = (σ (M.op x x)) ∨ (σ x) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq26233
       have i₂ := eq172780 x
       grind)
    | exact superpose eq172780 eq26233
    | exact resolve eq26233 eq172780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26233
  have eq173045 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq26243
       have i₂ := eq172780 x
       grind)
    | exact superpose eq172780 eq26243
    | exact resolve eq26243 eq172780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26243
  have eq173081 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq172780 (σ X0)
       grind)
    | exact superpose eq172780 eq15
    | exact resolve eq15 eq172780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq173095 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq172780 (τ X0)
       grind)
    | exact superpose eq172780 eq32
    | exact resolve eq32 eq172780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq173112 : y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq173045
  have eq173129 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq173095 X0
       have i₂ := eq172780 X0
       grind)
    | exact superpose eq172780 eq173095
    | exact resolve eq173095 eq172780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173095
  have eq173143 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq173081 X0
       have i₂ := eq172780 X0
       grind)
    | exact superpose eq172780 eq173081
    | exact resolve eq173081 eq172780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172780 eq173081
  have eq173176 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq173044
       have r₂ := eq173112
       grind)
    | exact resolve eq173044 eq173112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173044
  have eq173510 : ∀ X0 X1 : G, (M.op (τ X0) (M.op (τ (M.op X0 X0)) (M.op (τ X0) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (τ X0) (τ X0)
       have i₂ := eq173129 X0
       grind)
    | exact superpose eq173129 eq9
    | exact resolve eq9 eq173129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq173511 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (M.op (M.op X1 (τ X0)) (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (τ X0) (τ X0) X1
       have i₂ := eq173129 X0
       grind)
    | exact superpose eq173129 eq9
    | exact resolve eq9 eq173129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq173535 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (τ X0)) X1) = (M.op (τ (M.op X0 X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq116 (τ X0) X1 (τ X0) X2
       have i₂ := eq173129 X0
       grind)
    | exact superpose eq173129 eq116
    | exact resolve eq116 eq173129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq174121 : (σ x) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq173112 eq173176
    | exact resolve eq173176 eq173112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173176
  have eq174122 : (M.op x x) = (τ (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq174121
       grind)
    | exact superpose eq174121 eq10
    | exact resolve eq10 eq174121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174121
  have eq174242 : y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq174122
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq174122
    | exact resolve eq174122 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174122
  have eq186790 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq173510 X0 (τ X0)
       have i₂ := eq173129 X0
       grind)
    | exact superpose eq173129 eq173510
    | exact resolve eq173510 eq173129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173510
  have eq187078 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq186790 X0
       have i₂ := eq173129 (M.op X0 X0)
       grind)
    | exact superpose eq173129 eq186790
    | exact resolve eq186790 eq173129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186790
  have eq190510 : ∀ X0 X1 X2 X3 : G, (τ (M.op (M.op X3 X0) X0)) = (M.op (τ (M.op (M.op X3 X0) X0)) (τ (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X0)) X0)) (M.op X0 (M.op (M.op X1 (M.op X2 X0)) X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq187078 (M.op (M.op X0 X2) X2)
       have i₂ := eq15407 X0 X2 X2 X3 x (M.op X0 X2)
       grind)
    | exact superpose eq15407 eq187078
    | exact resolve eq187078 eq15407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15407 eq187078
  have eq190726 : ∀ X0 X3 : G, (τ (M.op (M.op X3 X0) X0)) = (M.op (τ (M.op (M.op X3 X0) X0)) (τ X0)) := by
    intro X0 X3
    first
    | (have i₁ := eq190510 X0 x x X3
       have i₂ := eq5446 X0 (M.op x (M.op x X0)) X0 x x X0
       grind)
    | exact superpose eq5446 eq190510
    | exact resolve eq190510 eq5446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5446 eq190510
  have eq194732 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (M.op (M.op X1 (τ X0)) (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have j0 := eq173511 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173511
  have eq195808 : ∀ X0 X1 : G, (τ X1) = (M.op (M.op X0 (τ X1)) (M.op (τ X1) (τ (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq194732 X1 x
       have i₂ := eq63 (τ (M.op X1 X1)) (τ X1) x X0
       grind)
    | exact superpose eq63 eq194732
    | exact resolve eq194732 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq194732
  have eq234769 : ∀ X0 X1 X2 : G, (M.op (τ (M.op X1 X1)) X2) = (M.op (τ (M.op (M.op X0 X1) X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq173535 X1 X2 (τ (M.op (M.op X0 X1) X1))
       have i₂ := eq190726 X1 X0
       grind)
    | exact superpose eq190726 eq173535
    | exact resolve eq173535 eq190726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq236887 : ∀ X0 X3 : G, (τ (M.op (M.op X3 X0) X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0 X3
    first
    | (have i₁ := eq190726 X0 X3
       have i₂ := eq234769 X3 X0 (τ X0)
       grind)
    | exact superpose eq234769 eq190726
    | exact resolve eq190726 eq234769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190726 eq234769
  have eq238697 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (τ X1)) (τ X1)) = (τ (M.op (M.op X2 X1) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq236887 X1 X2
       have i₂ := eq173535 X1 (τ X1) X0
       grind)
    | exact superpose eq173535 eq236887
    | exact resolve eq236887 eq173535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173535 eq236887
  have eq240089 : ∀ X0 X1 X2 X3 X4 : G, (τ (M.op (M.op X4 (M.op (M.op X3 X1) X1)) (M.op (M.op X3 X1) X1))) = (M.op (M.op X2 (M.op (M.op X0 (τ X1)) (τ X1))) (M.op (M.op X0 (τ X1)) (τ X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq238697 X0 (M.op (M.op X2 X1) X1) X2
       have i₂ := eq238697 X0 X1 X2
       grind)
    | exact superpose eq238697 eq238697
    | exact resolve eq238697 eq238697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238697
  have eq240818 : ∀ X1 X3 X4 : G, (M.op (τ X1) (M.op (τ X1) (τ X1))) = (τ (M.op (M.op X4 (M.op (M.op X3 X1) X1)) (M.op (M.op X3 X1) X1))) := by
    intro X1 X3 X4
    first
    | (have i₁ := eq240089 x X1 x X3 X4
       have i₂ := eq1602 x (τ X1) (τ X1) x (M.op x (τ X1))
       grind)
    | exact superpose eq1602 eq240089
    | exact resolve eq240089 eq1602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240089
  have eq240909 : ∀ X1 : G, (M.op (τ X1) (M.op (τ X1) (τ X1))) = (τ (M.op X1 (M.op X1 X1))) := by
    intro X1
    first
    | (have i₁ := eq240818 X1 x x
       have i₂ := eq1602 x X1 X1 x (M.op x X1)
       grind)
    | exact superpose eq1602 eq240818
    | exact resolve eq240818 eq1602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1602 eq240818
  have eq240963 : ∀ X1 : G, (M.op (τ X1) (τ (M.op X1 X1))) = (τ (M.op X1 (M.op X1 X1))) := by
    intro X1
    first
    | (have i₁ := eq240909 X1
       have i₂ := eq173129 X1
       grind)
    | exact superpose eq173129 eq240909
    | exact resolve eq240909 eq173129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173129 eq240909
  have eq250243 : ∀ X0 X1 : G, (τ X1) = (M.op (M.op X0 (τ X1)) (τ (M.op X1 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq195808 X0 X1
       have i₂ := eq240963 X1
       grind)
    | exact superpose eq240963 eq195808
    | exact resolve eq195808 eq240963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195808 eq240963
  have eq250676 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (τ (M.op (σ X0) (M.op (σ X0) (σ X0))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq250243 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq250243
    | exact resolve eq250243 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250243
  have eq251220 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (τ (M.op (σ X0) (σ (M.op X0 X0))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq250676 X0 X1
       have i₂ := eq173143 X0
       grind)
    | exact superpose eq173143 eq250676
    | exact resolve eq250676 eq173143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250676
  have eq251647 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (τ (M.op (σ X0) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq86 X0 x (τ (M.op (σ X0) (σ (M.op X0 X0))))
       have i₂ := eq251220 X0 x
       grind)
    | exact superpose eq251220 eq86
    | exact resolve eq86 eq251220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq251220
  have eq252279 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ (M.op X0 X0)))
       have i₂ := eq251647 X0
       grind)
    | exact superpose eq251647 eq11
    | exact resolve eq11 eq251647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251647
  have eq252945 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq252279 x
       have i₂ := eq173112
       grind)
    | exact superpose eq173112 eq252279
    | exact resolve eq252279 eq173112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173112 eq252279
  have eq253165 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq252945
       have r₂ := eq16
       grind)
    | exact resolve eq252945 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252945
  have eq253279 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq253165
       grind)
    | exact superpose eq253165 eq16
    | exact resolve eq16 eq253165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq253282 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq253165
       grind)
    | exact superpose eq253165 eq10
    | exact resolve eq10 eq253165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253165
  have eq253441 : x = y := by
    first
    | (have i₁ := eq253282
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq253282
    | exact resolve eq253282 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253282
  have eq253444 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq253279
       have i₂ := eq173143 x
       grind)
    | exact superpose eq173143 eq253279
    | exact resolve eq253279 eq173143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173143 eq253279
  have eq253449 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq174242
       have i₂ := eq253441
       grind)
    | exact superpose eq253441 eq174242
    | exact resolve eq174242 eq253441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174242
  have eq253478 : x = (M.op x x) := by grind
  clear eq253449
  have eq253505 : x = (M.op x x) := by grind
  clear eq253478
  have eq253927 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq253444
       have i₂ := eq253505
       grind)
    | exact superpose eq253505 eq253444
    | exact resolve eq253444 eq253505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253444
  have eq253928 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq253927
       have i₂ := eq253441
       grind)
    | exact superpose eq253441 eq253927
    | exact resolve eq253927 eq253441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253441 eq253927
  have eq253929 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq253928
       have i₂ := eq253505
       grind)
    | exact superpose eq253505 eq253928
    | exact resolve eq253928 eq253505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253505 eq253928
  have eq253930 : False := by grind
  exact eq253930

/-- `Equation964`: `x = y ◇ ((z ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = m(X,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pxy_pyx_pxx_pyx_Equation964 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law964 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law964.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X1 X0))) = X0 := by
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
  clear eq36
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
  clear eq37
  have eq87 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y x) = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq72
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq72
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq72 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y x) = (M.op y y) ∨ y = (M.op x x) := by
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
  have eq94 : (M.op y x) = (M.op y y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq93
    | exact resolve eq93 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq109 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq381 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq109 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq109
    | (have j0 := eq109 (σ X0)
       grind)
    | exact resolve eq109 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq385 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq109 x
       grind)
    | exact superpose eq109 eq44
    | (have j1 := eq109 x
       grind)
    | exact resolve eq44 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq6213 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq381 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381
  have eq76469 : ∀ X0 : G, y = (M.op y (M.op (M.op X0 y) (M.op y x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq14 y y X0
       have i₂ := eq94
       grind)
    | exact superpose eq94 eq14
    | exact resolve eq14 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq76641 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq76469 x
       have i₂ := eq14 x y x
       grind)
    | exact superpose eq14 eq76469
    | exact resolve eq76469 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76469
  have eq76753 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq76641 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq76641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76754 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq76753
    | exact resolve eq76753 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76753
  have eq76765 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq76754
       have r₂ := eq28
       grind)
    | exact resolve eq76754 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76754
  have eq76787 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (M.op X0 (σ y)) (M.op (σ y) (σ x)))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq76765 eq14
    | exact resolve eq14 eq76765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76765
  have eq76945 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq76787 x
       have i₂ := eq14 sF2 sF3 x
       grind)
    | exact superpose eq14 eq76787
    | exact resolve eq76787 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76787
  have eq77064 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by grind
  clear eq76945
  have eq77194 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq77064
    | exact resolve eq77064 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77064
  have eq78329 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq77194 eq76641
    | exact resolve eq76641 eq77194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76641 eq77194
  have eq78331 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq78329
  have eq78333 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq78331
       have r₂ := eq28
       grind)
    | exact resolve eq78331 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78331
  have eq79361 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq385
       have i₂ := eq78333
       grind)
    | exact superpose eq78333 eq385
    | exact resolve eq385 eq78333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79382 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq78333
  have eq79480 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq79361
  have eq79516 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq79382
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq79382
    | exact resolve eq79382 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79382
  have eq79522 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq79480
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq79480
    | exact resolve eq79480 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79480
  have eq79580 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq79516
       grind)
    | exact superpose eq79516 eq72
    | exact resolve eq72 eq79516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq79516
  have eq79598 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq79580
    | exact resolve eq79580 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79580
  have eq79599 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq79522
       have i₂ := eq109 sF2
       grind)
    | exact superpose eq109 eq79522
    | (have j1 := eq109 (σ x)
       grind)
    | exact resolve eq79522 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118211 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq79599
  have eq118375 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq118211
    | exact resolve eq118211 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118211
  have eq118433 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq118375 eq79598
    | exact resolve eq79598 eq118375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79598 eq118375
  have eq118435 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq118433
  have eq118445 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq118435
       have r₂ := eq28
       grind)
    | exact resolve eq118435 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118435
  have eq120657 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  have eq121188 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq120657 eq79522
    | exact resolve eq79522 eq120657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79522 eq120657
  have eq121203 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq121188
  have eq121213 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq121203 eq118445
    | exact resolve eq118445 eq121203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118445 eq121203
  have eq121347 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq121213
  have eq122258 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq121347 eq30
    | exact resolve eq30 eq121347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq121347
  have eq122434 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq122258
    | exact resolve eq122258 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq122258
  have eq122435 : x = y := by grind
  clear eq122434
  have eq122436 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq122435
       grind)
    | exact superpose eq122435 eq19
    | exact resolve eq19 eq122435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq122437 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq122435
       grind)
    | exact superpose eq122435 eq25
    | exact resolve eq25 eq122435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq122435
  have eq122611 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq122437
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq122437
    | exact resolve eq122437 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122437
  have eq122612 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq122611 eq27
    | exact resolve eq27 eq122611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq122611
  have eq122795 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq385
       have i₂ := eq122436
       grind)
    | exact superpose eq122436 eq385
    | exact resolve eq385 eq122436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385
  have eq122832 : (M.op x (M.op x y)) = (k (M.op x y) x) := by grind
  have eq123010 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq122795
    | exact resolve eq122795 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122795
  have eq123071 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (σ x)) := by grind
  have eq127295 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq123010 eq109
    | (have j0 := eq109 (σ x)
       grind)
    | exact resolve eq109 eq123010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq127296 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq122612 eq127295
    | exact resolve eq127295 eq122612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127295
  have eq127310 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq127296
       have r₂ := eq28
       grind)
    | exact resolve eq127296 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127296
  have eq127316 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq122612 eq127310
    | exact resolve eq127310 eq122612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127310
  have eq127374 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq127316 eq123071
    | exact resolve eq123071 eq127316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123071 eq127316
  have eq127380 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq122612 eq127374
    | exact resolve eq127374 eq122612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127374
  have eq127959 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq127380 eq123010
    | exact resolve eq123010 eq127380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123010 eq127380
  have eq127964 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq127959
  have eq127967 : x = (M.op x y) := by
    first
    | (have r₁ := eq127964
       have r₂ := eq28
       grind)
    | exact resolve eq127964 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127964
  have eq127978 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq127967 eq21
    | exact resolve eq21 eq127967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq128125 : (k x x) = (M.op x x) := by
    first
    | exact superpose eq127967 eq122832
    | exact resolve eq122832 eq127967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122832
  have eq128133 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq128125
       have i₂ := eq122436
       grind)
    | exact superpose eq122436 eq128125
    | exact resolve eq128125 eq122436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122436 eq128125
  have eq128241 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq127978
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq127978
    | exact resolve eq127978 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127978
  have eq128245 : x = (k x x) := by
    first
    | exact superpose eq127967 eq128133
    | exact resolve eq128133 eq127967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127967 eq128133
  have eq131150 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq6213 x
       have i₂ := eq128245
       grind)
    | exact superpose eq128245 eq6213
    | (have j0 := eq6213 x
       grind)
    | exact resolve eq6213 eq128245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6213 eq128245
  have eq131154 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq131150
  have eq131163 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq131154
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq131154
    | exact resolve eq131154 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq131154
  have eq131176 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq122612 eq131163
    | exact resolve eq131163 eq122612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122612 eq131163
  have eq131187 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq128241 eq131176
    | exact resolve eq131176 eq128241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128241 eq131176
  have eq131196 : False := by grind
  exact eq131196
