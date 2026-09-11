import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pyx_pyy_pxy_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
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
  have eq106 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq106 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq106
    | (have j0 := eq106 (σ X0)
       grind)
    | exact resolve eq106 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq106 (τ X0)
       grind)
    | exact superpose eq106 eq18
    | (have j1 := eq106 (τ X0)
       grind)
    | exact resolve eq18 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq135 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq134 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq134
    | (have j0 := eq134 X0
       grind)
    | exact resolve eq134 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq142 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X1 X1)) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq74 X1 (M.op X0 (M.op X0 X0))
       have i₂ := eq74 X0 X0
       grind)
    | exact superpose eq74 eq74
    | exact resolve eq74 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq154 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 (M.op X2 X2))) = X2 := by
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
  have eq155 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
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
  have eq159 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
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
  have eq214 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq154 X2 X1 (M.op X0 (M.op X0 X0))
       have i₂ := eq154 X0 X0 X0
       grind)
    | exact superpose eq154 eq154
    | exact resolve eq154 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq267 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq159 X2 X3
       have i₂ := eq155 X2 X0 X1
       grind)
    | exact superpose eq155 eq159
    | exact resolve eq159 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq268 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq68 X2
       have i₂ := eq155 X2 X0 X1
       grind)
    | exact superpose eq155 eq68
    | exact resolve eq68 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq269 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X2)) (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq154 X2 X3 X2
       have i₂ := eq155 X2 X0 X1
       grind)
    | exact superpose eq155 eq154
    | exact resolve eq154 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq271 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X0 (M.op (M.op X1 X0) X2)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq84 X2 X2
       have i₂ := eq155 X2 X0 X1
       grind)
    | exact superpose eq155 eq84
    | exact resolve eq84 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq275 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X3 (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 X3) X3 X2
       have i₂ := eq155 (M.op X2 X3) X0 X1
       grind)
    | exact superpose eq155 eq9
    | exact resolve eq9 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq399 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) (M.op (M.op X3 (M.op X0 X0)) (M.op X0 X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq267 (M.op X3 (M.op X0 X0)) (M.op x (M.op X3 X3)) X2 X1
       have i₂ := eq154 X3 x X0
       grind)
    | exact superpose eq154 eq267
    | exact resolve eq267 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq514 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq1005 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq71 X0 (M.op X1 X0) X2 X3
       have i₂ := eq155 X0 X0 X1
       grind)
    | exact superpose eq155 eq71
    | exact resolve eq71 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq1012 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X1 X2))) = (M.op X2 (M.op X0 (M.op X1 X2))) := by
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
  have eq1067 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1005 X0 X1 x x
       have i₂ := eq71 X0 X0 x x
       grind)
    | exact superpose eq71 eq1005
    | exact resolve eq1005 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1005
  have eq1256 : ∀ X0 X1 X2 : G, (M.op (σ X0) (M.op (M.op (σ X0) (σ X1)) (M.op X2 X2))) = X2 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (σ X0) (σ X1)
       have i₂ := eq514 X0 X1
       grind)
    | (have i₁ := eq9 X0 (σ X1) (σ X0)
       have i₂ := eq514 X0 X1
       grind)
    | exact superpose eq514 eq9
    | (have j1 := eq514 X0 X1
       grind)
    | exact resolve eq9 eq514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1257 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq514 X0 X1
       grind)
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq514 X0 X1
       grind)
    | exact superpose eq514 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq514 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq514 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq514 X0 X1
       grind)
    | exact resolve eq13 eq514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514
  have eq1274 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1257 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1257
  have eq1275 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1274 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1274
  have eq1282 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1275 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1275
    | (have j0 := eq1275 X0 X1
       grind)
    | exact resolve eq1275 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1275
  have eq1456 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) (M.op (M.op X3 X0) (M.op (M.op X0 (M.op X0 X0)) X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq267 (M.op X3 X0) (M.op X3 (M.op X3 X3)) X2 X1
       have i₂ := eq142 X0 X3
       grind)
    | exact superpose eq142 eq267
    | exact resolve eq267 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq2031 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op X1 (M.op (M.op X2 X1) X0)))) = (M.op (M.op X3 (M.op (M.op X4 X0) (M.op X4 X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq214 (M.op X1 (M.op (M.op X2 X1) X0)) X3 (M.op X4 X0)
       have i₂ := eq267 X1 X2 X0 X4
       grind)
    | exact superpose eq267 eq214
    | exact resolve eq214 eq267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2183 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op X1 (M.op (M.op X2 X1) X0)))) = (M.op (M.op X3 (M.op X0 (M.op X4 X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2031 X0 X1 X2 X3 X4
       have i₂ := eq63 X4 X0
       grind)
    | exact superpose eq63 eq2031
    | exact resolve eq2031 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2031
  have eq2233 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op (M.op (M.op X2 X1) X0) (M.op X1 (M.op (M.op X2 X1) X0)))) = (M.op (M.op X3 (M.op X0 (M.op X4 X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2183 X0 X1 X2 X3 X4
       have i₂ := eq63 X1 (M.op (M.op X2 X1) X0)
       grind)
    | exact superpose eq63 eq2183
    | exact resolve eq2183 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2183
  have eq2256 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) X0) = (M.op (M.op X3 (M.op X0 (M.op X4 X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2233 X0 X1 X2 X3 X4
       have i₂ := eq267 X1 X2 X0 (M.op X2 X1)
       grind)
    | exact superpose eq267 eq2233
    | exact resolve eq2233 eq267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2233
  have eq2261 : ∀ X0 X3 X4 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 (M.op X4 X0))) X0) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq2256 X0 x x X3 X4
       have i₂ := eq271 x x X0
       grind)
    | exact superpose eq271 eq2256
    | exact resolve eq2256 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271 eq2256
  have eq2280 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X2 (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0)))) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2261 (M.op X1 X0) X2 (M.op x (M.op X1 X1))
       have i₂ := eq214 X0 x X1
       grind)
    | exact superpose eq214 eq2261
    | exact resolve eq2261 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2352 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X2 X0) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2280 X0 X1 X2
       have i₂ := eq159 X0 X1
       grind)
    | exact superpose eq159 eq2280
    | exact resolve eq2280 eq159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2280
  have eq2369 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X0) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2352 X0 X1 X2
       have i₂ := eq63 X1 X0
       grind)
    | exact superpose eq63 eq2352
    | exact resolve eq2352 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq2352
  have eq3435 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X3 X0)) X0) = (M.op (M.op X1 (M.op (M.op (M.op X2 (M.op X3 X0)) X0) (M.op (M.op X2 (M.op X3 X0)) X0))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq269 X0 X3 (M.op (M.op X2 (M.op X3 X0)) X0) X1
       have i₂ := eq268 (M.op X3 X0) X2 X0
       grind)
    | exact superpose eq268 eq269
    | exact resolve eq269 eq268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq3566 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X3 X0)) X0) = (M.op (M.op X1 (M.op X0 (M.op (M.op X2 (M.op X3 X0)) X0))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3435 X0 X1 X2 X3
       have i₂ := eq2369 X0 (M.op X2 (M.op X3 X0)) (M.op X2 (M.op X3 X0))
       grind)
    | exact superpose eq2369 eq3435
    | exact resolve eq3435 eq2369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3435
  have eq3623 : ∀ X0 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X2 (M.op X3 X0)) X0) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq3566 X0 x X2 X3
       have i₂ := eq2261 X0 x (M.op X2 (M.op X3 X0))
       grind)
    | exact superpose eq2261 eq3566
    | exact resolve eq3566 eq2261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2261 eq3566
  have eq4363 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq275 (M.op X1 X1) x X1 (M.op X0 X0)
       have i₂ := eq154 X1 x X0
       grind)
    | exact superpose eq154 eq275
    | exact resolve eq275 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154 eq275
  have eq4487 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4363 X0 X1
       have i₂ := eq2369 X0 (M.op X1 X1) X0
       grind)
    | exact superpose eq2369 eq4363
    | exact resolve eq4363 eq2369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4363
  have eq4528 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = (M.op (M.op X1 X1) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4487 (M.op X1 X0) (M.op X1 X1)
       have i₂ := eq214 X0 (M.op X1 X1) X1
       grind)
    | exact superpose eq214 eq4487
    | exact resolve eq4487 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq4618 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 (M.op X0 X0)) X2) (M.op (M.op X1 (M.op X0 X0)) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq267 (M.op X0 X0) X1 X2 (M.op X1 (M.op X0 X0))
       have i₂ := eq4487 (M.op (M.op X1 (M.op X0 X0)) X2) X0
       grind)
    | exact superpose eq4487 eq267
    | exact resolve eq267 eq4487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4487
  have eq4644 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op (M.op X1 (M.op X0 X0)) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4618 X0 X1 X2
       have i₂ := eq2369 X2 (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X0 X0))
       grind)
    | exact superpose eq2369 eq4618
    | exact resolve eq4618 eq2369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4618
  have eq4686 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = (M.op (M.op X1 X1) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4528 X0 X1
       have i₂ := eq2369 X0 X1 X1
       grind)
    | exact superpose eq2369 eq4528
    | exact resolve eq4528 eq2369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4528
  have eq4724 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4686 X0 X1
       have i₂ := eq159 X0 X1
       grind)
    | exact superpose eq159 eq4686
    | exact resolve eq4686 eq159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159 eq4686
  have eq4799 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4724 (M.op (M.op X2 X1) X0) X1
       have i₂ := eq267 X1 X2 X0 (M.op X2 X1)
       grind)
    | exact superpose eq267 eq4724
    | exact resolve eq4724 eq267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5000 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4799 (M.op X0 (M.op X2 X0)) X2 X1
       have i₂ := eq4724 X0 X2
       grind)
    | exact superpose eq4724 eq4799
    | exact resolve eq4799 eq4724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4724 eq4799
  have eq6192 : ∀ X0 X1 X2 X3 : G, (M.op X3 X0) = (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X2 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq71 X0 (M.op X1 (M.op (M.op X2 X3) (M.op X2 X3))) X3 X2
       have i₂ := eq4644 (M.op X2 X3) X1 X0
       grind)
    | exact superpose eq4644 eq71
    | exact resolve eq71 eq4644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq4644
  have eq6219 : ∀ X0 X1 X2 X3 : G, (M.op X3 X0) = (M.op (M.op X1 (M.op X3 (M.op X2 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6192 X0 X1 X2 X3
       have i₂ := eq2369 X3 X2 X2
       grind)
    | exact superpose eq2369 eq6192
    | exact resolve eq6192 eq2369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6192
  have eq7975 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq127 X0
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq127
    | (have j0 := eq127 X0
       have j1 := eq106 (σ X0)
       grind)
    | exact resolve eq127 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq127
  have eq9673 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X3) (M.op (M.op X4 (M.op X0 X1)) (M.op (M.op X1 (M.op (M.op X0 X1) (M.op X0 X1))) X3))) = X3 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq399 (M.op X1 (M.op (M.op X0 X1) (M.op X0 X1))) X2 X3 X4
       have i₂ := eq269 X1 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq269 eq399
    | exact resolve eq399 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269 eq399
  have eq9916 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X3) (M.op (M.op X4 (M.op X0 X1)) (M.op (M.op X1 (M.op X1 (M.op X0 X1))) X3))) = X3 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9673 X0 X1 X2 X3 X4
       have i₂ := eq2369 X1 X0 X0
       grind)
    | exact superpose eq2369 eq9673
    | exact resolve eq9673 eq2369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2369 eq9673
  have eq9967 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X3) (M.op (M.op X4 (M.op X0 X1)) (M.op X1 X3))) = X3 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9916 X0 X1 X2 X3 X4
       have i₂ := eq6219 X3 X1 X0 X1
       grind)
    | exact superpose eq6219 eq9916
    | exact resolve eq9916 eq6219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6219 eq9916
  have eq10021 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq135 X0
       grind)
    | exact superpose eq135 eq10
    | (have j1 := eq135 X0
       grind)
    | exact resolve eq10 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq15272 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 X0) = (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq5000 (M.op X4 X0) X1 (M.op X2 (M.op X3 X4))
       have i₂ := eq9967 X3 X4 X4 X0 X2
       grind)
    | exact superpose eq9967 eq5000
    | exact resolve eq5000 eq9967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5000 eq9967
  have eq19467 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1282 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1282
  have eq29341 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op X3 (M.op X1 (M.op X2 X0))) (M.op X0 (M.op X0 (M.op X1 (M.op X2 X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq267 X0 X2 (M.op X1 (M.op X2 X0)) X3
       have i₂ := eq1012 X1 X2 X0
       grind)
    | exact superpose eq1012 eq267
    | exact resolve eq267 eq1012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267 eq1012
  have eq29484 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op X0 (M.op X0 (M.op X0 (M.op X1 (M.op X2 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29341 X0 X1 X2 x
       have i₂ := eq15272 (M.op X0 (M.op X0 (M.op X1 (M.op X2 X0)))) x X1 X2 X0
       grind)
    | exact superpose eq15272 eq29341
    | exact resolve eq29341 eq15272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15272 eq29341
  have eq43301 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (M.op (σ X0) (M.op (σ X0) (σ X0))) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1256 X1 X0 (M.op (M.op (σ X0) (M.op (σ X0) (σ X0))) (σ X0))
       have i₂ := eq1456 (σ X0) (σ X1) (σ X0) (M.op (σ X0) (M.op (σ X0) (σ X0)))
       grind)
    | exact superpose eq1456 eq1256
    | (have j0 := eq1256 X1 X0 x
       grind)
    | exact resolve eq1256 eq1456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1256 eq1456
  have eq43510 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq43301 X0 X1
       have i₂ := eq3623 (σ X0) (σ X0) (σ X0)
       grind)
    | exact superpose eq3623 eq43301
    | (have j0 := eq43301 X0 X1
       grind)
    | exact resolve eq43301 eq3623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3623 eq43301
  have eq43743 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq43510 X0 X1
       have j1 := eq19467 X1 X0
       grind)
    | (have r₁ := eq43510 X1 X1
       have r₂ := eq19467 X1 X1
       grind)
    | (have r₁ := eq43510 X1 X0
       have r₂ := eq19467 X0 X1
       grind)
    | exact resolve eq43510 eq19467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19467 eq43510
  have eq44113 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq10021 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10021
  have eq44124 : ∀ X1 X2 : G, (σ (k X2 X1)) = (M.op (σ X2) (σ X1)) ∨ (σ X2) = (M.op (σ X1) (σ X1)) := by
    intro X1 X2
    first
    | (have j0 := eq43743 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43743
  have eq44136 : ∀ X0 : G, (τ (σ X0)) ≠ (k X0 (τ (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq44113 (σ X0)
       have i₂ := eq29 X0 (σ X0)
       grind)
    | exact superpose eq29 eq44113
    | (have j0 := eq44113 (σ X0)
       grind)
    | exact resolve eq44113 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq44113
  have eq44137 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq44136 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq44136
    | (have j0 := eq44136 X0
       grind)
    | exact resolve eq44136 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44136
  have eq44140 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq44137 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq44137
    | (have j0 := eq44137 X0
       grind)
    | exact resolve eq44137 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44137
  have eq45012 : ∀ X3 X4 : G, (M.op (σ X3) (σ X4)) = (σ (k X3 X4)) ∨ (σ X3) = (M.op (σ X4) (σ X4)) := by
    intro X3 X4
    first
    | (have j0 := eq44124 X4 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44124
  have eq45350 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq45012 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45012
  have eq46075 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq45350 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45350
  have eq46301 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq46075 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46075
  have eq46358 : ∀ X2 X3 : G, (M.op (σ X2) (σ X3)) = (σ (k X2 X3)) ∨ (σ X2) = (M.op (σ X3) (σ X3)) := by
    intro X2 X3
    first
    | (have j0 := eq46301 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46301
  have eq46999 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq46358 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46358
  have eq47157 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X2) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq46999 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46999
  have eq48181 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq47157 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47157
  have eq49587 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq48181 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48181
  have eq49813 : ∀ X2 X3 : G, (M.op (σ X2) (σ X3)) = (σ (k X2 X3)) ∨ (σ X2) = (M.op (σ X3) (σ X3)) := by
    intro X2 X3
    first
    | (have j0 := eq49587 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49587
  have eq50288 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq49813 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49813
  have eq50993 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq50288 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50288
  have eq51099 : ∀ X2 X3 : G, (M.op (σ X2) (σ X3)) = (σ (k X2 X3)) ∨ (σ X2) = (M.op (σ X3) (σ X3)) := by
    intro X2 X3
    first
    | (have j0 := eq50993 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50993
  have eq52297 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq51099 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51099
  have eq53768 : ∀ X2 X4 : G, (σ (k X2 X4)) = (M.op (σ X2) (σ X4)) ∨ (σ X2) = (M.op (σ X4) (σ X4)) := by
    intro X2 X4
    first
    | (have j0 := eq52297 X2 X4
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52297
  have eq54652 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq53768 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53768
  have eq55582 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq54652 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54652
  have eq56857 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq55582 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55582
  have eq57053 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq56857 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56857
  have eq57183 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X2) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq57053 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57053
  have eq57611 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq57183 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57183
  have eq58497 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq57611 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57611
  have eq58935 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq58497 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58497
  have eq59755 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq58935 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58935
  have eq59973 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq59755 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59755
  have eq61204 : ∀ X0 X2 : G, (σ (k X0 X2)) = (M.op (σ X0) (σ X2)) ∨ (σ X0) = (M.op (σ X2) (σ X2)) := by
    intro X0 X2
    first
    | (have j0 := eq59973 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59973
  have eq61471 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq61204 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61204
  have eq62362 : ∀ X2 X3 : G, (M.op (σ X2) (σ X3)) = (σ (k X2 X3)) ∨ (σ X2) = (M.op (σ X3) (σ X3)) := by
    intro X2 X3
    first
    | (have j0 := eq61471 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61471
  have eq62608 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq62362 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62362
  have eq62686 : ∀ X3 X4 : G, (M.op (σ X3) (σ X4)) = (σ (k X3 X4)) ∨ (σ X3) = (M.op (σ X4) (σ X4)) := by
    intro X3 X4
    first
    | (have j0 := eq62608 X3 X4
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62608
  have eq63666 : ∀ X2 X3 : G, (M.op (σ X2) (σ X3)) = (σ (k X2 X3)) ∨ (σ X2) = (M.op (σ X3) (σ X3)) := by
    intro X2 X3
    first
    | (have j0 := eq62686 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62686
  have eq63900 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq63666 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63666
  have eq63968 : ∀ X3 X4 : G, (M.op (σ X3) (σ X4)) = (σ (k X3 X4)) ∨ (σ X3) = (M.op (σ X4) (σ X4)) := by
    intro X3 X4
    first
    | (have j0 := eq63900 X3 X4
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63900
  have eq64764 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X2) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq63968 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63968
  have eq64958 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq64764 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64764
  have eq66272 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq64958 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64958
  have eq66480 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq66272 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66272
  have eq67140 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq66480 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66480
  have eq67373 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq67140 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67140
  have eq67916 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq67373 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67373
  have eq68137 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X2) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq67916 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67916
  have eq69108 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq68137 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68137
  have eq69507 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq69108 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69108
  have eq69972 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq69507 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69507
  have eq70750 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq69972 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69972
  have eq71886 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X2) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq70750 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70750
  have eq73571 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq71886 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71886
  have eq73920 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq73571 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73571
  have eq74934 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq73920 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73920
  have eq75243 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq74934 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74934
  have eq75454 : ∀ X3 X4 : G, (M.op (σ X3) (σ X4)) = (σ (k X3 X4)) ∨ (σ X3) = (M.op (σ X4) (σ X4)) := by
    intro X3 X4
    first
    | (have j0 := eq75243 X3 X4
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75243
  have eq75615 : ∀ X0 X2 : G, (σ (k X0 X2)) = (M.op (σ X0) (σ X2)) ∨ (σ X0) = (M.op (σ X2) (σ X2)) := by
    intro X0 X2
    first
    | (have j0 := eq75454 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75454
  have eq76713 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq75615 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75615
  have eq77870 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq76713 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76713
  have eq78936 : ∀ X3 X4 : G, (M.op (σ X3) (σ X4)) = (σ (k X3 X4)) ∨ (σ X3) = (M.op (σ X4) (σ X4)) := by
    intro X3 X4
    first
    | (have j0 := eq77870 X3 X4
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77870
  have eq79238 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq78936 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78936
  have eq79341 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq79238 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79238
  have eq80295 : ∀ X3 X4 : G, (M.op (σ X3) (σ X4)) = (σ (k X3 X4)) ∨ (σ X3) = (M.op (σ X4) (σ X4)) := by
    intro X3 X4
    first
    | (have j0 := eq79341 X3 X4
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79341
  have eq81947 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq80295 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80295
  have eq82334 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq81947 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81947
  have eq82510 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq82334 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82334
  have eq83375 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq82510 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82510
  have eq83746 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X2) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq83375 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83375
  have eq83841 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X2) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq83746 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83746
  have eq85491 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq83841 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83841
  have eq85951 : ∀ X3 X4 : G, (M.op (σ X3) (σ X4)) = (σ (k X3 X4)) ∨ (σ X3) = (M.op (σ X4) (σ X4)) := by
    intro X3 X4
    first
    | (have j0 := eq85491 X3 X4
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85491
  have eq87059 : ∀ X2 X3 : G, (M.op (σ X2) (σ X3)) = (σ (k X2 X3)) ∨ (σ X2) = (M.op (σ X3) (σ X3)) := by
    intro X2 X3
    first
    | (have j0 := eq85951 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85951
  have eq87643 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq87059 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87059
  have eq87733 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq87643 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87643
  have eq87829 : ∀ X0 X2 : G, (σ (k X0 X2)) = (M.op (σ X0) (σ X2)) ∨ (σ X0) = (M.op (σ X2) (σ X2)) := by
    intro X0 X2
    first
    | (have j0 := eq87733 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87733
  have eq89305 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq87829 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87829
  have eq89570 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq89305 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89305
  have eq89770 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X2) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq89570 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89570
  have eq91278 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq89770 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89770
  have eq91629 : ∀ X1 X2 : G, (σ (k X2 X1)) = (M.op (σ X2) (σ X1)) ∨ (σ X2) = (M.op (σ X1) (σ X1)) := by
    intro X1 X2
    first
    | (have j0 := eq91278 X2 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91278
  have eq91901 : ∀ X1 X2 : G, (σ (k X2 X1)) = (M.op (σ X2) (σ X1)) ∨ (σ X2) = (M.op (σ X1) (σ X1)) := by
    intro X1 X2
    first
    | (have j0 := eq91629 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91629
  have eq93003 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X2) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq91901 X2 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91901
  have eq93245 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X2) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq93003 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93003
  have eq94162 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq93245 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93245
  have eq96588 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq94162 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94162
  have eq96971 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq96588 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96588
  have eq97266 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X2) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq96971 X2 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96971
  have eq98417 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X2) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq97266 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97266
  have eq98669 : ∀ X2 X3 : G, (M.op (σ X2) (σ X3)) = (σ (k X2 X3)) ∨ (σ X2) = (M.op (σ X3) (σ X3)) := by
    intro X2 X3
    first
    | (have j0 := eq98417 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98417
  have eq99956 : ∀ X2 X3 : G, (M.op (σ X2) (σ X3)) = (σ (k X2 X3)) ∨ (σ X2) = (M.op (σ X3) (σ X3)) := by
    intro X2 X3
    first
    | (have j0 := eq98669 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98669
  have eq101428 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X2) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq99956 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99956
  have eq102537 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq101428 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101428
  have eq102960 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq102537 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102537
  have eq104386 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq102960 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102960
  have eq106103 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X2) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq104386 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104386
  have eq106351 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X2) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq106103 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106103
  have eq107771 : ∀ X1 X2 : G, (σ (k X2 X1)) = (M.op (σ X2) (σ X1)) ∨ (σ X2) = (M.op (σ X1) (σ X1)) := by
    intro X1 X2
    first
    | (have j0 := eq106351 X2 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106351
  have eq108054 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq107771 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107771
  have eq108162 : ∀ X2 X3 : G, (M.op (σ X2) (σ X3)) = (σ (k X2 X3)) ∨ (σ X2) = (M.op (σ X3) (σ X3)) := by
    intro X2 X3
    first
    | (have j0 := eq108054 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108054
  have eq109854 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq108162 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108162
  have eq110255 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq109854 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109854
  have eq111785 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq110255 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110255
  have eq112908 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq111785 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111785
  have eq114924 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq112908 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112908
  have eq115290 : ∀ X1 X2 : G, (σ (k X2 X1)) = (M.op (σ X2) (σ X1)) ∨ (σ X2) = (M.op (σ X1) (σ X1)) := by
    intro X1 X2
    first
    | (have j0 := eq114924 X2 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114924
  have eq115570 : ∀ X2 X3 : G, (M.op (σ X2) (σ X3)) = (σ (k X2 X3)) ∨ (σ X2) = (M.op (σ X3) (σ X3)) := by
    intro X2 X3
    first
    | (have j0 := eq115290 X3 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115290
  have eq116900 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq115570 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115570
  have eq118447 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq116900 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116900
  have eq118782 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq118447 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118447
  have eq119023 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X2) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq118782 X2 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118782
  have eq119733 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq119023 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119023
  have eq120983 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq119733 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119733
  have eq121203 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X2) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq120983 X2 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120983
  have eq121876 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq121203 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121203
  have eq122213 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq121876 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121876
  have eq122612 : ∀ X0 X2 : G, (σ (k X0 X2)) = (M.op (σ X0) (σ X2)) ∨ (σ X0) = (M.op (σ X2) (σ X2)) := by
    intro X0 X2
    first
    | (have j0 := eq122213 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122213
  have eq122738 : ∀ X0 X3 : G, (σ (k X0 X3)) = (M.op (σ X0) (σ X3)) ∨ (σ X0) = (M.op (σ X3) (σ X3)) := by
    intro X0 X3
    first
    | (have j0 := eq122612 X0 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122612
  have eq122866 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq122738 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122738
  have eq124036 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq122866 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122866
  have eq124361 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq124036 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124036
  have eq125361 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq124361 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124361
  have eq125696 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq125361 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125361
  have eq125913 : ∀ X3 X4 : G, (M.op (σ X3) (σ X4)) = (σ (k X3 X4)) ∨ (σ X3) = (M.op (σ X4) (σ X4)) := by
    intro X3 X4
    first
    | (have j0 := eq125696 X3 X4
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125696
  have eq126106 : ∀ X0 X2 : G, (σ (k X0 X2)) = (M.op (σ X0) (σ X2)) ∨ (σ X0) = (M.op (σ X2) (σ X2)) := by
    intro X0 X2
    first
    | (have j0 := eq125913 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125913
  have eq126245 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq126106 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126106
  have eq126405 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq126245 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126245
  have eq126554 : ∀ X0 X2 : G, (σ (k X0 X2)) = (M.op (σ X0) (σ X2)) ∨ (σ X0) = (M.op (σ X2) (σ X2)) := by
    intro X0 X2
    first
    | (have j0 := eq126405 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126405
  have eq128227 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq126554 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126554
  have eq128465 : ∀ X1 X2 : G, (σ (k X2 X1)) = (M.op (σ X2) (σ X1)) ∨ (σ X2) = (M.op (σ X1) (σ X1)) := by
    intro X1 X2
    first
    | (have j0 := eq128227 X2 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128227
  have eq128677 : ∀ X2 X3 : G, (M.op (σ X2) (σ X3)) = (σ (k X2 X3)) ∨ (σ X2) = (M.op (σ X3) (σ X3)) := by
    intro X2 X3
    first
    | (have j0 := eq128465 X3 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128465
  have eq128892 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq128677 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128677
  have eq129028 : ∀ X0 X2 : G, (σ (k X0 X2)) = (M.op (σ X0) (σ X2)) ∨ (σ X0) = (M.op (σ X2) (σ X2)) := by
    intro X0 X2
    first
    | (have j0 := eq128892 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128892
  have eq129811 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq129028 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129028
  have eq130399 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    grind
  have eq130400 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq68 (σ X0)
       have i₂ := eq7975 X0
       grind)
    | exact superpose eq7975 eq68
    | (have j1 := eq7975 X0
       grind)
    | exact resolve eq68 eq7975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7975
  have eq130556 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq130399 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq130399
    | (have j0 := eq130399 X0
       grind)
    | exact resolve eq130399 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130399
  have eq130562 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq129811 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129811
  have eq130574 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    grind
  clear eq130556
  have eq130585 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq130562 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130562
  have eq130657 : ∀ X0 X2 : G, (σ (k X0 X2)) = (M.op (σ X0) (σ X2)) ∨ (σ X0) = (M.op (σ X2) (σ X2)) := by
    intro X0 X2
    first
    | (have j0 := eq130585 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130585
  have eq130675 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq130657 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130657
  have eq130681 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq130675 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130675
  have eq130771 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq130681 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130681
  have eq130777 : ∀ X0 X2 : G, (σ (k X0 X2)) = (M.op (σ X0) (σ X2)) ∨ (σ X0) = (M.op (σ X2) (σ X2)) := by
    intro X0 X2
    first
    | (have j0 := eq130771 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130771
  have eq130906 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq130777 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130777
  have eq130918 : ∀ X0 X2 : G, (σ (k X0 X2)) = (M.op (σ X0) (σ X2)) ∨ (σ X0) = (M.op (σ X2) (σ X2)) := by
    intro X0 X2
    first
    | (have j0 := eq130906 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130906
  have eq131062 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq130918 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130918
  have eq131074 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq131062 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131062
  have eq131912 : ∀ X0 X2 : G, (σ (k X2 X0)) = (M.op (σ X2) (σ X0)) ∨ (σ X2) = (M.op (σ X0) (σ X0)) := by
    intro X0 X2
    first
    | (have j0 := eq131074 X2 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131074
  have eq132217 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq131912 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131912
  have eq133683 : ∀ X0 X2 : G, (σ (k X0 X2)) = (M.op (σ X0) (σ X2)) ∨ (σ X0) = (M.op (σ X2) (σ X2)) := by
    intro X0 X2
    first
    | (have j0 := eq132217 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132217
  have eq134098 : ∀ X3 X4 : G, (M.op (σ X3) (σ X4)) = (σ (k X3 X4)) ∨ (σ X3) = (M.op (σ X4) (σ X4)) := by
    intro X3 X4
    first
    | (have j0 := eq133683 X3 X4
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133683
  have eq134443 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq134098 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134098
  have eq134604 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq134443 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134443
  have eq134680 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq134604 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134604
  have eq134704 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (σ X1) = (M.op (σ X2) (σ X2)) := by
    intro X1 X2
    first
    | (have j0 := eq134680 X2 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134680
  have eq134743 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq134704 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134704
  have eq134753 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  have eq134770 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq134743 (τ X1) (τ X0)
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq134743
    | (have j0 := eq134743 (τ X1) (τ X0)
       grind)
    | exact resolve eq134743 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq134793 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq134743 X1 X0
       grind)
    | exact superpose eq134743 eq10
    | (have j1 := eq134743 X1 X0
       grind)
    | exact resolve eq10 eq134743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134876 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq134770 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq134770
    | (have j0 := eq134770 X0 X1
       grind)
    | exact resolve eq134770 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134770
  have eq134900 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq134876 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq134876
    | (have j0 := eq134876 X0 X1
       grind)
    | exact resolve eq134876 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134876
  have eq134906 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq134900 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq134900
    | (have j0 := eq134900 X0 X1
       grind)
    | exact resolve eq134900 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134900
  have eq134911 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq134906 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq134906
    | (have j0 := eq134906 X0 X1
       grind)
    | exact resolve eq134906 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134906
  have eq134916 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq134911 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq134911
    | (have j0 := eq134911 X0 X1
       grind)
    | exact resolve eq134911 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134911
  have eq134949 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq134743 X1 X0
       have i₂ := eq134916 X0 X1
       grind)
    | exact superpose eq134916 eq134743
    | (have j0 := eq134743 X1 X0
       have j1 := eq134916 (σ X0) (σ X1)
       grind)
    | exact resolve eq134743 eq134916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134743
  have eq341077 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq134753 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134753
  have eq538757 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq134949 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134949
  have eq538874 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq538757 x y
       grind)
    | exact superpose eq538757 eq16
    | (have j1 := eq538757 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq538757 x y
       grind)
    | exact resolve eq16 eq538757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538757
  have eq539262 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq538874
  have eq539407 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq134793 y y
       have i₂ := eq539262
       grind)
    | exact superpose eq539262 eq134793
    | exact resolve eq134793 eq539262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134793
  have eq539411 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  have eq539515 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1067 (σ y) (σ y)
       have i₂ := eq539262
       grind)
    | exact superpose eq539262 eq1067
    | exact resolve eq1067 eq539262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq539817 : (M.op (σ y) (σ x)) = (σ (k x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq539411
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq539411
    | exact resolve eq539411 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539411
  have eq539820 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq539407
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq539407
    | exact resolve eq539407 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539407
  have eq539841 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq134916 eq539817
    | (have j1 := eq134916 x y
       grind)
    | exact resolve eq539817 eq134916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539817
  have eq539854 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq539515
       grind)
    | exact superpose eq539515 eq16
    | exact resolve eq16 eq539515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539515
  have eq540254 : x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq134916 y y
       have i₂ := eq539820
       grind)
    | exact superpose eq539820 eq134916
    | (have j0 := eq134916 x y
       grind)
    | exact resolve eq134916 eq539820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134916 eq539820
  have eq540256 : y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq540254
  have eq540660 : (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq341077 y
       have i₂ := eq540256
       grind)
    | exact superpose eq540256 eq341077
    | (have j0 := eq341077 y
       grind)
    | exact resolve eq341077 eq540256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq541003 : (σ x) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq539262 eq540660
    | exact resolve eq540660 eq539262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540660
  have eq541085 : (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq539262 eq541003
    | exact resolve eq541003 eq539262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541003
  have eq541086 : (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by grind
  clear eq541085
  have eq541110 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq540256 eq541086
    | exact resolve eq541086 eq540256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540256 eq541086
  have eq541111 : x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq541110
  have eq541126 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq541111 eq539262
    | exact resolve eq539262 eq541111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539262
  have eq541128 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq541111 eq539841
    | exact resolve eq539841 eq541111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539841 eq541111
  have eq569323 : (σ (M.op x y)) = (σ x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq541126 eq541128
    | exact resolve eq541128 eq541126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541126 eq541128
  have eq569324 : x = (M.op y y) := by
    first
    | (have r₁ := eq569323
       have r₂ := eq539854
       grind)
    | exact resolve eq569323 eq539854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539854 eq569323
  have eq569331 : y = (M.op y (M.op y x)) := by
    first
    | (have i₁ := eq68 y
       have i₂ := eq569324
       grind)
    | exact superpose eq569324 eq68
    | exact resolve eq68 eq569324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq569436 : x = (M.op x y) := by
    first
    | (have i₁ := eq1067 y y
       have i₂ := eq569324
       grind)
    | exact superpose eq569324 eq1067
    | exact resolve eq1067 eq569324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1067 eq569324
  have eq569730 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq569436
       grind)
    | exact superpose eq569436 eq16
    | exact resolve eq16 eq569436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq570133 : y = (M.op x (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq29484 x y y
       have i₂ := eq569331
       grind)
    | exact superpose eq569331 eq29484
    | exact resolve eq29484 eq569331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29484 eq569331
  have eq570553 : y = (M.op x (M.op x x)) := by
    first
    | (have i₁ := eq570133
       have i₂ := eq569436
       grind)
    | exact superpose eq569436 eq570133
    | exact resolve eq570133 eq569436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569436 eq570133
  have eq1613597 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 (M.op X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq130574 eq130400
    | (have j0 := eq130400 X0
       have j1 := eq130574 X0
       grind)
    | exact resolve eq130400 eq130574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130400 eq130574
  have eq1615580 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1613597 x
       have i₂ := eq570553
       grind)
    | exact superpose eq570553 eq1613597
    | (have j0 := eq1613597 x
       grind)
    | exact resolve eq1613597 eq570553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1613597
  have eq1616184 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq1615580
       have r₂ := eq569730
       grind)
    | exact resolve eq1615580 eq569730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1615580
  have eq1617062 : (τ (M.op (σ x) (σ x))) = (k (τ (σ x)) x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq65 x
       have i₂ := eq1616184
       grind)
    | exact superpose eq1616184 eq65
    | exact resolve eq65 eq1616184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq1617832 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1617062
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1617062
    | exact resolve eq1617062 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1617062
  have eq1617921 : (τ (σ x)) = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1616184 eq1617832
    | exact resolve eq1617832 eq1616184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1616184 eq1617832
  have eq1617954 : x = (k x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1617921
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1617921
    | exact resolve eq1617921 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1617921
  have eq1617968 : x = (M.op x x) := by
    first
    | (have j1 := eq44140 x
       grind)
    | (have r₁ := eq1617954
       have r₂ := eq44140 x
       grind)
    | exact resolve eq1617954 eq44140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44140 eq1617954
  have eq1617970 : y = (M.op x x) := by
    first
    | (have i₁ := eq570553
       have i₂ := eq1617968
       grind)
    | exact superpose eq1617968 eq570553
    | exact resolve eq570553 eq1617968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570553
  have eq1618161 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq341077 x
       have i₂ := eq1617968
       grind)
    | exact superpose eq1617968 eq341077
    | (have j0 := eq341077 x
       grind)
    | exact resolve eq341077 eq1617968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341077
  have eq1618798 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1618161
       have i₂ := eq1617968
       grind)
    | exact superpose eq1617968 eq1618161
    | exact resolve eq1618161 eq1617968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1618161
  have eq1618799 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1618798
  have eq1618926 : x = y := by
    first
    | (have i₁ := eq1617970
       have i₂ := eq1617968
       grind)
    | exact superpose eq1617968 eq1617970
    | exact resolve eq1617970 eq1617968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1617968 eq1617970
  have eq1619172 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq569730
       have i₂ := eq1618926
       grind)
    | exact superpose eq1618926 eq569730
    | exact resolve eq569730 eq1618926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569730 eq1618926
  have eq1619329 : False := by grind
  exact eq1619329

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if m(X,Y) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pyy_pxx_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
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
  have eq174 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
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
  have eq175 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
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
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq175 (M.op sF4 sF4)
       have i₂ := eq16 sF4 sF4 sF4
       grind)
    | exact superpose eq16 eq175
    | exact resolve eq175 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (σ y))) ≠ X0 ∨ (M.op (σ y) (M.op (σ x) (σ y))) = (k X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq182 eq13
    | (have r₁ := eq13 (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))
       have r₂ := eq182
       grind)
    | exact resolve eq13 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq613 : (M.op (σ y) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq182 eq11
    | exact resolve eq11 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq626 : (M.op x y) = (k y x) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
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
  have eq636 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
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
  have eq667 : (M.op (σ y) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) := by grind
  clear eq613
  have eq679 : (M.op (σ y) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have j1 := eq187 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq667
       have r₂ := eq187 (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq667
       have r₂ := eq187 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq667 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187 eq667
  have eq722 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq679 eq16
    | exact resolve eq16 eq679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679
  have eq876 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op x y) (M.op X0 X0)) X0) := by
    intro X0
    first
    | exact superpose eq174 eq177
    | exact resolve eq177 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq890 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 X0 X0
       have i₂ := eq177 X0 X0
       grind)
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq894 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (k (M.op X1 X0) (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X0 (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq177 X0 X1
       grind)
    | exact superpose eq177 eq11
    | exact resolve eq11 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq899 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq175 (M.op X1 X0)
       have i₂ := eq177 X1 X0
       grind)
    | exact superpose eq177 eq175
    | exact resolve eq175 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq901 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) ≠ X2 ∨ (M.op X0 (M.op X1 X0)) = (k X2 (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op X0 X1)
       have i₂ := eq177 X0 X1
       grind)
    | exact superpose eq177 eq13
    | (have r₁ := eq13 (M.op X1 (M.op X0 X1)) (M.op X0 X1)
       have r₂ := eq177 X0 X1
       grind)
    | exact resolve eq13 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq903 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (k (M.op X1 X0) (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq894 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq894
  have eq905 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (k (M.op X1 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq903 X0 X1
       have j1 := eq901 X0 X1 (M.op X1 X0)
       grind)
    | (have r₁ := eq903 X0 X1
       have r₂ := eq901 X0 X1 (k (M.op X1 X0) (M.op X1 X0))
       grind)
    | (have r₁ := eq903 (M.op X1 X0) X0
       have r₂ := eq901 X0 X1 (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0)))
       grind)
    | (have r₁ := eq903 X0 X1
       have r₂ := eq901 X0 X1 (M.op X1 X0)
       grind)
    | exact resolve eq903 eq901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901 eq903
  have eq943 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op X0 (M.op X0 X0)) X0
       have i₂ := eq890 X0
       grind)
    | exact superpose eq890 eq16
    | exact resolve eq16 eq890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq994 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq876 eq16
    | exact resolve eq16 eq876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq876
  have eq1007 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq994 X0
       have i₂ := eq177 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq177 eq994
    | exact resolve eq994 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq994
  have eq1014 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1007 X0
       have i₂ := eq177 X0 X0
       grind)
    | exact superpose eq177 eq1007
    | exact resolve eq1007 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1007
  have eq1144 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X0)) X0) := by
    intro X0 X1
    first
    | exact superpose eq180 eq177
    | exact resolve eq177 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq1417 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq626
       grind)
    | exact superpose eq626 eq39
    | exact resolve eq39 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626
  have eq1418 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1417
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1417
    | exact resolve eq1417 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1417
  have eq1420 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq1418
    | exact resolve eq1418 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1418
  have eq1962 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq899 (M.op X0 X0) X0
       have i₂ := eq1014 X0
       grind)
    | exact superpose eq1014 eq899
    | exact resolve eq899 eq1014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2109 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1014 X0
       have i₂ := eq1962 X0
       grind)
    | exact superpose eq1962 eq1014
    | exact resolve eq1014 eq1962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1014
  have eq2111 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq890 X0
       have i₂ := eq1962 X0
       grind)
    | exact superpose eq1962 eq890
    | exact resolve eq890 eq1962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq890
  have eq2120 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0))) = (M.op (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0))) := by
    intro X0
    first
    | (have i₁ := eq177 X0 (M.op X0 X0)
       have i₂ := eq1962 X0
       grind)
    | exact superpose eq1962 eq177
    | exact resolve eq177 eq1962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2151 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0))) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0))) := by
    intro X0
    first
    | (have i₁ := eq2120 X0
       have i₂ := eq177 sF3 (M.op sF4 X0)
       grind)
    | exact superpose eq177 eq2120
    | exact resolve eq2120 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq2120
  have eq2160 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq2109 eq2151
    | exact resolve eq2151 eq2109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2109 eq2151
  have eq2196 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | exact superpose eq175 eq2111
    | exact resolve eq2111 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2111
  have eq3543 : ∀ X0 : G, (k X0 X0) = (M.op (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) X0) := by
    intro X0
    first
    | exact superpose eq2160 eq905
    | exact resolve eq905 eq2160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2160
  have eq3580 : ∀ X0 : G, (k X0 X0) = (M.op (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op X0 X0)) X0) := by
    intro X0
    first
    | exact superpose eq722 eq905
    | exact resolve eq905 eq722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722
  have eq3592 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq3580 X0
       have i₂ := eq1144 X0 (k sF4 sF4)
       grind)
    | exact superpose eq1144 eq3580
    | exact resolve eq3580 eq1144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1144 eq3580
  have eq3662 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (k X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq175 X0
       have i₂ := eq3592 X0
       grind)
    | exact superpose eq3592 eq175
    | exact resolve eq175 eq3592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq3678 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq1962 X0
       have i₂ := eq3592 X0
       grind)
    | exact superpose eq3592 eq1962
    | exact resolve eq1962 eq3592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3681 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq2196 X0
       have i₂ := eq3592 X0
       grind)
    | exact superpose eq3592 eq2196
    | exact resolve eq2196 eq3592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2196
  have eq3690 : ∀ X0 : G, (k X0 X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq899 X0 X0
       have i₂ := eq3592 X0
       grind)
    | exact superpose eq3592 eq899
    | exact resolve eq899 eq3592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3692 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (k (k X0 X0) (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq905 X0 X0
       have i₂ := eq3592 X0
       grind)
    | exact superpose eq3592 eq905
    | exact resolve eq905 eq3592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905
  have eq3813 : ∀ X0 : G, (σ X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq3662 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq3662
    | exact resolve eq3662 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3662
  have eq5081 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq3678 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq3678
    | exact resolve eq3678 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3678
  have eq6003 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ (k X0 X0)) (σ (k X0 X0))) := by
    intro X0
    first
    | exact superpose eq3813 eq3543
    | exact resolve eq3543 eq3813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3543 eq3813
  have eq6027 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq6003 X0
       have i₂ := eq10 (k X0 X0) (k X0 X0)
       grind)
    | exact superpose eq10 eq6003
    | exact resolve eq6003 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6003
  have eq6046 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (M.op X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq6027 X0
       have i₂ := eq3692 X0
       grind)
    | exact superpose eq3692 eq6027
    | exact resolve eq6027 eq3692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3692 eq6027
  have eq6051 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ X0))) = (σ (M.op X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq6046 X0
       have i₂ := eq5081 X0
       grind)
    | exact superpose eq5081 eq6046
    | exact resolve eq6046 eq5081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5081 eq6046
  have eq10165 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq943 X0 X0
       grind)
    | exact superpose eq943 eq16
    | exact resolve eq16 eq943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq943
  have eq10239 : ∀ X0 X1 X2 : G, (M.op X0 (k X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10165 X0 X1 X2
       have i₂ := eq3592 X0
       grind)
    | exact superpose eq3592 eq10165
    | exact resolve eq10165 eq3592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10165
  have eq21340 : ∀ X0 X1 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (k X0 X0)))) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq899 X0 (M.op X1 X0)
       have i₂ := eq10239 X0 X0 X1
       grind)
    | exact superpose eq10239 eq899
    | exact resolve eq899 eq10239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq899 eq10239
  have eq21399 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | exact superpose eq3690 eq21340
    | exact resolve eq21340 eq3690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3690 eq21340
  have eq126643 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1420 eq636
    | exact resolve eq636 eq1420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636 eq1420
  have eq126654 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq126643
       have r₂ := eq27
       grind)
    | exact resolve eq126643 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126643
  have eq126662 : (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq126654
       have i₂ := eq3592 sF2
       grind)
    | exact superpose eq3592 eq126654
    | exact resolve eq126654 eq3592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126654
  have eq126668 : (σ y) = (k (σ x) (σ x)) ∨ y = (k x x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq126662
       have i₂ := eq3592 x
       grind)
    | exact superpose eq3592 eq126662
    | exact resolve eq126662 eq3592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126662
  have eq128195 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (k x x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq126668 eq3681
    | exact resolve eq3681 eq126668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126668
  have eq128286 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (k x x) ∨ y = (M.op y x) := by grind
  clear eq128195
  have eq128408 : (k (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ y = (k x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq128286 eq21399
    | exact resolve eq21399 eq128286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128438 : (σ y) = (k (σ x) (σ x)) ∨ y = (k x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq128286 eq128408
    | exact resolve eq128408 eq128286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128286 eq128408
  have eq128520 : (τ (σ y)) = (k x x) ∨ y = (k x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq128438 eq97
    | exact resolve eq97 eq128438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq128438
  have eq128733 : y = (k x x) ∨ y = (k x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq31 eq128520
    | exact resolve eq128520 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq128520
  have eq128734 : y = (k x x) ∨ y = (M.op y x) := by grind
  clear eq128733
  have eq128830 : y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq3681 x
       have i₂ := eq128734
       grind)
    | exact superpose eq128734 eq3681
    | exact resolve eq3681 eq128734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3681 eq128734
  have eq128920 : y = (M.op y x) := by grind
  clear eq128830
  have eq129015 : (k x x) = (M.op y x) := by
    first
    | (have i₁ := eq21399 x y
       have i₂ := eq128920
       grind)
    | exact superpose eq128920 eq21399
    | exact resolve eq21399 eq128920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21399
  have eq129045 : y = (k x x) := by
    first
    | (have i₁ := eq129015
       have i₂ := eq128920
       grind)
    | exact superpose eq128920 eq129015
    | exact resolve eq129015 eq128920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128920 eq129015
  have eq129120 : (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq129045
       grind)
    | exact superpose eq129045 eq39
    | exact resolve eq39 eq129045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq129185 : (σ (M.op x y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    first
    | (have i₁ := eq6051 x
       have i₂ := eq129045
       grind)
    | exact superpose eq129045 eq6051
    | exact resolve eq6051 eq129045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6051 eq129045
  have eq129252 : (σ (M.op x y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    first
    | (have i₁ := eq129185
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq129185
    | exact resolve eq129185 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129185
  have eq129299 : (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq129120
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq129120
    | exact resolve eq129120 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq129120
  have eq129323 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq1962 eq129252
    | exact resolve eq129252 eq1962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1962 eq129252
  have eq129359 : (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq129299
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq129299
    | exact resolve eq129299 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq129299
  have eq129368 : (σ (M.op x y)) = (M.op (σ x) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq129323
       have i₂ := eq3592 sF2
       grind)
    | exact superpose eq3592 eq129323
    | exact resolve eq129323 eq3592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3592 eq129323
  have eq129390 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq129359 eq129368
    | exact resolve eq129368 eq129359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129359 eq129368
  have eq129404 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq129390
    | exact resolve eq129390 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq129390
  have eq129416 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq129404
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq129404
    | exact resolve eq129404 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq129404
  have eq129426 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq129416
    | exact resolve eq129416 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq129416
  have eq129432 : False := by grind
  exact eq129432

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_pyy_pyx_pyy_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq33 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 (M.op X1 X0) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq38 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq173 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq38 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq176 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq173 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq173 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq173 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq173 X0 X1
       have r₂ := eq14 (M.op X1 X0) X1
       grind)
    | exact resolve eq173 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173
  have eq1122 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  clear eq176
  have eq1144 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1122 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1122
  have eq1499 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq1144 (σ X1) (σ X0)
       grind)
    | exact superpose eq1144 eq15
    | exact resolve eq15 eq1144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1510 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1499 X0 X1
       have i₂ := eq1144 X1 X0
       grind)
    | exact superpose eq1144 eq1499
    | exact resolve eq1499 eq1144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1144 eq1499
  have eq1520 : False := by grind
  exact eq1520

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pxx_pxx_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
  have eq26 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
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
  have eq46 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  have eq53 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq46 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq67 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq92 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq20 X0 (τ X0)
       have i₂ := eq53 (τ X0)
       grind)
    | exact superpose eq53 eq20
    | exact resolve eq20 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq93 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq92 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq92
    | exact resolve eq92 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq101 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq93 X0
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq93
    | exact resolve eq93 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq93
  have eq105 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq101 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq101
    | exact resolve eq101 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq121 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    grind
  clear eq26
  have eq344 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq67 X0 X1
       have i₂ := eq105 X1
       grind)
    | exact superpose eq105 eq67
    | (have j0 := eq67 X0 X1
       grind)
    | exact resolve eq67 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq383 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq344 y x
       grind)
    | exact superpose eq344 eq16
    | (have j1 := eq344 y x
       grind)
    | exact resolve eq16 eq344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344
  have eq1088 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq383
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq383
    | (have j1 := eq14 (σ y) (σ (M.op x x))
       grind)
    | (have r₁ := eq383
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq383
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq383 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383
  have eq1089 : x = y ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq1088
  have eq1129 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq121 (σ X0)
       have i₂ := eq105 X0
       grind)
    | exact superpose eq105 eq121
    | exact resolve eq121 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1152 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1129 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq1129
    | exact resolve eq1129 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1129
  have eq1162 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1152 X0
       have i₂ := eq121 X0
       grind)
    | exact superpose eq121 eq1152
    | exact resolve eq1152 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq1152
  have eq54688 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1089
       grind)
    | exact superpose eq1089 eq16
    | exact resolve eq16 eq1089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1089
  have eq54689 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq54688
       have r₂ := eq105 x
       grind)
    | exact resolve eq54688 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54688
  have eq631343 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq54689
       grind)
    | exact superpose eq54689 eq10
    | exact resolve eq10 eq54689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54689
  have eq631705 : x = y ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq631343
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq631343
    | exact resolve eq631343 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631343
  have eq892953 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq631705
       grind)
    | exact superpose eq631705 eq16
    | exact resolve eq16 eq631705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631705
  have eq892954 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq892953
       have r₂ := eq105 x
       grind)
    | exact resolve eq892953 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq892953
  have eq893044 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq892954
       grind)
    | exact superpose eq892954 eq10
    | exact resolve eq10 eq892954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq892954
  have eq893559 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq893044
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq893044
    | exact resolve eq893044 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq893044
  have eq893560 : y = (M.op x x) := by grind
  clear eq893559
  have eq893882 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1162 x
       have i₂ := eq893560
       grind)
    | exact superpose eq893560 eq1162
    | exact resolve eq1162 eq893560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1162 eq893560
  have eq894678 : False := by grind
  exact eq894678

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pyx_pxx_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
  have eq32 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq35 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  clear eq20
  have eq46 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  have eq49 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq46 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq62 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq85 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq32 X0 (σ X0)
       have i₂ := eq49 (σ X0)
       grind)
    | exact superpose eq49 eq32
    | exact resolve eq32 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq87 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq49 (τ X0)
       grind)
    | exact superpose eq49 eq19
    | exact resolve eq19 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq88 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq87 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq87
    | exact resolve eq87 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq90 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq85 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq85
    | exact resolve eq85 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq96 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq88 X0
       have i₂ := eq49 X0
       grind)
    | exact superpose eq49 eq88
    | exact resolve eq88 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq97 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq90 X0
       have i₂ := eq49 X0
       grind)
    | exact superpose eq49 eq90
    | exact resolve eq90 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq90
  have eq100 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq96 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq96
    | exact resolve eq96 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq96 X0
       grind)
    | exact superpose eq96 eq10
    | exact resolve eq10 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq192 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq62 X0 X1
       have i₂ := eq100 X1
       grind)
    | exact superpose eq100 eq62
    | (have j0 := eq62 X0 X1
       grind)
    | exact resolve eq62 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq223 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq192 y x
       grind)
    | exact superpose eq192 eq16
    | (have j1 := eq192 y x
       grind)
    | exact resolve eq16 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq428 : ∀ X0 : G, (σ (M.op (τ X0) (τ (M.op X0 X0)))) = (k (σ (τ (M.op X0 X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq35 X0
       have i₂ := eq108 X0
       grind)
    | exact superpose eq108 eq35
    | exact resolve eq35 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq108
  have eq429 : ∀ X0 : G, (k (M.op X0 X0) X0) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq428 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq428
    | exact resolve eq428 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428
  have eq430 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) := by
    intro X0
    grind
  clear eq429
  have eq461 : ∀ X0 : G, (M.op (σ X0) (M.op (σ X0) (σ X0))) = (σ (M.op X0 (τ (M.op (σ X0) (σ X0))))) := by
    intro X0
    first
    | (have i₁ := eq430 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq430
    | exact resolve eq430 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430
  have eq497 : ∀ X0 : G, (M.op (σ X0) (M.op (σ X0) (σ X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq461 X0
       have i₂ := eq97 X0
       grind)
    | exact superpose eq97 eq461
    | exact resolve eq461 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq461
  have eq503 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq497 X0
       have i₂ := eq100 X0
       grind)
    | exact superpose eq100 eq497
    | exact resolve eq497 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497
  have eq830 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq223
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq223
    | (have j1 := eq14 (σ y) (σ (M.op x x))
       grind)
    | (have r₁ := eq223
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq223
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq223 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq831 : x = y ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq830
  have eq12842 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq831
       grind)
    | exact superpose eq831 eq16
    | exact resolve eq16 eq831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831
  have eq12843 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq12842
       have r₂ := eq100 x
       grind)
    | exact resolve eq12842 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12842
  have eq335183 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq12843
       grind)
    | exact superpose eq12843 eq10
    | exact resolve eq10 eq12843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12843
  have eq335487 : x = y ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq335183
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq335183
    | exact resolve eq335183 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335183
  have eq720730 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq335487
       grind)
    | exact superpose eq335487 eq16
    | exact resolve eq16 eq335487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335487
  have eq720731 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq720730
       have r₂ := eq100 x
       grind)
    | exact resolve eq720730 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq720730
  have eq720819 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq720731
       grind)
    | exact superpose eq720731 eq10
    | exact resolve eq10 eq720731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720731
  have eq721256 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq720819
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq720819
    | exact resolve eq720819 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720819
  have eq721257 : y = (M.op x x) := by grind
  clear eq721256
  have eq721390 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq503 x
       have i₂ := eq721257
       grind)
    | exact superpose eq721257 eq503
    | exact resolve eq503 eq721257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503 eq721257
  have eq722134 : False := by grind
  exact eq722134

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyx_pyx_pxx_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
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
  have eq29 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X2 X2) = (M.op X0 X2) ∨ (M.op X0 X2) = (k X2 X0) := by
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
  have eq38 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq42 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq43 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq45 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X2 X2) = (M.op X0 X2) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq29 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq47 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq43 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq43 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq128 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq410 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq45 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq411 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq410 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410
  have eq416 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq411 X0 X1
       have j1 := eq128 X0 X1
       grind)
    | (have r₁ := eq411 X0 X1
       have r₂ := eq128 X0 X1
       grind)
    | (have r₁ := eq411 X0 X0
       have r₂ := eq128 X0 X0
       grind)
    | exact resolve eq411 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq411
  have eq570 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq416 (σ X1) (σ X0)
       grind)
    | exact superpose eq416 eq15
    | exact resolve eq15 eq416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq573 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq570 X0 X1
       have i₂ := eq416 X1 X0
       grind)
    | exact superpose eq416 eq570
    | exact resolve eq570 eq416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416 eq570
  have eq577 : False := by grind
  exact eq577

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyy_pyx_pxy_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq7275 : (M.op y y) = (τ (σ (M.op x x))) ∨ (M.op x x) = (M.op y y) := by
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
  have eq7322 : (M.op x x) = (M.op y y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq7275
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq7275
    | exact resolve eq7275 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7275
  have eq7323 : (M.op x x) = (M.op y y) := by grind
  clear eq7322
  have eq7352 : ∀ X0 : G, y = (M.op (τ X0) (M.op (τ (M.op X0 X0)) (M.op x x))) := by
    intro X0
    first
    | (have i₁ := eq224 X0 y
       have i₂ := eq7323
       grind)
    | exact superpose eq7323 eq224
    | exact resolve eq224 eq7323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7323
  have eq7429 : x = y := by
    first
    | (have i₁ := eq7352 x
       have i₂ := eq224 x x
       grind)
    | exact superpose eq224 eq7352
    | exact resolve eq7352 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224 eq7352
  have eq7503 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7429
       grind)
    | exact superpose eq7429 eq16
    | exact resolve eq16 eq7429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7429
  have eq7504 : False := by grind
  exact eq7504

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pyx_x_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq33 : ∀ X0 X1 X2 : G, (k (τ X2) (k (τ X0) X1)) = (τ (k X2 (k X0 (σ X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 X2 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq23
    | exact resolve eq23 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
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
  have eq64 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X2 X1) (M.op X0 X0)) X0) := by
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
  have eq66 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
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
  have eq68 : ∀ X0 X1 X2 : G, (M.op X1 X0) ≠ (M.op X0 (M.op X1 X0)) ∨ (k X2 (M.op X1 X0)) = (M.op (M.op X1 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 (M.op X1 X0)
       have i₂ := eq63 X1 X0
       grind)
    | exact superpose eq63 eq12
    | (have j0 := eq12 X2 (M.op X1 X0)
       grind)
    | exact resolve eq12 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
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
  have eq72 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 (M.op X0 X0)) X0
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq9
    | exact resolve eq9 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq64 X1 (M.op (M.op x x) (M.op X0 X0)) x
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq64
    | exact resolve eq64 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq110 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X1 X1)) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq72 X1 (M.op X0 (M.op X0 X0))
       have i₂ := eq72 X0 X0
       grind)
    | exact superpose eq72 eq72
    | exact resolve eq72 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X1 X1))
       have i₂ := eq72 X1 X0
       grind)
    | exact superpose eq72 eq9
    | exact resolve eq9 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq72 X0 X0
       grind)
    | exact superpose eq72 eq9
    | exact resolve eq9 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq82 X0 (M.op X1 (M.op X1 X1))
       have i₂ := eq72 X1 X1
       grind)
    | exact superpose eq72 eq82
    | exact resolve eq82 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq157 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq120 X2 X1 (M.op X0 (M.op X0 X0))
       have i₂ := eq120 X0 X0 X0
       grind)
    | exact superpose eq120 eq120
    | exact resolve eq120 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op X1 X0) X2)) = (M.op X3 (M.op (M.op X4 X3) X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq121 X2 X3 X4
       have i₂ := eq121 X2 X0 X1
       grind)
    | exact superpose eq121 eq121
    | exact resolve eq121 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq125 X2 X3
       have i₂ := eq121 X2 X0 X1
       grind)
    | exact superpose eq121 eq125
    | exact resolve eq125 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq198 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq66 X2
       have i₂ := eq121 X2 X0 X1
       grind)
    | exact superpose eq121 eq66
    | exact resolve eq66 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq199 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X2)) (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq120 X2 X3 X2
       have i₂ := eq121 X2 X0 X1
       grind)
    | exact superpose eq121 eq120
    | exact resolve eq120 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq201 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X0 (M.op (M.op X1 X0) X2)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq82 X2 X2
       have i₂ := eq121 X2 X0 X1
       grind)
    | exact superpose eq121 eq82
    | exact resolve eq82 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq205 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X3 (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 X3) X3 X2
       have i₂ := eq121 (M.op X2 X3) X0 X1
       grind)
    | exact superpose eq121 eq9
    | exact resolve eq9 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq289 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) (M.op (M.op X3 (M.op X0 X0)) (M.op X0 X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq197 (M.op X3 (M.op X0 X0)) (M.op x (M.op X3 X3)) X2 X1
       have i₂ := eq120 X3 x X0
       grind)
    | exact superpose eq120 eq197
    | exact resolve eq197 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq506 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
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
    | (have r₁ := eq14 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq507 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq506 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq506
    | (have j0 := eq506 (σ X0) (σ X1)
       grind)
    | exact resolve eq506 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq515 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    grind
  have eq642 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X2) = (M.op X3 (M.op (M.op X4 X3) (M.op X0 (M.op (M.op X1 X0) X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq69 X2 X2 X3 X4
       have i₂ := eq121 X2 X0 X1
       grind)
    | exact superpose eq121 eq69
    | exact resolve eq69 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq643 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq69 X0 (M.op X1 X0) X2 X3
       have i₂ := eq121 X0 X0 X1
       grind)
    | exact superpose eq121 eq69
    | exact resolve eq69 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq650 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X1 X2))) = (M.op X2 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq69 (M.op X0 (M.op X1 X2)) (M.op X1 X2) X2 X1
       have i₂ := eq69 (M.op X1 X2) X0 (M.op X1 X2) X0
       grind)
    | exact superpose eq69 eq69
    | exact resolve eq69 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq690 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq643 X0 X1 x x
       have i₂ := eq69 X0 X0 x x
       grind)
    | exact superpose eq69 eq643
    | exact resolve eq643 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643
  have eq890 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X0) X2)) = (M.op (M.op X3 (M.op X3 X3)) (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq110 X2 X3
       have i₂ := eq121 X2 X0 X1
       grind)
    | exact superpose eq121 eq110
    | exact resolve eq110 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq956 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X1)) = (M.op (M.op X2 X0) (M.op (M.op X0 (M.op X0 X0)) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq121 X1 (M.op X2 X0) (M.op X2 (M.op X2 X2))
       have i₂ := eq110 X0 X2
       grind)
    | exact superpose eq110 eq121
    | exact resolve eq121 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq958 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) (M.op (M.op X3 X0) (M.op (M.op X0 (M.op X0 X0)) X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq197 (M.op X3 X0) (M.op X3 (M.op X3 X3)) X2 X1
       have i₂ := eq110 X0 X3
       grind)
    | exact superpose eq110 eq197
    | exact resolve eq197 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq1401 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op X1 (M.op (M.op X2 X1) X0)))) = (M.op (M.op X3 (M.op (M.op X4 X0) (M.op X4 X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq157 (M.op X1 (M.op (M.op X2 X1) X0)) X3 (M.op X4 X0)
       have i₂ := eq197 X1 X2 X0 X4
       grind)
    | exact superpose eq197 eq157
    | exact resolve eq157 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1521 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op X1 (M.op (M.op X2 X1) X0)))) = (M.op (M.op X3 (M.op X0 (M.op X4 X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1401 X0 X1 X2 X3 X4
       have i₂ := eq63 X4 X0
       grind)
    | exact superpose eq63 eq1401
    | exact resolve eq1401 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1401
  have eq1561 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op (M.op (M.op X2 X1) X0) (M.op X1 (M.op (M.op X2 X1) X0)))) = (M.op (M.op X3 (M.op X0 (M.op X4 X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1521 X0 X1 X2 X3 X4
       have i₂ := eq63 X1 (M.op (M.op X2 X1) X0)
       grind)
    | exact superpose eq63 eq1521
    | exact resolve eq1521 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1521
  have eq1578 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) X0) = (M.op (M.op X3 (M.op X0 (M.op X4 X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1561 X0 X1 X2 X3 X4
       have i₂ := eq197 X1 X2 X0 (M.op X2 X1)
       grind)
    | exact superpose eq197 eq1561
    | exact resolve eq1561 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1561
  have eq1583 : ∀ X0 X3 X4 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 (M.op X4 X0))) X0) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq1578 X0 x x X3 X4
       have i₂ := eq201 x x X0
       grind)
    | exact superpose eq201 eq1578
    | exact resolve eq1578 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201 eq1578
  have eq1601 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X2 (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0)))) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1583 (M.op X1 X0) X2 (M.op x (M.op X1 X1))
       have i₂ := eq157 X0 x X1
       grind)
    | exact superpose eq157 eq1583
    | exact resolve eq1583 eq157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1659 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X2 X0) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1601 X0 X1 X2
       have i₂ := eq125 X0 X1
       grind)
    | exact superpose eq125 eq1601
    | exact resolve eq1601 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1601
  have eq1674 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X0) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1659 X0 X1 X2
       have i₂ := eq63 X1 X0
       grind)
    | exact superpose eq63 eq1659
    | exact resolve eq1659 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1659
  have eq1684 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0))) ∨ (M.op X1 X0) = (k (M.op X1 X0) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq515 (M.op X0 X1)
       have i₂ := eq63 X0 X1
       grind)
    | exact superpose eq63 eq515
    | exact resolve eq515 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1702 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq69 X0 X0 X1 X2
       have i₂ := eq515 X0
       grind)
    | exact superpose eq515 eq69
    | (have j1 := eq515 X0
       grind)
    | exact resolve eq69 eq515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1716 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op (M.op X0 X1) (M.op X0 X1))) ∨ (M.op X0 X1) = (k (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X1) X1 X0
       have i₂ := eq515 (M.op X0 X1)
       grind)
    | exact superpose eq515 eq9
    | (have j1 := eq515 (M.op X0 X1)
       grind)
    | exact resolve eq9 eq515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515
  have eq1724 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X1 (M.op X0 X1))) ∨ (M.op X0 X1) = (k (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1716 X0 X1
       have i₂ := eq63 X0 X1
       grind)
    | exact superpose eq63 eq1716
    | (have j0 := eq1716 X0 X1
       grind)
    | exact resolve eq1716 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1716
  have eq1728 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1702 X0 x x
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq1702
    | (have j0 := eq1702 X0 x x
       grind)
    | exact resolve eq1702 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1702
  have eq1738 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X1 (M.op X0 X1))) ∨ (M.op X0 X1) = (M.op X1 (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1724 X0 X1
       have i₂ := eq63 X0 X1
       grind)
    | exact superpose eq63 eq1724
    | (have j0 := eq1724 X0 X1
       grind)
    | exact resolve eq1724 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq1724
  have eq2342 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq507 X1 X0
       have i₂ := eq506 X1 X0
       grind)
    | exact superpose eq506 eq507
    | (have j0 := eq507 X1 X0
       have j1 := eq506 (σ X1) (σ X0)
       grind)
    | exact resolve eq507 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2344 : ∀ X0 X1 : G, (M.op (σ (σ X1)) (σ (σ X0))) = (σ (σ (k X0 X1))) ∨ (σ (σ X1)) = (M.op (σ (σ X0)) (σ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq507 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq507
    | (have j0 := eq507 (σ X0) (σ X1)
       grind)
    | exact resolve eq507 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2364 : ∀ X0 X1 X2 : G, (σ (k X2 (k X1 X0))) = (k (σ X2) (M.op (σ X0) (σ X1))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k X1 X0)
       have i₂ := eq507 X1 X0
       grind)
    | exact superpose eq507 eq15
    | (have j1 := eq507 X1 X0
       grind)
    | exact resolve eq15 eq507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2366 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq507 X1 X0
       grind)
    | exact superpose eq507 eq10
    | (have j1 := eq507 X1 X0
       grind)
    | exact resolve eq10 eq507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq507
  have eq2754 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X3 X0)) X0) = (M.op (M.op X1 (M.op (M.op (M.op X2 (M.op X3 X0)) X0) (M.op (M.op X2 (M.op X3 X0)) X0))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq199 X0 X3 (M.op (M.op X2 (M.op X3 X0)) X0) X1
       have i₂ := eq198 (M.op X3 X0) X2 X0
       grind)
    | exact superpose eq198 eq199
    | exact resolve eq199 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2759 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 (M.op X3 (M.op X4 X0))) X0) = (M.op (M.op X1 (M.op (M.op (M.op X2 (M.op X3 (M.op X4 X0))) X0) (M.op (M.op X2 (M.op X3 (M.op X4 X0))) X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq199 (M.op X4 X0) X3 (M.op (M.op X2 (M.op X3 (M.op X4 X0))) X0) X1
       have i₂ := eq197 (M.op X3 (M.op X4 X0)) X2 X0 X4
       grind)
    | exact superpose eq197 eq199
    | exact resolve eq199 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2859 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 (M.op X3 (M.op X4 X0))) X0) = (M.op (M.op X1 (M.op X0 (M.op (M.op X2 (M.op X3 (M.op X4 X0))) X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2759 X0 X1 X2 X3 X4
       have i₂ := eq1674 X0 (M.op X2 (M.op X3 (M.op X4 X0))) (M.op X2 (M.op X3 (M.op X4 X0)))
       grind)
    | exact superpose eq1674 eq2759
    | exact resolve eq2759 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2759
  have eq2860 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X3 X0)) X0) = (M.op (M.op X1 (M.op X0 (M.op (M.op X2 (M.op X3 X0)) X0))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2754 X0 X1 X2 X3
       have i₂ := eq1674 X0 (M.op X2 (M.op X3 X0)) (M.op X2 (M.op X3 X0))
       grind)
    | exact superpose eq1674 eq2754
    | exact resolve eq2754 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2754
  have eq2911 : ∀ X0 X2 X3 X4 : G, (M.op X0 X0) = (M.op (M.op X2 (M.op X3 (M.op X4 X0))) X0) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq2859 X0 x X2 X3 X4
       have i₂ := eq1583 X0 x (M.op X2 (M.op X3 (M.op X4 X0)))
       grind)
    | exact superpose eq1583 eq2859
    | exact resolve eq2859 eq1583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2859
  have eq2912 : ∀ X0 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X2 (M.op X3 X0)) X0) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq2860 X0 x X2 X3
       have i₂ := eq1583 X0 x (M.op X2 (M.op X3 X0))
       grind)
    | exact superpose eq1583 eq2860
    | exact resolve eq2860 eq1583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1583 eq2860
  have eq3089 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op X1 (M.op (M.op X2 X1) X0))) = (M.op (M.op X3 (M.op X4 X0)) (M.op X1 (M.op (M.op X2 X1) X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2911 (M.op X1 (M.op (M.op X2 X1) X0)) X3 X4 (M.op x (M.op X0 X0))
       have i₂ := eq199 X1 X2 X0 x
       grind)
    | exact superpose eq199 eq2911
    | exact resolve eq2911 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2911
  have eq3179 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X1) X0) (M.op X1 (M.op (M.op X2 X1) X0))) = (M.op (M.op X3 (M.op X4 X0)) (M.op X1 (M.op (M.op X2 X1) X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq3089 X0 X1 X2 X3 X4
       have i₂ := eq1674 (M.op (M.op X2 X1) X0) X1 X1
       grind)
    | exact superpose eq1674 eq3089
    | exact resolve eq3089 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3089
  have eq3197 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 (M.op X4 X0)) (M.op X1 (M.op (M.op X2 X1) X0))) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq3179 X0 X1 X2 X3 X4
       have i₂ := eq197 X1 X2 X0 (M.op X2 X1)
       grind)
    | exact superpose eq197 eq3179
    | exact resolve eq3179 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3179
  have eq3557 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq205 (M.op X1 X1) x X1 (M.op X0 X0)
       have i₂ := eq120 X1 x X0
       grind)
    | exact superpose eq120 eq205
    | exact resolve eq205 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq3565 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 X3)) (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq205 X3 X2 (M.op X1 (M.op X2 X3)) (M.op X0 X0)
       have i₂ := eq9 X0 (M.op X2 X3) X1
       grind)
    | exact superpose eq9 eq205
    | exact resolve eq205 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3583 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X2 (M.op X3 X1)) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq205 X1 X3 (M.op X2 (M.op X3 X1)) (M.op X0 X1)
       have i₂ := eq205 (M.op X3 X1) X2 X0 X1
       grind)
    | exact superpose eq205 eq205
    | exact resolve eq205 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3650 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 X1)) = (M.op (M.op X2 (M.op X3 X1)) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3583 X0 X1 X2 X3
       have i₂ := eq1674 X1 X0 X0
       grind)
    | exact superpose eq1674 eq3583
    | exact resolve eq3583 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3583
  have eq3660 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 X3)) (M.op X0 X0)) = (M.op X0 (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3565 X0 X1 X2 X3
       have i₂ := eq1674 X0 X3 X0
       grind)
    | exact superpose eq1674 eq3565
    | exact resolve eq3565 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3565
  have eq3666 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3557 X0 X1
       have i₂ := eq1674 X0 (M.op X1 X1) X0
       grind)
    | exact superpose eq1674 eq3557
    | exact resolve eq3557 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3557
  have eq3702 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = (M.op (M.op X1 X1) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3666 (M.op X1 X0) (M.op X1 X1)
       have i₂ := eq157 X0 (M.op X1 X1) X1
       grind)
    | exact superpose eq157 eq3666
    | exact resolve eq3666 eq157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157
  have eq3782 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 (M.op X0 X0)) X2) (M.op (M.op X1 (M.op X0 X0)) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq197 (M.op X0 X0) X1 X2 (M.op X1 (M.op X0 X0))
       have i₂ := eq3666 (M.op (M.op X1 (M.op X0 X0)) X2) X0
       grind)
    | exact superpose eq3666 eq197
    | exact resolve eq197 eq3666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3804 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op (M.op X1 (M.op X0 X0)) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3782 X0 X1 X2
       have i₂ := eq1674 X2 (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X0 X0))
       grind)
    | exact superpose eq1674 eq3782
    | exact resolve eq3782 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3782
  have eq3845 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = (M.op (M.op X1 X1) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3702 X0 X1
       have i₂ := eq1674 X0 X1 X1
       grind)
    | exact superpose eq1674 eq3702
    | exact resolve eq3702 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3702
  have eq3880 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3845 X0 X1
       have i₂ := eq125 X0 X1
       grind)
    | exact superpose eq125 eq3845
    | exact resolve eq3845 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq3845
  have eq3947 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3880 (M.op (M.op X2 X1) X0) X1
       have i₂ := eq197 X1 X2 X0 (M.op X2 X1)
       grind)
    | exact superpose eq197 eq3880
    | exact resolve eq3880 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq4122 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3947 (M.op X0 (M.op X2 X0)) X2 X1
       have i₂ := eq3880 X0 X2
       grind)
    | exact superpose eq3880 eq3947
    | exact resolve eq3947 eq3880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3880
  have eq4245 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3666 X2 X1
       have i₂ := eq3947 X2 X1 X0
       grind)
    | (have i₁ := eq3666 X0 X1
       have i₂ := eq3947 X0 X1 X1
       grind)
    | exact superpose eq3947 eq3666
    | exact resolve eq3666 eq3947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3666 eq3947
  have eq5154 : ∀ X0 X1 X2 X3 : G, (M.op X3 X0) = (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X2 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq69 X0 (M.op X1 (M.op (M.op X2 X3) (M.op X2 X3))) X3 X2
       have i₂ := eq3804 (M.op X2 X3) X1 X0
       grind)
    | exact superpose eq3804 eq69
    | exact resolve eq69 eq3804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq3804
  have eq5177 : ∀ X0 X1 X2 X3 : G, (M.op X3 X0) = (M.op (M.op X1 (M.op X3 (M.op X2 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq5154 X0 X1 X2 X3
       have i₂ := eq1674 X3 X2 X2
       grind)
    | exact superpose eq1674 eq5154
    | exact resolve eq5154 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5154
  have eq8176 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X3) (M.op (M.op X4 (M.op X0 X1)) (M.op (M.op X1 (M.op (M.op X0 X1) (M.op X0 X1))) X3))) = X3 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq289 (M.op X1 (M.op (M.op X0 X1) (M.op X0 X1))) X2 X3 X4
       have i₂ := eq199 X1 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq199 eq289
    | exact resolve eq289 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199 eq289
  have eq8393 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X3) (M.op (M.op X4 (M.op X0 X1)) (M.op (M.op X1 (M.op X1 (M.op X0 X1))) X3))) = X3 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8176 X0 X1 X2 X3 X4
       have i₂ := eq1674 X1 X0 X0
       grind)
    | exact superpose eq1674 eq8176
    | exact resolve eq8176 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8176
  have eq8437 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X3) (M.op (M.op X4 (M.op X0 X1)) (M.op X1 X3))) = X3 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8393 X0 X1 X2 X3 X4
       have i₂ := eq5177 X3 X1 X0 X1
       grind)
    | exact superpose eq5177 eq8393
    | exact resolve eq8393 eq5177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5177 eq8393
  have eq11586 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 X3)) (M.op X3 X0)) = (M.op (M.op (M.op X1 (M.op X2 X3)) (M.op X3 X0)) (M.op X0 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq198 X0 x (M.op (M.op X1 (M.op X2 X3)) (M.op X3 X0))
       have i₂ := eq8437 X2 X3 x X0 X1
       grind)
    | exact superpose eq8437 eq198
    | exact resolve eq198 eq8437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11612 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 X0) = (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq4122 (M.op X4 X0) X1 (M.op X2 (M.op X3 X4))
       have i₂ := eq8437 X3 X4 X4 X0 X2
       grind)
    | exact superpose eq8437 eq4122
    | exact resolve eq4122 eq8437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4122 eq8437
  have eq11690 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X2 X3)) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq11586 X0 X1 X2 X3
       have i₂ := eq3650 X0 X0 (M.op X1 (M.op X2 X3)) X3
       grind)
    | exact superpose eq3650 eq11586
    | exact resolve eq11586 eq3650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3650 eq11586
  have eq13570 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2342 x y
       grind)
    | exact superpose eq2342 eq16
    | (have j1 := eq2342 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq2342 x y
       grind)
    | exact resolve eq16 eq2342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2342
  have eq13631 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq13570
  have eq13640 : (k y y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2366 y y
       have i₂ := eq13631
       grind)
    | exact superpose eq13631 eq2366
    | exact resolve eq2366 eq13631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2366
  have eq13700 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq13640
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq13640
    | exact resolve eq13640 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13640
  have eq13764 : x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq506 y y
       have i₂ := eq13700
       grind)
    | exact superpose eq13700 eq506
    | (have j0 := eq506 y x
       grind)
    | exact resolve eq506 eq13700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13765 : y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq13764
  have eq13822 : x ≠ y ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  have eq14363 : ∀ X0 : G, (σ X0) = (σ (k X0 (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1728 (σ X0)
       have i₂ := eq2364 X0 X0 X0
       grind)
    | exact superpose eq2364 eq1728
    | (have j0 := eq1728 (σ X0)
       have j1 := eq2364 X0 X0 x
       grind)
    | exact resolve eq1728 eq2364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1728 eq2364
  have eq14366 : ∀ X0 : G, (σ X0) = (σ (k X0 (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq14363 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14363
  have eq17453 : ∀ X0 X1 : G, (σ (σ X0)) ≠ (σ (σ (k X0 X0))) ∨ (k X1 (σ (σ X0))) = (M.op (σ (σ X0)) X1) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ (σ X0))
       have i₂ := eq2344 X0 X0
       grind)
    | exact superpose eq2344 eq12
    | (have j0 := eq12 X1 (σ (σ X0))
       have j1 := eq2344 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ (σ X1))
       have r₂ := eq2344 X1 X1
       grind)
    | exact resolve eq12 eq2344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2344
  have eq17519 : ∀ X0 X1 : G, (σ (σ X0)) ≠ (σ (σ (k X0 X0))) ∨ (k X1 (σ (σ X0))) = (M.op (σ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have j0 := eq17453 X0 X1
       have j1 := eq12 X1 (σ (σ X0))
       grind)
    | (have r₁ := eq17453 X0 X1
       have r₂ := eq12 X0 (σ (σ X0))
       grind)
    | exact resolve eq17453 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17453
  have eq18819 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0)) X0) = X0 ∨ (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0)) = (k (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1684 (M.op X0 X0) (M.op x (M.op X0 X0))
       have i₂ := eq9 X0 (M.op X0 X0) x
       grind)
    | exact superpose eq9 eq1684
    | exact resolve eq1684 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18869 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) ≠ (M.op X0 (M.op X1 X0)) ∨ (M.op (M.op X0 (M.op X1 X0)) X2) = (k X2 (M.op X0 (M.op X1 X0))) ∨ (M.op X1 X0) = (k (M.op X1 X0) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq68 (M.op X1 X0) X0 X2
       have i₂ := eq1684 X0 X1
       grind)
    | exact superpose eq1684 eq68
    | (have j0 := eq68 (M.op X1 X0) X0 X2
       have j1 := eq1684 X0 X1
       grind)
    | (have r₁ := eq68 (M.op X1 X0) X0 X2
       have r₂ := eq1684 X0 X1
       grind)
    | exact resolve eq68 eq1684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq18928 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X0)) X2) = (k X2 (M.op X0 (M.op X1 X0))) ∨ (M.op X1 X0) = (k (M.op X1 X0) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq18869 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18869
  have eq18988 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0)) = (k (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq18819 X0 X1
       have i₂ := eq2912 X0 (M.op X1 (M.op X0 X0)) X0
       grind)
    | exact superpose eq2912 eq18819
    | (have j0 := eq18819 X0 X1
       grind)
    | exact resolve eq18819 eq2912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18819
  have eq19050 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op (M.op X0 X0) (M.op X0 X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq18988 X0 x
       have i₂ := eq690 (M.op X0 X0) x
       grind)
    | exact superpose eq690 eq18988
    | (have j0 := eq18988 X0 x
       grind)
    | exact resolve eq18988 eq690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18988
  have eq19091 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 (M.op X0 X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq19050 x
       have i₂ := eq1674 x x x
       grind)
    | exact superpose eq1674 eq19050
    | (have j0 := eq19050 X0
       grind)
    | exact resolve eq19050 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19050
  have eq26042 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op X0 (M.op X1 X0))) ∨ (M.op X1 X0) = (k (M.op X1 X0) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1684 X0 X1
       have i₂ := eq650 X0 X1 X0
       grind)
    | exact superpose eq650 eq1684
    | (have j0 := eq1684 X0 X1
       grind)
    | exact resolve eq1684 eq650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1684
  have eq26366 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X1 X0) (M.op X0 (M.op X1 X0))) ∨ (M.op X1 X0) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | exact superpose eq1738 eq26042
    | (have j0 := eq26042 X0 X1
       have j1 := eq1738 X1 X0
       grind)
    | exact resolve eq26042 eq1738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1738 eq26042
  have eq27951 : ∀ X0 : G, (τ (σ X0)) = (k X0 (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 (k X0 X0))
       have i₂ := eq14366 X0
       grind)
    | exact superpose eq14366 eq10
    | (have j1 := eq14366 X0
       grind)
    | exact resolve eq10 eq14366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14366
  have eq27986 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq27951 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq27951
    | (have j0 := eq27951 X0
       grind)
    | exact resolve eq27951 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27951
  have eq28061 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq27986 X0
       grind)
    | exact superpose eq27986 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq27986 X0
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq27986 X0
       grind)
    | exact resolve eq12 eq27986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28123 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq28061 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28061
  have eq28164 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (τ X0) = (k (τ X0) (k (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq28123 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq28123
    | (have j0 := eq28123 (τ X0) X1
       grind)
    | exact resolve eq28123 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28176 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (k X1 (k X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28123 X1 (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq28123
    | (have j0 := eq28123 X1 X1
       grind)
    | exact resolve eq28123 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28123
  have eq28191 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 (k X0 (σ (τ X0))))) ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq28164 X0 X1
       have i₂ := eq33 X0 (τ X0) X0
       grind)
    | exact superpose eq33 eq28164
    | (have j0 := eq28164 X0 X1
       grind)
    | exact resolve eq28164 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq28164
  have eq28192 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 (k X0 X0))) ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq28191 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq28191
    | (have j0 := eq28191 X0 X1
       grind)
    | exact resolve eq28191 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28191
  have eq28193 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 (M.op X0 X0))) ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28192 X0 X1
       have i₂ := eq506 X0 X0
       grind)
    | exact superpose eq506 eq28192
    | (have j0 := eq28192 X0 X1
       have j1 := eq506 X1 X0
       grind)
    | exact resolve eq28192 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28203 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (k X0 X0)) ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 (k X0 X0))
       have i₂ := eq28192 X0 X1
       grind)
    | exact superpose eq28192 eq11
    | (have j1 := eq28192 X0 X1
       grind)
    | exact resolve eq11 eq28192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28192
  have eq28240 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28203 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq28203
    | (have j0 := eq28203 X0 X1
       grind)
    | exact resolve eq28203 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28203
  have eq28248 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 (M.op X0 X0))) ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq28193 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq28193 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq28193 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28193
  have eq28372 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (M.op X0 X0)) ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 (M.op X0 X0))
       have i₂ := eq28248 X0 X1
       grind)
    | exact superpose eq28248 eq11
    | (have j1 := eq28248 X0 X1
       grind)
    | exact resolve eq11 eq28248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28248
  have eq28409 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28372 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq28372
    | (have j0 := eq28372 X0 X1
       grind)
    | exact resolve eq28372 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28372
  have eq28484 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ y = (k y (M.op y y)) := by
    first
    | (have i₁ := eq13700
       have i₂ := eq28409 y y
       grind)
    | exact superpose eq28409 eq13700
    | (have j1 := eq28409 y x
       grind)
    | exact resolve eq13700 eq28409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28486 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (k y (M.op y y)) := by grind
  clear eq28484
  have eq28488 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (k y y) := by
    first
    | exact superpose eq13765 eq28486
    | exact resolve eq28486 eq13765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13765 eq28486
  have eq28498 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq13700 eq28488
    | exact resolve eq28488 eq13700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13700 eq28488
  have eq28506 : x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq28498
       have r₂ := eq13822
       grind)
    | exact resolve eq28498 eq13822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13822 eq28498
  have eq28512 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq28506 eq13631
    | exact resolve eq13631 eq28506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13631 eq28506
  have eq29149 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (σ x)
       have i₂ := eq28512
       grind)
    | exact superpose eq28512 eq12
    | (have j0 := eq12 X0 (σ x)
       grind)
    | (have r₁ := eq12 X0 (σ x)
       have r₂ := eq28512
       grind)
    | exact resolve eq12 eq28512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29209 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq29149 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29149
  have eq29386 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq29209 (σ X0)
       have i₂ := eq15 X0 x
       grind)
    | exact superpose eq15 eq29209
    | exact resolve eq29209 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29387 : ∀ X0 : G, (k (τ X0) x) = (τ (M.op (σ x) X0)) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq23 X0 x
       have i₂ := eq29209 X0
       grind)
    | exact superpose eq29209 eq23
    | exact resolve eq23 eq29209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq29209
  have eq31191 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq29387 (σ x)
       have i₂ := eq28512
       grind)
    | exact superpose eq28512 eq29387
    | exact resolve eq29387 eq28512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28512 eq29387
  have eq31215 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op y y) := by grind
  clear eq31191
  have eq31223 : x = (k x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq31215
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq31215
    | exact resolve eq31215 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31215
  have eq56343 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X6 X6) = (M.op X5 (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X3 (M.op X4 X5))) X6)))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq642 (M.op X3 (M.op X4 X5)) X2 X6 X5 X4
       have i₂ := eq183 (M.op X4 X5) X3 (M.op (M.op X2 (M.op X3 (M.op X4 X5))) X6) X0 X1
       grind)
    | (have i₁ := eq642 (M.op X3 (M.op X4 X5)) X2 X6 X5 X4
       have i₂ := eq183 X0 X1 (M.op (M.op X2 (M.op X3 (M.op X4 X5))) X6) (M.op X4 X5) X3
       grind)
    | exact superpose eq183 eq642
    | exact resolve eq642 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56950 : ∀ X0 X1 X5 X6 : G, (M.op X6 X6) = (M.op X5 (M.op X0 (M.op (M.op X1 X0) (M.op X5 X6)))) := by
    intro X0 X1 X5 X6
    first
    | (have i₁ := eq56343 X0 X1 x x x X5 X6
       have i₂ := eq11612 X6 x x x X5
       grind)
    | exact superpose eq11612 eq56343
    | exact resolve eq56343 eq11612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56343
  have eq57589 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op (M.op X1 X2) (M.op X0 X0))) = (M.op X2 (M.op X3 (M.op (M.op X4 X3) X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq56950 X3 X4 X2 (M.op (M.op X1 X2) (M.op X0 X0))
       have i₂ := eq9 X0 X2 X1
       grind)
    | exact superpose eq9 eq56950
    | exact resolve eq56950 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58498 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X0) (M.op (M.op X1 X2) (M.op X0 X0))) = (M.op X2 (M.op X3 (M.op (M.op X4 X3) X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq57589 X0 X1 X2 X3 X4
       have i₂ := eq1674 (M.op X0 X0) (M.op X1 X2) (M.op X1 X2)
       grind)
    | exact superpose eq1674 eq57589
    | exact resolve eq57589 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57589
  have eq58689 : ∀ X0 X2 X3 X4 : G, (M.op X2 (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op X2 (M.op X3 (M.op (M.op X4 X3) X0))) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq58498 X0 x X2 X3 X4
       have i₂ := eq4245 x X2 (M.op X0 X0)
       grind)
    | exact superpose eq4245 eq58498
    | exact resolve eq58498 eq4245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58498
  have eq58763 : ∀ X0 X2 X3 X4 : G, (M.op X2 (M.op X0 (M.op X0 X0))) = (M.op X2 (M.op X3 (M.op (M.op X4 X3) X0))) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq58689 X0 X2 X3 X4
       have i₂ := eq1674 X0 X0 X0
       grind)
    | exact superpose eq1674 eq58689
    | exact resolve eq58689 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58689
  have eq59436 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X5 X5) = (M.op X4 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X5)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq642 (M.op X2 (M.op X3 X4)) X1 X5 X4 X3
       have i₂ := eq890 (M.op X3 X4) X2 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X5) X0
       grind)
    | exact superpose eq890 eq642
    | exact resolve eq642 eq890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642 eq890
  have eq59863 : ∀ X0 X4 X5 : G, (M.op X5 X5) = (M.op X4 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X4 X5)))) := by
    intro X0 X4 X5
    first
    | (have i₁ := eq59436 X0 x x x X4 X5
       have i₂ := eq11612 X5 x x x X4
       grind)
    | exact superpose eq11612 eq59436
    | exact resolve eq59436 eq11612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59436
  have eq63045 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) X0) = (M.op (M.op (M.op X1 (M.op X2 (M.op X2 X2))) (M.op X0 X0)) (M.op (M.op (M.op X1 (M.op X2 (M.op X2 X2))) (M.op X0 X0)) (M.op (M.op X1 (M.op X2 (M.op X2 X2))) (M.op X0 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq956 X2 (M.op (M.op X1 (M.op X2 (M.op X2 X2))) (M.op X0 X0)) X3
       have i₂ := eq9 X0 (M.op X2 (M.op X2 X2)) X1
       grind)
    | exact superpose eq9 eq956
    | exact resolve eq956 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq956
  have eq63764 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) X0) = (M.op (M.op X0 X0) (M.op (M.op (M.op X1 (M.op X2 (M.op X2 X2))) (M.op X0 X0)) (M.op (M.op X1 (M.op X2 (M.op X2 X2))) (M.op X0 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq63045 X0 X1 X2 X3
       have i₂ := eq4245 (M.op X1 (M.op X2 (M.op X2 X2))) (M.op X0 X0) (M.op (M.op X1 (M.op X2 (M.op X2 X2))) (M.op X0 X0))
       grind)
    | exact superpose eq4245 eq63045
    | exact resolve eq63045 eq4245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63045
  have eq64095 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) X0) = (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X2 (M.op X2 X2))) (M.op X0 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq63764 X0 X1 X2 X3
       have i₂ := eq1674 (M.op X0 X0) (M.op X1 (M.op X2 (M.op X2 X2))) (M.op X1 (M.op X2 (M.op X2 X2)))
       grind)
    | exact superpose eq1674 eq63764
    | exact resolve eq63764 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63764
  have eq64232 : ∀ X0 X2 X3 : G, (M.op (M.op X3 X2) X0) = (M.op (M.op X0 X0) (M.op (M.op X2 (M.op X2 X2)) (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq64095 X0 x X2 X3
       have i₂ := eq4245 x (M.op X2 (M.op X2 X2)) (M.op X0 X0)
       grind)
    | exact superpose eq4245 eq64095
    | exact resolve eq64095 eq4245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64095
  have eq64311 : ∀ X0 X2 X3 : G, (M.op (M.op X3 X2) X0) = (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X2 (M.op X0 X0)))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq64232 X0 X2 X3
       have i₂ := eq3660 (M.op X0 X0) X2 X2 X2
       grind)
    | exact superpose eq3660 eq64232
    | exact resolve eq64232 eq3660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64232
  have eq64355 : ∀ X0 X2 X3 : G, (M.op (M.op X3 X2) X0) = (M.op (M.op X0 X0) (M.op X0 (M.op X2 (M.op X0 X0)))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq64311 X0 X2 X3
       have i₂ := eq650 X2 X0 X0
       grind)
    | exact superpose eq650 eq64311
    | exact resolve eq64311 eq650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64311
  have eq75018 : ∀ X0 X1 : G, (σ (σ (τ X0))) ≠ (σ (k (σ (τ X0)) X0)) ∨ (k X1 (σ (σ (τ X0)))) = (M.op (σ (σ (τ X0))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17519 (τ X0) X1
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq17519
    | (have j0 := eq17519 (τ X0) X1
       grind)
    | exact resolve eq17519 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17519
  have eq75029 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ (σ (τ X0)))) = (M.op (σ (σ (τ X0))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq75018 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq75018
    | (have j0 := eq75018 X0 X1
       grind)
    | exact resolve eq75018 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75018
  have eq75045 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq75029 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq75029
    | (have j0 := eq75029 X0 X1
       grind)
    | exact resolve eq75029 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75029
  have eq75062 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (k X1 (σ (τ X0))) = (M.op (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq75045 (τ X0) X1
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq75045
    | (have j0 := eq75045 (τ X0) X1
       grind)
    | exact resolve eq75045 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq75045
  have eq75073 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = (M.op (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq75062 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq75062
    | (have j0 := eq75062 X0 X1
       grind)
    | exact resolve eq75062 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75062
  have eq75087 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq75073 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq75073
    | (have j0 := eq75073 X0 X1
       grind)
    | exact resolve eq75073 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75073
  have eq75103 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq75087 x X0
       have i₂ := eq31223
       grind)
    | exact superpose eq31223 eq75087
    | (have j0 := eq75087 x X0
       grind)
    | (have r₁ := eq75087 x x
       have r₂ := eq31223
       grind)
    | exact resolve eq75087 eq31223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31223
  have eq75104 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq75103 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75103
  have eq75106 : ∀ X0 : G, (σ (M.op x X0)) = (M.op (σ x) (σ X0)) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq75104 eq29386
    | exact resolve eq29386 eq75104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29386 eq75104
  have eq75382 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq75106 y
       grind)
    | exact superpose eq75106 eq16
    | (have r₁ := eq16
       have r₂ := eq75106 y
       grind)
    | exact resolve eq16 eq75106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75106
  have eq75517 : x = (M.op y y) := by grind
  clear eq75382
  have eq75664 : ∀ X0 : G, (M.op y (M.op x (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 y y
       have i₂ := eq75517
       grind)
    | exact superpose eq75517 eq9
    | exact resolve eq9 eq75517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75668 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq121 X0 y y
       have i₂ := eq75517
       grind)
    | exact superpose eq75517 eq121
    | exact resolve eq121 eq75517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq75669 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) X0)) = (M.op y (M.op x X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq183 y y X0 X1 X2
       have i₂ := eq75517
       grind)
    | exact superpose eq75517 eq183
    | exact resolve eq183 eq75517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq75673 : ∀ X0 : G, (M.op X0 (M.op y (M.op x X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq198 y y X0
       have i₂ := eq75517
       grind)
    | exact superpose eq75517 eq198
    | exact resolve eq198 eq75517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75674 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op y (M.op x (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq205 y y X0 X1
       have i₂ := eq75517
       grind)
    | exact superpose eq75517 eq205
    | exact resolve eq205 eq75517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq75680 : x = (M.op x y) := by
    first
    | (have i₁ := eq690 y y
       have i₂ := eq75517
       grind)
    | exact superpose eq75517 eq690
    | exact resolve eq690 eq75517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75743 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op y (M.op x (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq56950 y y X1 X0
       have i₂ := eq75517
       grind)
    | exact superpose eq75517 eq56950
    | exact resolve eq56950 eq75517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56950
  have eq75768 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq75680
       grind)
    | exact superpose eq75680 eq16
    | exact resolve eq16 eq75680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75680
  have eq93883 : ∀ X0 X1 : G, (M.op (M.op X1 x) X0) = (M.op X0 (M.op y (M.op y (M.op x X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq75674 (M.op X1 x) X0
       have i₂ := eq75669 X0 x X1
       grind)
    | exact superpose eq75669 eq75674
    | exact resolve eq75674 eq75669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75674
  have eq95142 : ∀ X0 : G, (M.op (M.op x (M.op X0 X0)) (M.op x (M.op X0 X0))) = (M.op y (M.op y (M.op x X0))) := by
    intro X0
    first
    | (have i₁ := eq75743 (M.op x (M.op X0 X0)) y
       have i₂ := eq75664 X0
       grind)
    | exact superpose eq75664 eq75743
    | exact resolve eq75743 eq75664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75743
  have eq95852 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op x (M.op X0 X0))) = (M.op y (M.op y (M.op x X0))) := by
    intro X0
    first
    | (have i₁ := eq95142 X0
       have i₂ := eq1674 (M.op X0 X0) x x
       grind)
    | exact superpose eq1674 eq95142
    | exact resolve eq95142 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95142
  have eq96022 : ∀ X0 : G, (M.op X0 (M.op x (M.op X0 X0))) = (M.op y (M.op y (M.op x X0))) := by
    intro X0
    first
    | (have i₁ := eq95852 X0
       have i₂ := eq650 x X0 X0
       grind)
    | exact superpose eq650 eq95852
    | exact resolve eq95852 eq650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650 eq95852
  have eq175196 : ∀ X0 : G, (M.op y (M.op x X0)) = (M.op x (M.op X0 (M.op y (M.op y (M.op x X0))))) := by
    intro X0
    first
    | (have i₁ := eq75669 X0 x x
       have i₂ := eq93883 X0 x
       grind)
    | exact superpose eq93883 eq75669
    | exact resolve eq75669 eq93883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75669 eq93883
  have eq193508 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k (M.op X1 X0) (M.op X0 (M.op X1 X0))) ∨ (k X2 (M.op X1 X0)) = (M.op (M.op X1 X0) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq26366 eq18928
    | (have j0 := eq18928 X0 X1 X2
       have j1 := eq26366 X0 X1
       grind)
    | exact resolve eq18928 eq26366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18928 eq26366
  have eq202221 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0)) = (k (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0)) X0) ∨ (k X2 (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0))) = (M.op (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq193508 (M.op X0 X0) (M.op X1 (M.op X0 X0)) X2
       have i₂ := eq9 X0 (M.op X0 X0) X1
       grind)
    | exact superpose eq9 eq193508
    | (have j0 := eq193508 (M.op X0 X0) (M.op X1 (M.op X0 X0)) X2
       grind)
    | exact resolve eq193508 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193508
  have eq202331 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op (M.op X0 X0) (M.op X0 X0)) X0) ∨ (k X2 (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0))) = (M.op (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq202221 X0 X1 X2
       have i₂ := eq690 (M.op X0 X0) X1
       grind)
    | exact superpose eq690 eq202221
    | (have j0 := eq202221 X0 X1 X2
       grind)
    | exact resolve eq202221 eq690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202221
  have eq202531 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 (M.op X0 X0)) X0) ∨ (k X2 (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0))) = (M.op (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq202331 X1 X1 X2
       have i₂ := eq1674 X1 X1 X1
       grind)
    | exact superpose eq1674 eq202331
    | (have j0 := eq202331 X0 X1 X2
       grind)
    | exact resolve eq202331 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202331
  have eq202606 : ∀ X0 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X2) = (k X2 (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 (M.op X0 X0)) X0) := by
    intro X0 X2
    first
    | (have i₁ := eq202531 X0 x X2
       have i₂ := eq690 (M.op X0 X0) x
       grind)
    | exact superpose eq690 eq202531
    | (have j0 := eq202531 X0 x X2
       grind)
    | exact resolve eq202531 eq690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690 eq202531
  have eq202646 : ∀ X0 X2 : G, (M.op (M.op X0 (M.op X0 X0)) X2) = (k X2 (M.op X0 (M.op X0 X0))) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 (M.op X0 X0)) X0) := by
    intro X0 X2
    first
    | (have i₁ := eq202606 x X2
       have i₂ := eq1674 x x x
       grind)
    | exact superpose eq1674 eq202606
    | (have j0 := eq202606 X0 X2
       grind)
    | exact resolve eq202606 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1674 eq202606
  have eq202660 : ∀ X0 X2 : G, (M.op (M.op X0 X0) X2) = (k X2 (M.op X0 X0)) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 (M.op X0 X0)) X0) := by
    intro X0 X2
    first
    | exact superpose eq19091 eq202646
    | (have j0 := eq202646 X0 X2
       have j1 := eq19091 X0
       grind)
    | exact resolve eq202646 eq19091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202646
  have eq202669 : ∀ X0 X2 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 (M.op X0 X0)) X0) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X2
    first
    | exact superpose eq19091 eq202660
    | (have j0 := eq202660 X0 X2
       have j1 := eq19091 X0
       grind)
    | exact resolve eq202660 eq19091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19091 eq202660
  have eq363177 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 X4) (M.op (M.op X5 X2) (M.op (M.op X2 (M.op X0 (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X0 X2))))) X4))) = X4 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq958 X2 X3 X4 X5
       have i₂ := eq59863 X1 X0 X2
       grind)
    | exact superpose eq59863 eq958
    | exact resolve eq958 eq59863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq958 eq59863
  have eq364426 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 X4) (M.op (M.op X5 X2) (M.op (M.op X1 (M.op X0 X2)) X4))) = X4 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq363177 X0 X1 X2 X3 X4 X5
       have i₂ := eq11612 X4 X2 X0 (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X0 X2))
       grind)
    | exact superpose eq11612 eq363177
    | exact resolve eq363177 eq11612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11612 eq363177
  have eq369137 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op (M.op X0 X0) (M.op X0 (M.op X1 (M.op X0 X0)))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq198 X1 x X0
       have i₂ := eq64355 X0 X1 x
       grind)
    | exact superpose eq64355 eq198
    | exact resolve eq198 eq64355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64355
  have eq414611 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X1 (k X1 X1)) = X1 := by
    intro X0 X1
    first
    | exact superpose eq28240 eq28176
    | (have j0 := eq28176 X0 X1
       have j1 := eq28240 X1 X1
       grind)
    | exact resolve eq28176 eq28240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28176 eq28240
  have eq428223 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op (M.op X3 X2) X0))) = (M.op X1 (M.op y (M.op x X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq58763 X0 X1 X2 X3
       have i₂ := eq75668 X0
       grind)
    | exact superpose eq75668 eq58763
    | exact resolve eq58763 eq75668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58763 eq75668
  have eq467247 : ∀ X0 : G, (M.op X0 (M.op x (M.op (M.op X0 X0) (M.op y (M.op y (M.op x X0)))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq369137 X0 x
       have i₂ := eq96022 X0
       grind)
    | exact superpose eq96022 eq369137
    | exact resolve eq369137 eq96022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96022 eq369137
  have eq470092 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k X0 (k X0 X0)) = X0 ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq27986 X0
       have i₂ := eq414611 X0 X0
       grind)
    | exact superpose eq414611 eq27986
    | (have j0 := eq27986 X0
       have j1 := eq414611 X0 X0
       grind)
    | exact resolve eq27986 eq414611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq470335 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq470092 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470092
  have eq1196993 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op X0 (M.op X0 (M.op X0 X0))) ∨ (M.op X0 (M.op X0 (M.op X0 X0))) = (k (M.op X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have j0 := eq202669 X0 (M.op X0 (M.op X0 X0))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202669
  have eq1196994 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) ≠ X0 ∨ (M.op X0 (M.op X0 (M.op X0 X0))) = (k (M.op X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq1196993 X0
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq1196993
    | (have j0 := eq1196993 X0
       grind)
    | exact resolve eq1196993 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1196993
  have eq1197130 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) ≠ X0 ∨ (k (M.op X0 (M.op X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1196994 X0
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq1196994
    | (have j0 := eq1196994 X0
       grind)
    | exact resolve eq1196994 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq1196994
  have eq1197418 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X0)) X0) ≠ X0 ∨ (M.op (M.op X1 (M.op X2 X0)) X0) = (k X0 (M.op (M.op X1 (M.op X2 X0)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1197130 (M.op (M.op X1 (M.op X0 X2)) X2)
       have i₂ := eq364426 X0 X1 X2 (M.op X1 (M.op X0 X2)) X2 (M.op X1 (M.op X0 X2))
       grind)
    | exact superpose eq364426 eq1197130
    | exact resolve eq1197130 eq364426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364426 eq1197130
  have eq1197462 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X0 ∨ (M.op (M.op X1 (M.op X2 X0)) X0) = (k X0 (M.op (M.op X1 (M.op X2 X0)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1197418 X0 X1 X2
       have i₂ := eq2912 X0 X1 X2
       grind)
    | exact superpose eq2912 eq1197418
    | (have j0 := eq1197418 X0 X1 X2
       grind)
    | exact resolve eq1197418 eq2912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1197418
  have eq1197559 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1197462 X0 x x
       have i₂ := eq2912 X0 x x
       grind)
    | exact superpose eq2912 eq1197462
    | (have j0 := eq1197462 X0 x x
       grind)
    | exact resolve eq1197462 eq2912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2912 eq1197462
  have eq1197978 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (k (σ X0) (σ (M.op X0 X0))) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1197559 (σ X0)
       have i₂ := eq414611 X0 X0
       grind)
    | exact superpose eq414611 eq1197559
    | (have j1 := eq414611 X0 X0
       grind)
    | exact resolve eq1197559 eq414611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414611 eq1197559
  have eq1197998 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) (σ (M.op X0 X0))) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq1197978 X0
       have j1 := eq470335 X0
       grind)
    | (have r₁ := eq1197978 X0
       have r₂ := eq470335 X0
       grind)
    | exact resolve eq1197978 eq470335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1197978
  have eq1198042 : ∀ X0 : G, (σ (k X0 (M.op X0 X0))) = (σ (M.op X0 X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1197998 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq1197998
    | (have j0 := eq1197998 X0
       grind)
    | exact resolve eq1197998 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1197998
  have eq1198082 : ∀ X0 : G, (σ X0) = (σ (k X0 (M.op X0 X0))) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | exact superpose eq470335 eq1198042
    | (have j0 := eq1198042 X0
       have j1 := eq470335 X0
       grind)
    | exact resolve eq1198042 eq470335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470335 eq1198042
  have eq1200861 : ∀ X0 : G, (τ (σ X0)) = (k X0 (M.op X0 X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 (M.op X0 X0))
       have i₂ := eq1198082 X0
       grind)
    | exact superpose eq1198082 eq10
    | (have j1 := eq1198082 X0
       grind)
    | exact resolve eq10 eq1198082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1198082
  have eq1201519 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1200861 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1200861
    | (have j0 := eq1200861 X0
       grind)
    | exact resolve eq1200861 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1200861
  have eq1201811 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | exact superpose eq28409 eq1201519
    | (have j0 := eq1201519 X0
       have j1 := eq28409 X0 x
       grind)
    | exact resolve eq1201519 eq28409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28409 eq1201519
  have eq1201812 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq1201811 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1201811
  have eq1202131 : ∀ X0 X1 X2 : G, (M.op y (M.op x X0)) = (k (M.op y (M.op x X0)) (M.op (M.op y (M.op x X0)) (M.op X1 (M.op (M.op X2 X1) X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1201812 (M.op y (M.op x X0))
       have i₂ := eq428223 X0 (M.op y (M.op x X0)) X1 X2
       grind)
    | exact superpose eq428223 eq1201812
    | exact resolve eq1201812 eq428223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428223
  have eq1202167 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq29 X0 (M.op (σ X0) (σ X0))
       have i₂ := eq1201812 (σ X0)
       grind)
    | exact superpose eq1201812 eq29
    | exact resolve eq29 eq1201812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1201812
  have eq1202350 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1202167 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1202167
    | exact resolve eq1202167 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1202167
  have eq1202369 : ∀ X0 : G, (M.op y (M.op x X0)) = (k (M.op y (M.op x X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq1202131 X0 x x
       have i₂ := eq3197 X0 x x y x
       grind)
    | exact superpose eq3197 eq1202131
    | exact resolve eq1202131 eq3197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3197 eq1202131
  have eq1203371 : ∀ X0 : G, (k X0 (τ (σ X0))) = X0 ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1202350 X0
       have i₂ := eq27986 X0
       grind)
    | exact superpose eq27986 eq1202350
    | (have j1 := eq27986 X0
       grind)
    | exact resolve eq1202350 eq27986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27986 eq1202350
  have eq1203664 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1203371 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1203371
    | (have j0 := eq1203371 X0
       grind)
    | exact resolve eq1203371 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1203371
  have eq1204045 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq506 X0 (k X0 X0)
       have i₂ := eq1203664 X0
       grind)
    | exact superpose eq1203664 eq506
    | (have j0 := eq506 X0 X0
       have j1 := eq1203664 X0
       grind)
    | exact resolve eq506 eq1203664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1203664
  have eq1204321 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1204045 X0
       have j1 := eq75087 X0 X0
       grind)
    | (have r₁ := eq1204045 X0
       have r₂ := eq75087 X0 x
       grind)
    | exact resolve eq1204045 eq75087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1204045
  have eq1226328 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq198 X0 (k X0 X0) X1
       have i₂ := eq1204321 X0
       grind)
    | exact superpose eq1204321 eq198
    | (have j1 := eq1204321 X0
       grind)
    | exact resolve eq198 eq1204321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198 eq1204321
  have eq1269689 : ∀ X0 : G, (M.op x (M.op (M.op X0 X0) (M.op y (M.op y (M.op x X0))))) = (M.op (M.op x (M.op (M.op X0 X0) (M.op y (M.op y (M.op x X0))))) (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq1226328 X0 (M.op x (M.op (M.op X0 X0) (M.op y (M.op y (M.op x X0)))))
       have i₂ := eq467247 X0
       grind)
    | exact superpose eq467247 eq1226328
    | (have j0 := eq1226328 X0 x
       grind)
    | exact resolve eq1226328 eq467247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467247 eq1226328
  have eq1271464 : ∀ X0 : G, (M.op x (M.op (M.op X0 X0) (M.op y (M.op y (M.op x X0))))) = (M.op X0 (M.op (M.op y (M.op y (M.op x X0))) X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq1269689 X0
       have i₂ := eq3660 X0 x (M.op X0 X0) (M.op y (M.op y (M.op x X0)))
       grind)
    | exact superpose eq3660 eq1269689
    | (have j0 := eq1269689 X0
       grind)
    | exact resolve eq1269689 eq3660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3660 eq1269689
  have eq1271981 : ∀ X0 : G, (M.op (M.op y (M.op x X0)) (M.op X0 X0)) = (M.op x (M.op (M.op X0 X0) (M.op y (M.op y (M.op x X0))))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq1271464 X0
       have i₂ := eq4245 y (M.op y (M.op x X0)) X0
       grind)
    | exact superpose eq4245 eq1271464
    | (have j0 := eq1271464 X0
       grind)
    | exact resolve eq1271464 eq4245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4245 eq1271464
  have eq1272287 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op x (M.op (M.op X0 X0) (M.op y (M.op y (M.op x X0))))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq1271981 X0
       have i₂ := eq11690 X0 y x X0
       grind)
    | exact superpose eq11690 eq1271981
    | (have j0 := eq1271981 X0
       grind)
    | exact resolve eq1271981 eq11690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11690 eq1271981
  have eq1272435 : ∀ X0 : G, (M.op X0 X0) = (M.op x (M.op X0 (M.op y (M.op y (M.op x X0))))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | exact superpose eq506 eq1272287
    | (have j0 := eq1272287 X0
       have j1 := eq506 X0 X0
       grind)
    | exact resolve eq1272287 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1272287
  have eq1272512 : ∀ X0 : G, (M.op X0 X0) = (M.op y (M.op x X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq1272435 X0
       have i₂ := eq175196 X0
       grind)
    | exact superpose eq175196 eq1272435
    | (have j0 := eq1272435 X0
       grind)
    | exact resolve eq1272435 eq175196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175196 eq1272435
  have eq1272551 : ∀ X0 : G, (M.op y (M.op x X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | exact superpose eq506 eq1272512
    | (have j0 := eq1272512 X0
       have j1 := eq506 X0 X0
       grind)
    | exact resolve eq1272512 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506 eq1272512
  have eq1272820 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq1202369 X0
       have i₂ := eq1272551 X0
       grind)
    | exact superpose eq1272551 eq1202369
    | (have j1 := eq1272551 X0
       grind)
    | exact resolve eq1202369 eq1272551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1202369 eq1272551
  have eq1273699 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1272820 X0
       have j1 := eq75087 X0 X0
       grind)
    | (have r₁ := eq1272820 X0
       have r₂ := eq75087 X0 x
       grind)
    | exact resolve eq1272820 eq75087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75087 eq1272820
  have eq1275363 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq1273699 (σ X0)
       grind)
    | exact superpose eq1273699 eq15
    | exact resolve eq15 eq1273699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1275568 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1275363 X0
       have i₂ := eq1273699 X0
       grind)
    | exact superpose eq1273699 eq1275363
    | exact resolve eq1275363 eq1273699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1273699 eq1275363
  have eq1276873 : ∀ X0 : G, (σ X0) = (M.op y (M.op x (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq75664 (σ X0)
       have i₂ := eq1275568 X0
       grind)
    | exact superpose eq1275568 eq75664
    | exact resolve eq75664 eq1275568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75664 eq1275568
  have eq1283500 : (σ y) = (M.op y (M.op x (σ x))) := by
    first
    | (have i₁ := eq1276873 y
       have i₂ := eq75517
       grind)
    | exact superpose eq75517 eq1276873
    | exact resolve eq1276873 eq75517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75517 eq1276873
  have eq1284088 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq75673 (σ x)
       have i₂ := eq1283500
       grind)
    | exact superpose eq1283500 eq75673
    | exact resolve eq75673 eq1283500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75673 eq1283500
  have eq1284552 : False := by grind
  exact eq1284552
