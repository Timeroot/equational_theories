import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2165`: `x = ((y ◇ z) ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_pyx_pyy_pyx_Equation2165 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2165 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2165.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X1 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq25 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X2) X0) X3)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X2) X0) (M.op X1 X0)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X1 X2) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X0) (M.op X1 X2) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op (M.op (M.op (M.op X1 X2) X0) X3) (M.op X1 X0)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X1 X0) (M.op (M.op X1 X2) X0) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq91 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X0 X1 x (M.op X1 X0)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq25
    | exact resolve eq25 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq171 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 (M.op (M.op X0 X1) X2)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27 X2 (M.op X0 X1) (M.op (M.op X0 X1) X2) (M.op X0 (M.op (M.op X0 X1) X2))
       have i₂ := eq27 (M.op (M.op X0 X1) X2) X0 X1 X2
       grind)
    | exact superpose eq27 eq27
    | exact resolve eq27 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq287 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq46 y x
       grind)
    | exact superpose eq46 eq16
    | (have j1 := eq46 y x
       grind)
    | exact resolve eq16 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq289 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (M.op (M.op (σ X1) X2) (σ X0)) (σ (k X0 X1))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) (σ X1) X2
       have i₂ := eq46 X0 X1
       grind)
    | exact superpose eq46 eq9
    | (have j1 := eq46 X0 X1
       grind)
    | exact resolve eq9 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq586 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 (M.op X0 X1)
       have i₂ := eq91 X1 X0
       grind)
    | exact superpose eq91 eq9
    | exact resolve eq9 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq669 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    grind
  have eq894 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq287
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq287
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq287 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287
  have eq897 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq894
  have eq1213 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X0) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq171 (M.op X1 X0) X1 X0
       have i₂ := eq25 X1 X1 X0 X0
       grind)
    | exact superpose eq25 eq171
    | exact resolve eq171 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq1215 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq171 X0 X1 (M.op X0 X0)
       have i₂ := eq26 X0 X0 X1
       grind)
    | exact superpose eq26 eq171
    | exact resolve eq171 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq171
  have eq1252 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1215 X0 X1
       have i₂ := eq586 X0 X0
       grind)
    | exact superpose eq586 eq1215
    | exact resolve eq1215 eq586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1215
  have eq8619 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (σ X1) ∨ (M.op (M.op (M.op (σ X1) X2) X0) (σ (k (τ X0) X1))) = X0 ∨ (M.op (σ X1) (σ X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq289 (τ X0) X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq289
    | exact resolve eq289 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289
  have eq8814 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ X1) X2) X0) (k X0 (σ X1))) = X0 ∨ (M.op X0 X0) = (σ X1) ∨ (M.op (σ X1) (σ X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8619 X0 X1 X2
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq8619
    | (have j0 := eq8619 X0 X1 X2
       grind)
    | exact resolve eq8619 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8619
  have eq15042 : x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1252 x x
       have i₂ := eq897
       grind)
    | exact superpose eq897 eq1252
    | exact resolve eq1252 eq897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq897 eq1252
  have eq15050 : x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq15042
  have eq15233 : ∀ X0 : G, (σ X0) = (M.op (k (σ X0) (σ X0)) (k (σ X0) (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1213 (k (σ X0) (σ X0)) (σ X0)
       have i₂ := eq8814 (σ X0) X0 (k (σ X0) (σ X0))
       grind)
    | exact superpose eq8814 eq1213
    | (have j1 := eq8814 (σ X0) X0 x
       grind)
    | exact resolve eq1213 eq8814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1213 eq8814
  have eq15358 : ∀ X0 : G, (σ X0) = (M.op (k (σ X0) (σ X0)) (k (σ X0) (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq15233 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15233
  have eq15362 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15358 x
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq15358
    | (have j0 := eq15358 X0
       grind)
    | exact resolve eq15358 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15358
  have eq15504 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq586 (σ (k X0 X0)) (σ (k X0 X0))
       have i₂ := eq15362 X0
       grind)
    | exact superpose eq15362 eq586
    | (have j1 := eq15362 X0
       grind)
    | exact resolve eq586 eq15362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15362
  have eq30500 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq669 (σ X0)
       have i₂ := eq15504 X0
       grind)
    | exact superpose eq15504 eq669
    | (have j1 := eq15504 X0
       grind)
    | exact resolve eq669 eq15504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15504
  have eq30620 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq30500 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq30500
    | (have j0 := eq30500 X0
       grind)
    | exact resolve eq30500 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30500
  have eq30621 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq30620 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30620
  have eq30665 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq30621 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq30621
    | exact resolve eq30621 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30740 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq586 X1 (σ X0)
       have i₂ := eq30621 X0
       grind)
    | exact superpose eq30621 eq586
    | exact resolve eq586 eq30621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30743 : ∀ X0 : G, (k (σ X0) (σ (k X0 X0))) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq669 (σ X0)
       have i₂ := eq30621 X0
       grind)
    | exact superpose eq30621 eq669
    | exact resolve eq669 eq30621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30883 : ∀ X0 : G, (σ (k X0 (k X0 X0))) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq30743 X0
       have i₂ := eq15 X0 (k X0 X0)
       grind)
    | exact superpose eq15 eq30743
    | exact resolve eq30743 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30743
  have eq30942 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq30665 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq30665
    | exact resolve eq30665 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq30665
  have eq30969 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq30942 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq30942
    | exact resolve eq30942 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30942
  have eq31682 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq30740 X0 X1
       have i₂ := eq30969 X0
       grind)
    | exact superpose eq30969 eq30740
    | exact resolve eq30740 eq30969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30740
  have eq31737 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq31682 (M.op X0 X0) (M.op x (σ X0))
       have i₂ := eq31682 X0 x
       grind)
    | exact superpose eq31682 eq31682
    | exact resolve eq31682 eq31682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31682
  have eq32049 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq31737 X0
       have i₂ := eq586 X0 X0
       grind)
    | exact superpose eq586 eq31737
    | exact resolve eq31737 eq586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31737
  have eq42039 : ∀ X0 : G, (σ (k X0 (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq30883 X0
       have i₂ := eq30969 X0
       grind)
    | exact superpose eq30969 eq30883
    | exact resolve eq30883 eq30969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30883
  have eq42040 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq42039 X0
       have i₂ := eq669 X0
       grind)
    | exact superpose eq669 eq42039
    | exact resolve eq42039 eq669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669 eq42039
  have eq45803 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq42040 y
       have i₂ := eq15050
       grind)
    | exact superpose eq15050 eq42040
    | exact resolve eq42040 eq15050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15050
  have eq46096 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq45803
       have r₂ := eq16
       grind)
    | exact resolve eq45803 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45803
  have eq46179 : (σ y) = (σ (k x x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq46096
       have i₂ := eq30621 x
       grind)
    | exact superpose eq30621 eq46096
    | exact resolve eq46096 eq30621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46096
  have eq46238 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq46179
       have i₂ := eq30969 x
       grind)
    | exact superpose eq30969 eq46179
    | exact resolve eq46179 eq30969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46179
  have eq46273 : (σ x) = (σ (k y y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq46238
       have i₂ := eq30621 y
       grind)
    | exact superpose eq30621 eq46238
    | exact resolve eq46238 eq30621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46238
  have eq46296 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq46273
       have i₂ := eq30969 y
       grind)
    | exact superpose eq30969 eq46273
    | exact resolve eq46273 eq30969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46273
  have eq68157 : (M.op (σ y) (σ y)) = (σ (M.op (M.op x x) (M.op x x))) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq32049 (M.op x x)
       have i₂ := eq46296
       grind)
    | exact superpose eq46296 eq32049
    | exact resolve eq32049 eq46296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32049 eq46296
  have eq68192 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq68157
       have i₂ := eq586 x x
       grind)
    | exact superpose eq586 eq68157
    | exact resolve eq68157 eq586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586 eq68157
  have eq68252 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq68192
       have i₂ := eq30621 y
       grind)
    | exact superpose eq30621 eq68192
    | exact resolve eq68192 eq30621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30621 eq68192
  have eq68285 : (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq68252
       have i₂ := eq30969 y
       grind)
    | exact superpose eq30969 eq68252
    | exact resolve eq68252 eq30969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30969 eq68252
  have eq68286 : (σ x) = (σ (M.op y y)) := by grind
  clear eq68285
  have eq68364 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq68286
       grind)
    | exact superpose eq68286 eq10
    | exact resolve eq10 eq68286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68286
  have eq68518 : x = (M.op y y) := by
    first
    | (have i₁ := eq68364
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq68364
    | exact resolve eq68364 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68364
  have eq68649 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq42040 y
       have i₂ := eq68518
       grind)
    | exact superpose eq68518 eq42040
    | exact resolve eq42040 eq68518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42040 eq68518
  have eq68793 : False := by grind
  exact eq68793

/-- `Equation2165`: `x = ((y ◇ z) ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pyx_pxy_pyx_Equation2165 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2165 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2165.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) := by
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
  have eq51 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq51 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq51 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq51 (M.op x x)
       have r₂ := eq12 (M.op (M.op x x) (M.op x x)) x
       grind)
    | (have r₁ := eq51 x
       have r₂ := eq12 (k x x) x
       grind)
    | exact resolve eq51 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq55 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq52 (σ X0)
       grind)
    | exact superpose eq52 eq15
    | exact resolve eq15 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq55 X0
       have i₂ := eq52 X0
       grind)
    | exact superpose eq52 eq55
    | exact resolve eq55 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq55
  have eq77 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq84 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq77 X0 X1
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq77
    | (have j0 := eq77 X0 X1
       grind)
    | exact resolve eq77 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq128 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ X1 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq12 (σ (M.op X0 X0)) (σ X0)
       have r₂ := eq62 X0
       grind)
    | exact resolve eq12 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq542 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq84 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq84 X0 X1
       grind)
    | exact superpose eq84 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq84 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq84 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq84 X0 X1
       grind)
    | exact resolve eq13 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq576 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq542 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542
  have eq583 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq576 X0 X1
       have j1 := eq128 X0 (σ X1)
       grind)
    | (have r₁ := eq576 X0 (M.op X0 X0)
       have r₂ := eq128 X0 (M.op (σ X0) (σ X0))
       grind)
    | (have r₁ := eq576 X0 (M.op X0 X0)
       have r₂ := eq128 X0 (σ (M.op X0 X0))
       grind)
    | (have r₁ := eq576 X0 X1
       have r₂ := eq128 X0 (σ X1)
       grind)
    | exact resolve eq576 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq576
  have eq615 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq583 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq583 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq583 X0 X0
       have r₂ := eq12 (k (σ X0) (σ X0)) (σ X0)
       grind)
    | (have r₁ := eq583 X0 X0
       have r₂ := eq12 (σ (k X0 X0)) (σ X0)
       grind)
    | exact resolve eq583 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583
  have eq633 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq615 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq615
    | (have j0 := eq615 X0 X1
       grind)
    | exact resolve eq615 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq615
  have eq634 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq633 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633
  have eq656 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq634 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq634
    | exact resolve eq634 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq669 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq634 x y
       grind)
    | exact superpose eq634 eq16
    | exact resolve eq16 eq634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634
  have eq812 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq656 X0 (τ X1)
       grind)
    | exact superpose eq656 eq17
    | exact resolve eq17 eq656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq656
  have eq827 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq812 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq812
    | exact resolve eq812 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq812
  have eq835 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq827 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq827
    | exact resolve eq827 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827
  have eq934 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq669
       have i₂ := eq835 x y
       grind)
    | exact superpose eq835 eq669
    | exact resolve eq669 eq835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669 eq835
  have eq935 : False := by grind
  exact eq935

/-- `Equation2165`: `x = ((y ◇ z) ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = m(X,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pxy_pyx_pxx_pyx_Equation2165 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2165 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2165.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X1 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq19 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X2) X0) X3)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X2) X0) (M.op X1 X0)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X1 X2) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X0) (M.op X1 X2) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq44 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq45 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq50 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq45 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq45 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq102 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1 x (M.op X1 X0)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq19
    | exact resolve eq19 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq121 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X2 (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20 X2 X1 (M.op (M.op X0 x) (M.op X0 X1))
       have i₂ := eq20 X1 X0 x
       grind)
    | exact superpose eq20 eq20
    | exact resolve eq20 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq162 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq2287 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 (M.op X0 X1)
       have i₂ := eq102 X1 X0
       grind)
    | exact superpose eq102 eq9
    | exact resolve eq9 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq2547 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X0) (M.op X0 X0))) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq121 X0 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq121 X0 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq121
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq121 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq2641 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X0) (M.op X0 X0))) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2547 X0 X1 X2
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq2547 X0 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq2547 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2547
  have eq2653 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2641 X0 X1 x
       have i₂ := eq2287 x X0
       grind)
    | exact superpose eq2287 eq2641
    | (have j0 := eq2641 X0 X1 x
       grind)
    | exact resolve eq2641 eq2287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2287 eq2641
  have eq2656 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq2653 X0 X1
       have j1 := eq162 X0 X1
       grind)
    | (have r₁ := eq2653 X0 X1
       have r₂ := eq162 X0 X1
       grind)
    | (have r₁ := eq2653 X1 X1
       have r₂ := eq162 X1 X1
       grind)
    | exact resolve eq2653 eq162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162 eq2653
  have eq4169 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq2656 (σ X1) (σ X0)
       grind)
    | exact superpose eq2656 eq15
    | exact resolve eq15 eq2656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4182 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4169 X0 X1
       have i₂ := eq2656 X1 X0
       grind)
    | exact superpose eq2656 eq4169
    | exact resolve eq4169 eq2656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2656 eq4169
  have eq4197 : False := by grind
  exact eq4197

/-- `Equation2165`: `x = ((y ◇ z) ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_pxy_y_pyx_Equation2165 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2165 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2165.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X1 X0)) = X0 := by
    intro X0 X1 X2
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
  have eq50 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) (M.op x X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) X0)) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X2) X0) X3)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X2) X0) (M.op X1 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X1 X2) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X1 X0) (M.op X1 X2) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, y = (M.op (M.op (M.op x X0) y) (M.op x y)) := by
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
  have eq55 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) X0) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op (M.op (M.op (M.op X1 X2) X0) X3) (M.op X1 X0)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 X0) (M.op (M.op X1 X2) X0) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq73 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq84 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq16
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq35 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq92 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq11 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq96 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq43
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq43
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq43 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq72
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq72
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq72 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq99 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq73
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq73 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq99
  have eq107 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq96
  have eq108 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq97
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq97
    | exact resolve eq97 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq97
  have eq109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq108
    | exact resolve eq108 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq207 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op (M.op x y) X0) X1)) = X1 := by
    intro X0 X1
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq211 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq51
    | (have j0 := eq51 (σ y)
       grind)
    | exact resolve eq51 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq214 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op (M.op (σ x) (σ y)) X0) X1)) = X1 := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq223 : ∀ X0 : G, (M.op x y) = (M.op y (M.op (M.op x X0) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq224 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op (M.op (M.op (M.op x X0) y) X1) (M.op x y)) y) := by
    intro X0 X1
    first
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq227 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) X0) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq228 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (M.op (σ x) X0) (σ y)) X1) (M.op (σ x) (σ y))) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq378 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op (M.op X0 X1) X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X1 (M.op x X0) (M.op (M.op (M.op x x) x) X0) X2
       have i₂ := eq52 x x x X0
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq393 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) X2) (M.op X0 X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (M.op X1 X0) (M.op X1 x) X0 X2
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq397 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) (M.op y X0)) = X0 := by
    intro X0
    first
    | exact superpose eq54 eq52
    | exact resolve eq52 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq400 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X1 x (M.op X1 X0)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq402 : (M.op x y) = (M.op (M.op y (M.op x y)) y) := by
    first
    | exact superpose eq54 eq52
    | exact resolve eq52 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq403 : (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq55 eq52
    | exact resolve eq52 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq408 : y = (M.op (M.op x y) (M.op y y)) := by
    first
    | exact superpose eq402 eq14
    | exact resolve eq14 eq402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq414 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq403 eq14
    | exact resolve eq14 eq403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq425 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op X2 (M.op X0 (M.op (M.op X1 X0) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X2 (M.op X1 X0) (M.op (M.op (M.op x x) X1) X0)
       have i₂ := eq52 X1 x x X0
       grind)
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq437 : ∀ X0 : G, (M.op y X0) = (M.op X0 (M.op (M.op x y) (M.op y X0))) := by
    intro X0
    first
    | exact superpose eq223 eq53
    | exact resolve eq53 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq441 : ∀ X0 : G, (M.op (σ y) X0) = (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0))) := by
    intro X0
    first
    | exact superpose eq227 eq53
    | exact resolve eq53 eq227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227
  have eq443 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X2 X3) X1) X0) (M.op (M.op (M.op X1 X0) X4) X0)) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 (M.op (M.op (M.op X1 X2) X0) X3) (M.op X0 X3) X2
       have i₂ := eq52 X0 X1 X2 X3
       grind)
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq444 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op (M.op (M.op (M.op X1 X2) X0) X3) X0)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 (M.op X1 X0) (M.op (M.op X1 X2) X0) X2
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq449 : ∀ X0 X1 : G, y = (M.op (M.op x y) (M.op (M.op (M.op (M.op x X0) y) X1) y)) := by
    intro X0 X1
    first
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq452 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (M.op (σ x) X0) (σ y)) X1) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq55 eq53
    | exact resolve eq53 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq473 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op X0 (σ x)) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq55 (M.op (M.op x x) (M.op x sF2))
       have i₂ := eq53 sF2 x x
       grind)
    | exact superpose eq53 eq55
    | exact resolve eq55 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq509 : ∀ X0 X1 X2 X4 : G, (M.op X1 X2) = (M.op (M.op (M.op (M.op (M.op X0 X1) X2) X4) (M.op X1 X2)) X2) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq56 X2 X1 (M.op (M.op X0 x) (M.op X0 X1)) X4
       have i₂ := eq53 X1 X0 x
       grind)
    | exact superpose eq53 eq56
    | exact resolve eq56 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq511 : ∀ X0 X1 X2 X5 : G, (M.op (M.op X1 X0) X2) = (M.op (M.op (M.op (M.op X0 X2) X5) (M.op (M.op X1 X0) X2)) X2) := by
    intro X0 X1 X2 X5
    first
    | (have i₁ := eq56 X2 (M.op X1 X0) (M.op (M.op (M.op x x) X1) X0) X5
       have i₂ := eq52 X1 x x X0
       grind)
    | exact superpose eq52 eq56
    | exact resolve eq56 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq540 : ∀ X0 X1 : G, (M.op (M.op x X0) (M.op x y)) = (M.op (M.op (M.op y X1) (M.op (M.op x X0) (M.op x y))) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq54 eq56
    | exact resolve eq56 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq550 : ∀ X0 X1 X2 X3 : G, (M.op X1 X3) = (M.op (M.op (M.op X0 (M.op (M.op X1 X2) X3)) (M.op X1 X3)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq56 X3 X1 X2 (M.op (M.op X0 x) (M.op X0 (M.op (M.op X1 X2) X3)))
       have i₂ := eq53 (M.op (M.op X1 X2) X3) X0 x
       grind)
    | exact superpose eq53 eq56
    | exact resolve eq56 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq552 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op (M.op (M.op (M.op (M.op (M.op X0 X2) X1) X3) (M.op X0 X1)) X4) X1) X5) (M.op X0 X1)) X1) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq56 X0 (M.op (M.op (M.op (M.op X1 X2) X0) X3) (M.op X1 X0)) X2 X3
       have i₂ := eq56 X0 X1 X2 X3
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq554 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op (M.op (M.op (M.op X1 X2) X0) X3) (M.op X1 X0)) X4) X0) (M.op X1 X0)) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq56 (M.op X1 X0) (M.op (M.op X1 X2) X0) X2 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq555 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op (M.op (M.op (M.op x y) X0) X1) (M.op x X0)) X2) X0) (M.op x X0)) = X0 := by
    intro X0 X1 X2
    first
    | exact superpose eq50 eq56
    | exact resolve eq56 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq559 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op (M.op (M.op (M.op (M.op y (M.op x y)) X0) y) X1) (M.op x y)) y) := by
    intro X0 X1
    first
    | exact superpose eq402 eq56
    | exact resolve eq56 eq402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq561 : ∀ X0 X1 X2 : G, y = (M.op (M.op (M.op (M.op (M.op (M.op (M.op x X0) y) X1) (M.op x y)) X2) y) (M.op x y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq54 eq56
    | exact resolve eq56 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq562 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) X0) (σ y)) X1) (M.op (σ x) (σ y))) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq403 eq56
    | exact resolve eq56 eq403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403
  have eq563 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) (M.op (σ x) (σ y))) X1) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq211 eq56
    | exact resolve eq56 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq573 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 (M.op (M.op X0 X1) X2)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 X2 (M.op X0 X1) (M.op (M.op X0 X1) X2) (M.op X0 (M.op (M.op X0 X1) X2))
       have i₂ := eq56 (M.op (M.op X0 X1) X2) X0 X1 X2
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq969 : ∀ X0 : G, (M.op x X0) = (M.op X0 (M.op (M.op (M.op x y) (M.op (M.op x y) X0)) (M.op x X0))) := by
    intro X0
    first
    | exact superpose eq50 eq207
    | exact resolve eq207 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq1013 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op x y) X1) X0) (M.op (M.op (M.op X1 X0) X2) X0)) = X0 := by
    intro X0 X1 X2
    first
    | exact superpose eq207 eq53
    | exact resolve eq53 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq1091 : ∀ X0 : G, (M.op y X0) = (M.op X0 (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op x y) X0)) (M.op y X0))) := by
    intro X0
    first
    | exact superpose eq397 eq214
    | exact resolve eq214 eq397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214 eq397
  have eq1525 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq393 X0 (M.op X1 x) (M.op X1 X0)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq393
    | exact resolve eq393 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393
  have eq1737 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 (M.op X0 X1)
       have i₂ := eq400 X1 X0
       grind)
    | exact superpose eq400 eq14
    | exact resolve eq14 eq400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2681 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op y (M.op (M.op x X0) y)) y)) := by
    intro X0
    first
    | exact superpose eq437 eq449
    | exact resolve eq449 eq437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437 eq449
  have eq2709 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op x X0) y)) := by
    intro X0
    first
    | (have i₁ := eq2681 X0
       have i₂ := eq400 y (M.op x X0)
       grind)
    | exact superpose eq400 eq2681
    | exact resolve eq2681 eq400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2681
  have eq2763 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) (M.op (M.op (σ x) X0) (σ y))) (σ y))) := by
    intro X0
    first
    | exact superpose eq441 eq452
    | exact resolve eq452 eq441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441 eq452
  have eq2789 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq2763 X0
       have i₂ := eq400 sF3 (M.op sF2 X0)
       grind)
    | exact superpose eq400 eq2763
    | exact resolve eq2763 eq400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2763
  have eq5304 : (M.op y y) = (M.op (M.op x (M.op x y)) y) := by
    first
    | exact superpose eq2709 eq425
    | exact resolve eq425 eq2709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2709
  have eq5309 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq2789 eq425
    | exact resolve eq425 eq2789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2789
  have eq5780 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) (M.op (M.op (σ y) X1) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq473 eq444
    | exact resolve eq444 eq473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444 eq473
  have eq6216 : ∀ X0 X1 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 X0) (M.op X0 X3)) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq573 (M.op X1 x) (M.op (M.op X0 X1) x) x
       have i₂ := eq378 X0 X1 x
       grind)
    | exact superpose eq378 eq573
    | exact resolve eq573 eq378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378
  have eq6358 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq573 X0 X1 (M.op X0 X0)
       have i₂ := eq53 X0 X0 X1
       grind)
    | exact superpose eq53 eq573
    | exact resolve eq573 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq6361 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X0) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq573 (M.op X1 X0) X1 X0
       have i₂ := eq52 X1 X1 X0 X0
       grind)
    | exact superpose eq52 eq573
    | exact resolve eq573 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq573
  have eq6475 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6358 X0 X1
       have i₂ := eq1737 X0 X0
       grind)
    | exact superpose eq1737 eq6358
    | exact resolve eq6358 eq1737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1737 eq6358
  have eq6557 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq26 eq6475
    | (have j0 := eq6475 (σ x) (σ y)
       grind)
    | exact resolve eq6475 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6602 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x X0) (M.op x y)) y) := by
    intro X0
    first
    | (have i₁ := eq224 X0 (M.op (M.op x X0) (M.op x X0))
       have i₂ := eq6475 (M.op x X0) y
       grind)
    | exact superpose eq6475 eq224
    | exact resolve eq224 eq6475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq6604 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq228 X0 (M.op (M.op sF2 X0) (M.op sF2 X0))
       have i₂ := eq6475 (M.op sF2 X0) sF3
       grind)
    | exact superpose eq6475 eq228
    | exact resolve eq228 eq6475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228 eq6475
  have eq7217 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op X0 x) (M.op x y)) y) := by
    intro X0
    first
    | (have i₁ := eq6602 (M.op x (M.op X0 x))
       have i₂ := eq1525 x X0
       grind)
    | exact superpose eq1525 eq6602
    | exact resolve eq6602 eq1525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6602
  have eq7556 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq6604 (M.op sF2 (M.op x sF2))
       have i₂ := eq1525 sF2 x
       grind)
    | exact superpose eq1525 eq6604
    | exact resolve eq6604 eq1525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1525 eq6604
  have eq8541 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq56 X0 (M.op (M.op X0 X0) X1) x X0
       have i₂ := eq443 X0 X0 (M.op (M.op X0 X0) X1) x X1
       grind)
    | exact superpose eq443 eq56
    | exact resolve eq56 eq443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq443
  have eq12413 : ∀ X0 X1 : G, y = (M.op (M.op (M.op (M.op (M.op X0 x) (M.op x y)) X1) y) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq561 sF0 (M.op (M.op X1 x) sF0) x
       have i₂ := eq511 x X1 sF0 y
       grind)
    | exact superpose eq511 eq561
    | exact resolve eq561 eq511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561
  have eq13613 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op (M.op x y) X1)) X1) (M.op x X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq555 x x (M.op (M.op X1 (M.op sF0 x)) x)
       have i₂ := eq511 (M.op sF0 x) X1 x (M.op x x)
       grind)
    | exact superpose eq511 eq555
    | exact resolve eq555 eq511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511 eq555
  have eq15398 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X2) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq554 X1 (M.op X0 X2) x x (M.op X0 X1)
       have i₂ := eq550 (M.op (M.op (M.op (M.op X0 X2) x) X1) x) X0 X2 X1
       grind)
    | exact superpose eq550 eq554
    | exact resolve eq554 eq550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550 eq554
  have eq16133 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq425 (M.op X1 X0) X1 X0
       have i₂ := eq15398 X1 X0 (M.op X1 X0)
       grind)
    | exact superpose eq15398 eq425
    | exact resolve eq425 eq15398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425
  have eq16219 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq91 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq91
    | (have j0 := eq91 x
       grind)
    | exact resolve eq91 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq16284 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq16219
  have eq16287 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16284
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq16284
    | exact resolve eq16284 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16284
  have eq16294 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq16287
       have r₂ := eq13 x (σ x)
       grind)
    | exact resolve eq16287 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16287
  have eq16299 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq16294 eq49
    | exact resolve eq49 eq16294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq16359 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq92 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq92
    | (have j0 := eq92 y
       grind)
    | exact resolve eq92 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq16418 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq16359
  have eq16420 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16418
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq16418
    | exact resolve eq16418 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16418
  have eq16429 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq16420
       have r₂ := eq13 x (σ y)
       grind)
    | exact resolve eq16420 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16420
  have eq16436 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq16429 eq84
    | exact resolve eq84 eq16429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq24199 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq552 X0 X1 x x (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))
       have i₂ := eq509 (M.op (M.op (M.op X0 x) X1) x) (M.op X0 X1) (M.op X0 X1) X1
       grind)
    | exact superpose eq509 eq552
    | exact resolve eq552 eq509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509 eq552
  have eq45987 : (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq16429 eq106
    | exact resolve eq106 eq16429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq45988 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq16294 eq107
    | exact resolve eq107 eq16294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq63654 : (M.op y y) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq45987
       grind)
    | exact superpose eq45987 eq16
    | exact resolve eq16 eq45987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45987
  have eq63739 : (k y y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq16436 eq63654
    | exact resolve eq63654 eq16436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63654
  have eq63742 : (k y y) = (M.op y y) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq63739
       have r₂ := eq13 x y
       grind)
    | exact resolve eq63739 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63739
  have eq63743 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq63742
       grind)
    | exact superpose eq63742 eq73
    | exact resolve eq73 eq63742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq63779 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq16429 eq63743
    | exact resolve eq63743 eq16429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16429 eq63743
  have eq63885 : (M.op x x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq45988
       grind)
    | exact superpose eq45988 eq16
    | exact resolve eq16 eq45988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45988
  have eq63972 : (k x x) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq16299 eq63885
    | exact resolve eq63885 eq16299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63885
  have eq63975 : (k x x) = (M.op x x) := by
    first
    | (have j1 := eq13 x x
       grind)
    | (have r₁ := eq63972
       have r₂ := eq13 x x
       grind)
    | exact resolve eq63972 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63972
  have eq63976 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq63975
       grind)
    | exact superpose eq63975 eq43
    | exact resolve eq43 eq63975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq64012 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | exact superpose eq16294 eq63976
    | exact resolve eq63976 eq16294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16294 eq63976
  have eq71790 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq109 eq11
    | (have j0 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq11 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq71798 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq71790
    | exact resolve eq71790 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq71790
  have eq71809 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq71798
       have r₂ := eq27
       grind)
    | exact resolve eq71798 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71798
  have eq71822 : (τ (σ y)) = (k y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq71809 eq16436
    | exact resolve eq16436 eq71809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16436 eq71809
  have eq71968 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq71822
       have i₂ := eq63742
       grind)
    | exact superpose eq63742 eq71822
    | exact resolve eq71822 eq63742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63742 eq71822
  have eq71979 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq71968
    | exact resolve eq71968 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq71968
  have eq71980 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq71979
  have eq71983 : (τ (σ x)) = (k x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq71980 eq16299
    | exact resolve eq16299 eq71980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16299 eq71980
  have eq72178 : (τ (σ x)) = (M.op x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq71983
       have i₂ := eq63975
       grind)
    | exact superpose eq63975 eq71983
    | exact resolve eq71983 eq63975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63975 eq71983
  have eq72187 : x = (M.op x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq72178
    | exact resolve eq72178 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq72178
  have eq72188 : y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq72187
  have eq72190 : y = (M.op (M.op x y) y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq408
       have i₂ := eq72188
       grind)
    | exact superpose eq72188 eq408
    | exact resolve eq408 eq72188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408
  have eq72206 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq63779
       have i₂ := eq72188
       grind)
    | exact superpose eq72188 eq63779
    | exact resolve eq63779 eq72188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72338 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq72206
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq72206
    | exact resolve eq72206 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72206
  have eq72474 : (M.op y y) = (M.op (M.op y (M.op x y)) y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq72190 eq6361
    | exact resolve eq6361 eq72190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72190
  have eq72481 : (M.op x y) = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq402 eq72474
    | exact resolve eq72474 eq402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402 eq72474
  have eq72634 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq72338 eq414
    | exact resolve eq414 eq72338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414
  have eq72984 : y = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq72188
       have i₂ := eq72481
       grind)
    | exact superpose eq72481 eq72188
    | exact resolve eq72188 eq72481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72188 eq72481
  have eq73099 : x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq72984
  have eq73123 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq64012
       have i₂ := eq73099
       grind)
    | exact superpose eq73099 eq64012
    | exact resolve eq64012 eq73099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73167 : (M.op x y) = (M.op (M.op x (M.op x y)) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq7217 x
       have i₂ := eq73099
       grind)
    | exact superpose eq73099 eq7217
    | exact resolve eq7217 eq73099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7217 eq73099
  have eq73281 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5304 eq73167
    | exact resolve eq73167 eq5304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5304 eq73167
  have eq73306 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq73123
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq73123
    | exact resolve eq73123 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73123
  have eq73478 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq63779
       have i₂ := eq73281
       grind)
    | exact superpose eq73281 eq63779
    | exact resolve eq63779 eq73281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73281
  have eq73603 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq73478
    | exact resolve eq73478 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73478
  have eq73827 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq73306 eq7556
    | exact resolve eq7556 eq73306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7556 eq73306
  have eq73941 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5309 eq73827
    | exact resolve eq73827 eq5309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73827
  have eq75230 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq73941 eq73603
    | exact resolve eq73603 eq73941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73603 eq73941
  have eq75346 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq75230
  have eq75350 : y = (M.op x y) := by
    first
    | (have r₁ := eq75346
       have r₂ := eq27
       grind)
    | exact resolve eq75346 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75346
  have eq75362 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq75350 eq20
    | exact resolve eq20 eq75350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq75668 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq75362
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq75362
    | exact resolve eq75362 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75362
  have eq75677 : ∀ X0 X1 : G, y = (M.op (M.op (M.op (M.op (M.op (M.op y y) X0) y) X1) y) y) := by
    intro X0 X1
    first
    | exact superpose eq75350 eq559
    | exact resolve eq559 eq75350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559
  have eq75678 : ∀ X1 : G, y = (M.op (M.op (M.op (M.op y y) X1) y) y) := by
    intro X1
    first
    | (have i₁ := eq75677 x X1
       have i₂ := eq8541 y x
       grind)
    | exact superpose eq8541 eq75677
    | exact resolve eq75677 eq8541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75677
  have eq75679 : y = (M.op (M.op y y) y) := by
    first
    | (have i₁ := eq75678 x
       have i₂ := eq8541 y x
       grind)
    | exact superpose eq8541 eq75678
    | exact resolve eq75678 eq8541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8541 eq75678
  have eq75788 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ (M.op x y))) := by
    first
    | exact superpose eq75668 eq5309
    | exact resolve eq5309 eq75668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5309
  have eq76236 : ∀ X0 : G, (M.op y X0) = (M.op (M.op y (M.op y X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq6216 y (M.op y y) X0
       have i₂ := eq75679
       grind)
    | exact superpose eq75679 eq6216
    | exact resolve eq6216 eq75679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6216 eq75679
  have eq76247 : ∀ X0 : G, (M.op X0 X0) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq76236 X0
       have i₂ := eq16133 X0 y
       grind)
    | exact superpose eq16133 eq76236
    | exact resolve eq76236 eq16133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16133 eq76236
  have eq76432 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (M.op (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) X0) (σ (M.op x y))) X1) (M.op (σ x) (σ y))) (σ (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq75668 eq562
    | exact resolve eq562 eq75668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq76846 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op y (σ x))) := by
    first
    | (have i₁ := eq6557
       have i₂ := eq76247 sF2
       grind)
    | exact superpose eq76247 eq6557
    | exact resolve eq6557 eq76247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6557
  have eq76907 : (σ y) = (M.op y (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq72338
       have i₂ := eq76247 sF3
       grind)
    | exact superpose eq76247 eq72338
    | exact resolve eq72338 eq76247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72338
  have eq77123 : (σ (M.op x y)) = (M.op y (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq75668 eq76907
    | exact resolve eq76907 eq75668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76907
  have eq77392 : (M.op (σ x) (σ y)) = (M.op (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) (σ (M.op x y))) := by
    first
    | exact superpose eq13613 eq76432
    | exact resolve eq76432 eq13613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13613 eq76432
  have eq77614 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) X0) (M.op (σ x) (σ y))) X1) (σ (M.op x y))) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq75668 eq563
    | exact resolve eq563 eq75668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563
  have eq77847 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq77614 eq24199
    | exact resolve eq24199 eq77614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24199 eq77614
  have eq77848 : (σ (M.op x y)) = (M.op (M.op y (σ (M.op x y))) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq77847
       have i₂ := eq76247 sF1
       grind)
    | exact superpose eq76247 eq77847
    | exact resolve eq77847 eq76247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77847
  have eq81671 : ∀ X0 : G, (M.op x X0) = (M.op X0 (M.op (M.op y (M.op y X0)) (M.op x X0))) := by
    intro X0
    first
    | exact superpose eq75350 eq969
    | exact resolve eq969 eq75350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq969
  have eq82004 : ∀ X0 : G, (M.op (M.op x X0) (M.op x y)) = (M.op (M.op (M.op x y) (M.op (M.op x X0) (M.op x y))) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq540 X0 (M.op (M.op y (M.op y y)) (M.op x y))
       have i₂ := eq81671 y
       grind)
    | exact superpose eq81671 eq540
    | exact resolve eq540 eq81671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540 eq81671
  have eq82141 : ∀ X0 : G, (M.op (M.op x X0) y) = (M.op (M.op (M.op x y) (M.op (M.op x X0) y)) y) := by
    intro X0
    first
    | exact superpose eq75350 eq82004
    | exact resolve eq82004 eq75350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82004
  have eq82246 : ∀ X0 : G, (M.op (M.op x X0) y) = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq82141 X0
       have i₂ := eq15398 x y X0
       grind)
    | exact superpose eq15398 eq82141
    | exact resolve eq82141 eq15398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15398 eq82141
  have eq83948 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op y X1) X0) (M.op (M.op (M.op X1 X0) X2) X0)) = X0 := by
    intro X0 X1 X2
    first
    | exact superpose eq75350 eq1013
    | exact resolve eq1013 eq75350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1013
  have eq84785 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op y (M.op (M.op X0 x) (M.op x y))) (M.op x y)) y) := by
    intro X0
    first
    | exact superpose eq12413 eq83948
    | exact resolve eq83948 eq12413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12413 eq83948
  have eq84990 : ∀ X0 : G, y = (M.op (M.op (M.op y (M.op (M.op X0 x) y)) y) y) := by
    intro X0
    first
    | exact superpose eq75350 eq84785
    | exact resolve eq84785 eq75350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84785
  have eq85317 : ∀ X0 : G, y = (M.op (M.op (M.op X0 x) y) y) := by
    intro X0
    first
    | (have i₁ := eq84990 X0
       have i₂ := eq400 y (M.op X0 x)
       grind)
    | exact superpose eq400 eq84990
    | exact resolve eq84990 eq400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400 eq84990
  have eq86708 : ∀ X0 : G, (M.op y X0) = (M.op X0 (M.op (M.op (M.op (σ x) (σ y)) (M.op y X0)) (M.op y X0))) := by
    intro X0
    first
    | exact superpose eq75350 eq1091
    | exact resolve eq1091 eq75350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1091 eq75350
  have eq87100 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) (M.op (M.op y (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq86708 eq5780
    | exact resolve eq5780 eq86708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5780 eq86708
  have eq87139 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) (M.op (M.op y (σ (M.op x y))) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq75668 eq87100
    | exact resolve eq87100 eq75668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87100
  have eq87279 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq77848 eq87139
    | exact resolve eq87139 eq77848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77848 eq87139
  have eq120886 : (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ (M.op x y))) = (M.op y (σ (M.op x y))) := by
    first
    | (have i₁ := eq75788
       have i₂ := eq76247 sF1
       grind)
    | exact superpose eq76247 eq75788
    | exact resolve eq75788 eq76247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75788
  have eq122225 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq75668 eq72634
    | exact resolve eq72634 eq75668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72634
  have eq122569 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq122225 eq6361
    | exact resolve eq6361 eq122225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6361 eq122225
  have eq122588 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq77392 eq122569
    | exact resolve eq122569 eq77392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77392 eq122569
  have eq122640 : (M.op (σ x) (σ y)) = (M.op y (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq122588
       have i₂ := eq76247 sF1
       grind)
    | exact superpose eq76247 eq122588
    | exact resolve eq122588 eq76247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122588
  have eq124387 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq122640 eq77123
    | exact resolve eq77123 eq122640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77123 eq122640
  have eq124533 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq124387
  have eq124569 : x = (M.op x x) := by
    first
    | (have r₁ := eq124533
       have r₂ := eq27
       grind)
    | exact resolve eq124533 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124533
  have eq124587 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq64012
       have i₂ := eq124569
       grind)
    | exact superpose eq124569 eq64012
    | exact resolve eq64012 eq124569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64012
  have eq124639 : y = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq85317 x
       have i₂ := eq124569
       grind)
    | exact superpose eq124569 eq85317
    | exact resolve eq85317 eq124569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85317 eq124569
  have eq124802 : y = (M.op y y) := by
    first
    | (have i₁ := eq124639
       have i₂ := eq82246 y
       grind)
    | exact superpose eq82246 eq124639
    | exact resolve eq124639 eq82246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82246 eq124639
  have eq124854 : (σ x) = (M.op y (σ x)) := by
    first
    | (have i₁ := eq124587
       have i₂ := eq76247 sF2
       grind)
    | exact superpose eq76247 eq124587
    | exact resolve eq124587 eq76247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124587
  have eq124929 : (σ x) = (M.op y (σ x)) := by
    first
    | (have i₁ := eq124854
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq124854
    | exact resolve eq124854 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq124854
  have eq125014 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq63779
       have i₂ := eq124802
       grind)
    | exact superpose eq124802 eq63779
    | exact resolve eq63779 eq124802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63779 eq124802
  have eq125227 : (σ y) = (M.op y (σ y)) := by
    first
    | (have i₁ := eq125014
       have i₂ := eq76247 sF3
       grind)
    | exact superpose eq76247 eq125014
    | exact resolve eq125014 eq76247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76247 eq125014
  have eq125259 : (σ y) = (M.op y (σ (M.op x y))) := by
    first
    | exact superpose eq75668 eq125227
    | exact resolve eq125227 eq75668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125227
  have eq125272 : (σ y) = (M.op y (σ (M.op x y))) := by
    first
    | (have i₁ := eq125259
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq125259
    | exact resolve eq125259 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq125259
  have eq125283 : (σ (M.op x y)) = (M.op y (σ (M.op x y))) := by
    first
    | exact superpose eq75668 eq125272
    | exact resolve eq125272 eq75668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75668 eq125272
  have eq125299 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq124929 eq76846
    | exact resolve eq76846 eq124929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76846 eq124929
  have eq126984 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ (M.op x y))) := by
    first
    | exact superpose eq125299 eq87279
    | exact resolve eq87279 eq125299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87279 eq125299
  have eq127133 : (M.op (σ x) (σ y)) = (M.op y (σ (M.op x y))) := by
    first
    | exact superpose eq120886 eq126984
    | exact resolve eq126984 eq120886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120886 eq126984
  have eq127184 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq125283 eq127133
    | exact resolve eq127133 eq125283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125283 eq127133
  have eq127218 : False := by grind
  exact eq127218

/-- `Equation2165`: `x = ((y ◇ z) ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pxx_pyy_pyx_Equation2165 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2165 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2165.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X1 X0)) = X0 := by
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
  have eq38 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq59 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 x)
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq15
    | exact resolve eq15 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq47 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq47
    | (have j0 := eq47 y
       grind)
    | exact resolve eq47 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq141 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq59 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq59
    | exact resolve eq59 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq176 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X2) X0) X3)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X3 (M.op (M.op X1 X2) X0) (M.op X1 X0)
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X1 X2) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X1 X0) (M.op X1 X2) X0
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, y = (M.op (M.op (M.op x X0) y) (M.op x y)) := by
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
  have eq179 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) X0) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) (σ x) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op (M.op (M.op (M.op X1 X2) X0) X3) (M.op X1 X0)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op X1 X0) (M.op (M.op X1 X2) X0) X3
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq200 : ∀ X0 : G, (M.op x y) = (M.op y (M.op (M.op x X0) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq204 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) X0) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq643 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
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
  have eq646 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq735 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq737 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq735 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq735 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq735 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735
  have eq739 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X0) (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X0 X1
       have i₂ := eq737 X0
       grind)
    | exact superpose eq737 eq16
    | exact resolve eq16 eq737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq746 : (M.op x y) = (M.op y (M.op (k x x) (M.op x y))) := by
    first
    | (have i₁ := eq200 x
       have i₂ := eq737 x
       grind)
    | exact superpose eq737 eq200
    | exact resolve eq200 eq737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq747 : y = (M.op (M.op (k x x) y) (M.op x y)) := by
    first
    | (have i₁ := eq178 x
       have i₂ := eq737 x
       grind)
    | exact superpose eq737 eq178
    | exact resolve eq178 eq737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq754 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (k (σ x) (σ x)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq204 sF2
       have i₂ := eq737 sF2
       grind)
    | exact superpose eq737 eq204
    | exact resolve eq204 eq737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq1512 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq176 X0 X1 x (M.op X1 X0)
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq176
    | exact resolve eq176 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq1553 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X2 (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq177 X2 X1 (M.op (M.op X0 x) (M.op X0 X1))
       have i₂ := eq177 X1 X0 x
       grind)
    | exact superpose eq177 eq177
    | exact resolve eq177 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1555 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op (k X0 X0) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq177 X1 X0 X0
       have i₂ := eq737 X0
       grind)
    | exact superpose eq737 eq177
    | exact resolve eq177 eq737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3070 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (k X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq739 X1 (M.op X0 X1)
       have i₂ := eq1512 X1 X0
       grind)
    | exact superpose eq1512 eq739
    | exact resolve eq739 eq1512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739 eq1512
  have eq3111 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq643
       grind)
    | exact superpose eq643 eq39
    | exact resolve eq39 eq643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643
  have eq3112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq3111
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3111
    | exact resolve eq3111 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3111
  have eq3114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq3112
    | exact resolve eq3112 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3112
  have eq3116 : (M.op x y) = (k x x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq3114
       have i₂ := eq737 x
       grind)
    | exact superpose eq737 eq3114
    | exact resolve eq3114 eq737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3114
  have eq3118 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq3116
       have i₂ := eq737 x
       grind)
    | exact superpose eq737 eq3116
    | exact resolve eq3116 eq737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3116
  have eq3135 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq3070 X0 X0
       have i₂ := eq737 X0
       grind)
    | exact superpose eq737 eq3070
    | exact resolve eq3070 eq737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3220 : ∀ X0 X1 : G, (k X0 X0) = (M.op X0 (M.op X1 (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 X0) X1 X0
       have i₂ := eq3070 X1 X0
       grind)
    | exact superpose eq3070 eq16
    | exact resolve eq16 eq3070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3070
  have eq3242 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq3135 X0
       have i₂ := eq737 (k X0 X0)
       grind)
    | exact superpose eq737 eq3135
    | exact resolve eq3135 eq737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3135
  have eq3584 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 (M.op (M.op X0 X1) X2)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq180 X2 (M.op X0 X1) (M.op (M.op X0 X1) X2) (M.op X0 (M.op (M.op X0 X1) X2))
       have i₂ := eq180 (M.op (M.op X0 X1) X2) X0 X1 X2
       grind)
    | exact superpose eq180 eq180
    | exact resolve eq180 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq7318 : ∀ X0 X1 : G, (M.op (k X0 X0) (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3220 (k X0 X0) X1
       have i₂ := eq3242 X0
       grind)
    | exact superpose eq3242 eq3220
    | exact resolve eq3220 eq3242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3242
  have eq7602 : (M.op x y) = (M.op (k (M.op x y) (M.op x y)) y) := by
    first
    | exact superpose eq747 eq7318
    | exact resolve eq7318 eq747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7616 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (k (M.op X1 X0) (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq7318 (M.op X1 X0) (k X0 X0)
       have i₂ := eq7318 X0 X1
       grind)
    | exact superpose eq7318 eq7318
    | exact resolve eq7318 eq7318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7623 : y = (M.op (k y y) (M.op x y)) := by
    first
    | (have i₁ := eq7318 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq7318
    | (have j0 := eq7318 y x
       grind)
    | exact resolve eq7318 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq7651 : (σ y) = (M.op (k (σ y) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq7318
    | (have j0 := eq7318 (σ y) (σ x)
       grind)
    | exact resolve eq7318 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq23351 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (k (M.op (M.op x X0) y) (M.op (M.op x X0) y)) y)) := by
    intro X0
    first
    | exact superpose eq178 eq1555
    | exact resolve eq1555 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq23375 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (k (M.op (M.op (σ x) X0) (σ y)) (M.op (M.op (σ x) X0) (σ y))) (σ y))) := by
    intro X0
    first
    | exact superpose eq179 eq1555
    | exact resolve eq1555 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq23422 : (M.op x y) = (M.op (M.op (k x x) (M.op x y)) (M.op (k y y) (M.op x y))) := by
    first
    | exact superpose eq746 eq1555
    | exact resolve eq1555 eq746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746
  have eq23466 : (M.op (σ x) (σ y)) = (M.op (M.op (k (σ x) (σ x)) (M.op (σ x) (σ y))) (M.op (k (σ y) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq754 eq1555
    | exact resolve eq1555 eq754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq754 eq1555
  have eq23719 : (M.op (σ x) (σ y)) = (M.op (M.op (k (σ x) (σ x)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq7651 eq23466
    | exact resolve eq23466 eq7651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23466
  have eq23750 : (M.op x y) = (M.op (M.op (k x x) (M.op x y)) y) := by
    first
    | exact superpose eq7623 eq23422
    | exact resolve eq23422 eq7623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23422
  have eq23786 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq23375 X0
       have i₂ := eq7616 sF3 (M.op sF2 X0)
       grind)
    | exact superpose eq7616 eq23375
    | exact resolve eq23375 eq7616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23375
  have eq23805 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op x X0) y)) := by
    intro X0
    first
    | (have i₁ := eq23351 X0
       have i₂ := eq7616 y (M.op x X0)
       grind)
    | exact superpose eq7616 eq23351
    | exact resolve eq23351 eq7616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7616 eq23351
  have eq24216 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (M.op (σ x) X0) (σ y)) (M.op (M.op X1 (M.op (σ x) (σ y))) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq23786 eq1553
    | exact resolve eq1553 eq23786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23786
  have eq24323 : ∀ X0 X1 : G, y = (M.op (M.op (M.op x X0) y) (M.op (M.op X1 (M.op x y)) y)) := by
    intro X0 X1
    first
    | exact superpose eq23805 eq1553
    | exact resolve eq1553 eq23805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1553 eq23805
  have eq68814 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq24216 eq177
    | exact resolve eq177 eq24216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24216
  have eq68914 : (k (σ y) (σ y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | (have i₁ := eq68814
       have i₂ := eq737 sF3
       grind)
    | exact superpose eq737 eq68814
    | exact resolve eq68814 eq737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68814
  have eq69446 : (M.op y y) = (M.op (M.op x (M.op x y)) y) := by
    first
    | exact superpose eq24323 eq177
    | exact resolve eq177 eq24323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq24323
  have eq69543 : (k y y) = (M.op (M.op x (M.op x y)) y) := by
    first
    | (have i₁ := eq69446
       have i₂ := eq737 y
       grind)
    | exact superpose eq737 eq69446
    | exact resolve eq69446 eq737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69446
  have eq99114 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = (k x x) := by
    first
    | exact superpose eq3118 eq646
    | exact resolve eq646 eq3118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99125 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = (k x x) := by
    first
    | (have r₁ := eq99114
       have r₂ := eq27
       grind)
    | exact resolve eq99114 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99114
  have eq99133 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq99125
       have i₂ := eq737 sF2
       grind)
    | exact superpose eq737 eq99125
    | exact resolve eq99125 eq737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99125
  have eq99137 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq99133
       have i₂ := eq737 sF2
       grind)
    | exact superpose eq737 eq99133
    | exact resolve eq99133 eq737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99133
  have eq100055 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (k X0 X0) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3584 (k X0 X0) X1 X0
       have i₂ := eq7318 X0 (M.op (k X0 X0) X1)
       grind)
    | exact superpose eq7318 eq3584
    | exact resolve eq3584 eq7318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3584 eq7318
  have eq100631 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op (k X0 X0) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq100055 X0 X1
       have i₂ := eq737 X0
       grind)
    | exact superpose eq737 eq100055
    | exact resolve eq100055 eq737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100055
  have eq100744 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = (k x x) := by
    intro X0
    first
    | exact superpose eq99137 eq3220
    | exact resolve eq3220 eq99137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101560 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (M.op X0 (M.op (σ x) (σ y))) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = (k x x) := by
    intro X0
    first
    | exact superpose eq100744 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq100744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100744
  have eq101631 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (M.op X0 (M.op (σ x) (σ y))) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = (k x x) := by
    intro X0
    first
    | (have i₁ := eq101560 X0
       have i₂ := eq737 sF2
       grind)
    | exact superpose eq737 eq101560
    | (have j0 := eq101560 X0
       grind)
    | exact resolve eq101560 eq737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101560
  have eq101662 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (M.op X0 (M.op (σ x) (σ y))) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = (k x x) := by
    intro X0
    first
    | (have j0 := eq101631 X0
       grind)
    | (have r₁ := eq101631 X0
       have r₂ := eq99137
       grind)
    | exact resolve eq101631 eq99137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101631
  have eq101671 : ∀ X0 : G, (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (M.op X0 (M.op (σ x) (σ y))) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = (k x x) := by
    intro X0
    first
    | (have i₁ := eq101662 X0
       have i₂ := eq737 sF2
       grind)
    | exact superpose eq737 eq101662
    | (have j0 := eq101662 X0
       grind)
    | exact resolve eq101662 eq737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101662
  have eq101672 : ∀ X0 : G, (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (M.op X0 (M.op (σ x) (σ y))) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = (k x x) := by
    intro X0
    first
    | (have j0 := eq101671 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101671
  have eq101674 : ∀ X0 : G, (k (σ x) (σ x)) = (k (M.op X0 (M.op (σ x) (σ y))) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = (k x x) := by
    intro X0
    first
    | (have i₁ := eq101672 X0
       have i₂ := eq737 sF2
       grind)
    | exact superpose eq737 eq101672
    | exact resolve eq101672 eq737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101672
  have eq101675 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (M.op X0 (M.op (σ x) (σ y))) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = (k x x) := by
    intro X0
    first
    | exact superpose eq99137 eq101674
    | exact resolve eq101674 eq99137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99137 eq101674
  have eq102422 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = (k x x) := by
    first
    | exact superpose eq7651 eq101675
    | exact resolve eq101675 eq7651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7651 eq101675
  have eq102430 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = (k x x) := by
    first
    | exact superpose eq3118 eq102422
    | exact resolve eq102422 eq3118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3118 eq102422
  have eq102466 : (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = (k x x) := by
    first
    | (have r₁ := eq102430
       have r₂ := eq27
       grind)
    | exact resolve eq102430 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102430
  have eq102525 : (τ (σ x)) = (k (τ (σ x)) x) ∨ (M.op x y) = (k x x) ∨ x = (k x x) := by
    first
    | exact superpose eq102466 eq141
    | exact resolve eq141 eq102466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq102466
  have eq102569 : x = (k x x) ∨ (M.op x y) = (k x x) ∨ x = (k x x) := by
    first
    | exact superpose eq29 eq102525
    | exact resolve eq102525 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102525
  have eq102570 : (M.op x y) = (k x x) ∨ x = (k x x) := by grind
  clear eq102569
  have eq102632 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq102570
       grind)
    | exact superpose eq102570 eq39
    | exact resolve eq39 eq102570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102652 : ∀ X0 : G, (M.op x y) = (M.op x (M.op X0 (M.op x y))) ∨ x = (k x x) := by
    intro X0
    first
    | (have i₁ := eq3220 x x
       have i₂ := eq102570
       grind)
    | exact superpose eq102570 eq3220
    | exact resolve eq3220 eq102570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3220
  have eq102664 : x ≠ (M.op x y) ∨ x = (k x x) := by grind
  have eq102669 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq102632
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq102632
    | exact resolve eq102632 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102632
  have eq102683 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | exact superpose eq20 eq102669
    | exact resolve eq102669 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102669
  have eq103527 : ∀ X0 : G, (M.op x y) ≠ (M.op x x) ∨ x = (M.op x x) ∨ (M.op x x) = (k (M.op X0 (M.op x y)) x) ∨ x = (k x x) := by
    intro X0
    first
    | exact superpose eq102652 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq102652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102652
  have eq103598 : ∀ X0 : G, (M.op x y) ≠ (k x x) ∨ x = (M.op x x) ∨ (M.op x x) = (k (M.op X0 (M.op x y)) x) ∨ x = (k x x) := by
    intro X0
    first
    | (have i₁ := eq103527 X0
       have i₂ := eq737 x
       grind)
    | exact superpose eq737 eq103527
    | (have j0 := eq103527 X0
       grind)
    | exact resolve eq103527 eq737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103527
  have eq103629 : ∀ X0 : G, x = (M.op x x) ∨ (M.op x x) = (k (M.op X0 (M.op x y)) x) ∨ x = (k x x) := by
    intro X0
    first
    | (have j0 := eq103598 X0
       grind)
    | (have r₁ := eq103598 X0
       have r₂ := eq102570
       grind)
    | exact resolve eq103598 eq102570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103598
  have eq103638 : ∀ X0 : G, x = (k x x) ∨ (M.op x x) = (k (M.op X0 (M.op x y)) x) ∨ x = (k x x) := by
    intro X0
    first
    | (have i₁ := eq103629 X0
       have i₂ := eq737 x
       grind)
    | exact superpose eq737 eq103629
    | (have j0 := eq103629 X0
       grind)
    | exact resolve eq103629 eq737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103629
  have eq103639 : ∀ X0 : G, x = (k x x) ∨ (M.op x x) = (k (M.op X0 (M.op x y)) x) := by
    intro X0
    first
    | (have j0 := eq103638 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103638
  have eq103641 : ∀ X0 : G, (k x x) = (k (M.op X0 (M.op x y)) x) ∨ x = (k x x) := by
    intro X0
    first
    | (have i₁ := eq103639 X0
       have i₂ := eq737 x
       grind)
    | exact superpose eq737 eq103639
    | exact resolve eq103639 eq737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103639
  have eq103642 : ∀ X0 : G, (M.op x y) = (k (M.op X0 (M.op x y)) x) ∨ x = (k x x) := by
    intro X0
    first
    | exact superpose eq102570 eq103641
    | exact resolve eq103641 eq102570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102570 eq103641
  have eq107587 : (M.op x y) = (k y x) ∨ x = (k x x) := by
    first
    | exact superpose eq7623 eq103642
    | exact resolve eq103642 eq7623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7623 eq103642
  have eq107618 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq107587
       grind)
    | exact superpose eq107587 eq39
    | exact resolve eq39 eq107587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107587
  have eq107621 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq107618
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq107618
    | exact resolve eq107618 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107618
  have eq107625 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k x x) := by
    first
    | exact superpose eq20 eq107621
    | exact resolve eq107621 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107621
  have eq107630 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | exact superpose eq107625 eq646
    | exact resolve eq646 eq107625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646 eq107625
  have eq107640 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | (have r₁ := eq107630
       have r₂ := eq27
       grind)
    | exact resolve eq107630 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107630
  have eq107647 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq107640
       have i₂ := eq737 sF2
       grind)
    | exact superpose eq737 eq107640
    | exact resolve eq107640 eq737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107640
  have eq107650 : (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq107647
       have i₂ := eq737 sF2
       grind)
    | exact superpose eq737 eq107647
    | exact resolve eq107647 eq737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107647
  have eq107653 : (σ (M.op x y)) = (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | exact superpose eq102683 eq107650
    | exact resolve eq107650 eq102683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107650
  have eq107656 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
    first
    | exact superpose eq102683 eq107653
    | exact resolve eq107653 eq102683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102683 eq107653
  have eq107659 : x = (k x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq107656
       have r₂ := eq27
       grind)
    | exact resolve eq107656 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107656
  have eq107687 : (M.op x y) = (M.op (M.op x (M.op x y)) y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq23750
       have i₂ := eq107659
       grind)
    | exact superpose eq107659 eq23750
    | exact resolve eq23750 eq107659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23750
  have eq107696 : (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq107659
       grind)
    | exact superpose eq107659 eq39
    | exact resolve eq39 eq107659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq107659
  have eq107739 : (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq107696
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq107696
    | exact resolve eq107696 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq107696
  have eq107746 : (M.op x y) = (k y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq69543 eq107687
    | exact resolve eq107687 eq69543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107687
  have eq107988 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq107739 eq23719
    | exact resolve eq23719 eq107739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107739
  have eq108050 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq68914 eq107988
    | exact resolve eq107988 eq68914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68914 eq107988
  have eq108416 : (k y y) = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq108050 eq115
    | exact resolve eq115 eq108050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq108050
  have eq108487 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq107746 eq108416
    | exact resolve eq108416 eq107746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107746 eq108416
  have eq108493 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq108487 eq14
    | exact resolve eq14 eq108487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108487
  have eq108513 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq108493
    | exact resolve eq108493 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108493
  have eq108518 : (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq108513
       have r₂ := eq27
       grind)
    | exact resolve eq108513 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108513
  have eq108519 : (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq108518 eq28
    | exact resolve eq28 eq108518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq108518
  have eq108645 : x = (M.op x y) := by
    first
    | exact superpose eq108519 eq29
    | exact resolve eq29 eq108519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq108646 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq108519 eq14
    | exact resolve eq14 eq108519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108648 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (k X0 (M.op x y))) := by
    intro X0
    first
    | exact superpose eq108519 eq38
    | exact resolve eq38 eq108519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq108519
  have eq108699 : y = (M.op (M.op (k (M.op x y) (M.op x y)) y) (M.op x y)) := by
    first
    | (have i₁ := eq747
       have i₂ := eq108645
       grind)
    | exact superpose eq108645 eq747
    | exact resolve eq747 eq108645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747
  have eq108840 : (k y y) = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq69543
       have i₂ := eq108645
       grind)
    | exact superpose eq108645 eq69543
    | exact resolve eq69543 eq108645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69543
  have eq108848 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq102664
       have i₂ := eq108645
       grind)
    | exact superpose eq108645 eq102664
    | (have r₁ := eq102664
       have r₂ := eq108645
       grind)
    | exact resolve eq102664 eq108645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102664 eq108645
  have eq108855 : (M.op x y) = (k (M.op x y) (M.op x y)) := by grind
  clear eq108848
  have eq108860 : (k y y) = (M.op (k (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq108840
       have i₂ := eq737 sF0
       grind)
    | exact superpose eq737 eq108840
    | exact resolve eq108840 eq737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq737 eq108840
  have eq108892 : y = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq108699
       have i₂ := eq100631 sF0 y
       grind)
    | exact superpose eq100631 eq108699
    | exact resolve eq108699 eq100631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108699
  have eq108902 : (M.op x y) = (k y y) := by
    first
    | exact superpose eq7602 eq108860
    | exact resolve eq108860 eq7602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7602 eq108860
  have eq108916 : y = (M.op x y) := by
    first
    | exact superpose eq108855 eq108892
    | exact resolve eq108892 eq108855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108855 eq108892
  have eq108937 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq108916
       grind)
    | exact superpose eq108916 eq24
    | exact resolve eq24 eq108916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108939 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (k X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq108916
       grind)
    | exact superpose eq108916 eq40
    | exact resolve eq40 eq108916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108916
  have eq109333 : ∀ X0 : G, (k (σ X0) (σ x)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq108648 eq108939
    | exact resolve eq108939 eq108648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108648 eq108939
  have eq109335 : (σ x) = (σ y) := by
    first
    | exact superpose eq108646 eq108937
    | exact resolve eq108937 eq108646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108646 eq108937
  have eq109753 : (M.op (σ x) (σ y)) = (M.op (M.op (k (σ x) (σ x)) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq109335 eq23719
    | exact resolve eq23719 eq109335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23719
  have eq109836 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq109753
       have i₂ := eq100631 sF2 sF4
       grind)
    | exact superpose eq100631 eq109753
    | exact resolve eq109753 eq100631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100631 eq109753
  have eq110699 : (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq108902
       grind)
    | exact superpose eq108902 eq40
    | exact resolve eq40 eq108902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq108902
  have eq110752 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq109333 eq110699
    | exact resolve eq110699 eq109333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109333 eq110699
  have eq110768 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq110752
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq110752
    | exact resolve eq110752 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq110752
  have eq110781 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq109335 eq110768
    | exact resolve eq110768 eq109335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109335 eq110768
  have eq110789 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq109836 eq110781
    | exact resolve eq110781 eq109836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109836 eq110781
  have eq110793 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq110789
    | exact resolve eq110789 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq110789
  have eq110797 : False := by grind
  exact eq110797

/-- `Equation2165`: `x = ((y ◇ z) ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pyx_pxy_pyx_Equation2165 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2165 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2165.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X1 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq20 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X1 X2) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X0) (M.op X1 X2) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
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
  have eq32 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) X0) (M.op X0 X1)) = X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X0 X2
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq27 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq40 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq45 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) X0) (M.op X0 X1)) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq32 X0 X1 X2
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq32 X1 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq32 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq49 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq40 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq40 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq112 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X2 (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20 X2 X1 (M.op (M.op X0 x) (M.op X0 X1))
       have i₂ := eq20 X1 X0 x
       grind)
    | exact superpose eq20 eq20
    | exact resolve eq20 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq138 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq49 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq1185 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq112 (M.op X0 x) X0 X1
       have i₂ := eq45 X0 X1 x
       grind)
    | exact superpose eq45 eq112
    | (have j1 := eq45 X0 X1 x
       grind)
    | exact resolve eq112 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq112
  have eq1236 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1185 X0 X1
       have j1 := eq138 X1 X0
       grind)
    | (have r₁ := eq1185 X0 X1
       have r₂ := eq138 X0 X1
       grind)
    | (have r₁ := eq1185 X1 X0
       have r₂ := eq138 X0 X1
       grind)
    | exact resolve eq1185 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138 eq1185
  have eq34786 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq1236 (σ X0) (σ X1)
       grind)
    | exact superpose eq1236 eq15
    | exact resolve eq15 eq1236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34805 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq34786 X0 X1
       have i₂ := eq1236 X0 X1
       grind)
    | exact superpose eq1236 eq34786
    | exact resolve eq34786 eq1236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1236 eq34786
  have eq34828 : False := by grind
  exact eq34828

/-- `Equation2165`: `x = ((y ◇ z) ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(Y,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_x_pxy_pyx_Equation2165 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2165 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2165.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X1 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
  have eq29 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 x X0
       grind)
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 X0 x
       grind)
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15
    | (have j0 := eq15 X0 y
       grind)
    | exact resolve eq15 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10
    | (have j0 := eq10 x
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 y
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq29 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq29
    | (have j0 := eq29 x
       grind)
    | exact resolve eq29 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq48 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq49 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq52 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) (M.op x X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9
    | (have j0 := eq9 X0 x y
       grind)
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X2) X0) X3)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X2) X0) (M.op X1 X0)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X1 X2) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X0) (M.op X1 X2) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, y = (M.op (M.op (M.op x X0) y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq9 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9
    | (have j0 := eq9 y x X0
       grind)
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op (M.op (M.op (M.op X1 X2) X0) X3) (M.op X1 X0)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X1 X0) (M.op (M.op X1 X2) X0) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) X0) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq9
    | (have j0 := eq9 (σ y) (σ x) X0
       grind)
    | exact resolve eq9 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) X0)) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq9
    | (have j0 := eq9 X0 (σ x) (σ y)
       grind)
    | exact resolve eq9 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq31 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq31
    | (have j0 := eq31 y
       grind)
    | exact resolve eq31 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq71 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq32 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq32
    | (have j0 := eq32 y
       grind)
    | exact resolve eq32 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq79 : y = (M.op (M.op (M.op x y) y) (M.op x y)) := by
    first
    | (have i₁ := eq52 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 y
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 : G, (M.op x X0) = (M.op X0 (M.op (M.op x y) (M.op x X0))) := by
    intro X0
    first
    | exact superpose eq52 eq9
    | exact resolve eq9 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : (M.op x y) = (M.op y (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq79 eq9
    | exact resolve eq9 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq87 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) (M.op y X0)) = X0 := by
    intro X0
    first
    | exact superpose eq83 eq9
    | exact resolve eq9 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq89 : ∀ X0 : G, (M.op x y) = (M.op y (M.op (M.op x X0) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq55 eq9
    | exact resolve eq9 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq57
    | (have j0 := eq57 (σ y)
       grind)
    | exact resolve eq57 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) X0) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq57 eq9
    | exact resolve eq9 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq123 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq66
       have i₂ := eq14 sF3 sF2
       grind)
    | exact superpose eq14 eq66
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq66 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq123
    | exact resolve eq123 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq129 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq127
    | exact resolve eq127 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq131 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq92 eq9
    | exact resolve eq9 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq136 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ y) X0)) = X0 := by
    intro X0
    first
    | exact superpose eq131 eq9
    | exact resolve eq9 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq138 : ∀ X0 : G, (M.op (σ x) X0) = (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0))) := by
    intro X0
    first
    | exact superpose eq58 eq9
    | exact resolve eq9 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq151 : ∀ X0 : G, (M.op y X0) = (M.op X0 (M.op (M.op x y) (M.op y X0))) := by
    intro X0
    first
    | exact superpose eq87 eq9
    | exact resolve eq9 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq156 : ∀ X0 : G, (M.op (σ y) X0) = (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0))) := by
    intro X0
    first
    | exact superpose eq136 eq9
    | exact resolve eq9 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq172 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq48 X1 X0
       grind)
    | exact superpose eq48 eq10
    | exact resolve eq10 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq213 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq172 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq172
    | exact resolve eq172 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172
  have eq325 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq49 X0 (τ X0)
       have i₂ := eq99 (τ X0)
       grind)
    | exact superpose eq99 eq49
    | (have j1 := eq99 (τ X0)
       grind)
    | exact resolve eq49 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq328 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq41
       have i₂ := eq99 sF2
       grind)
    | exact superpose eq99 eq41
    | (have j1 := eq99 (σ x)
       grind)
    | exact resolve eq41 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq329 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq71
       have i₂ := eq99 sF3
       grind)
    | exact superpose eq99 eq71
    | (have j1 := eq99 (σ y)
       grind)
    | exact resolve eq71 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq330 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq325 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq325
    | (have j0 := eq325 X0
       grind)
    | exact resolve eq325 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325
  have eq343 : ∀ X0 X1 : G, y = (M.op (M.op x y) (M.op (M.op (M.op X0 X1) x) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq53 x X0 X1 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq53
    | (have j0 := eq53 x X0 X1 y
       grind)
    | exact resolve eq53 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq346 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op X0 X1) (σ x)) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq53
    | (have j0 := eq53 (σ x) X0 X1 (σ y)
       grind)
    | exact resolve eq53 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq370 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) X2) (M.op X0 X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 (M.op X1 X0) (M.op X1 x) X0 X2
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq53
    | exact resolve eq53 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq381 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0 X1 x (M.op X1 X0)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq53
    | exact resolve eq53 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq383 : (M.op x y) = (M.op (M.op y (M.op x y)) y) := by
    first
    | exact superpose eq55 eq53
    | exact resolve eq53 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq390 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X4) (M.op (M.op X1 X0) X4)) = X4 := by
    intro X0 X1 X4
    first
    | (have i₁ := eq9 X4 (M.op X1 X0) (M.op (M.op (M.op x x) X1) X0)
       have i₂ := eq53 X1 x x X0
       grind)
    | exact superpose eq53 eq9
    | exact resolve eq9 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq392 : y = (M.op (M.op x y) (M.op y y)) := by
    first
    | exact superpose eq383 eq9
    | exact resolve eq9 eq383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383
  have eq399 : ∀ X0 : G, (M.op (M.op y X0) (M.op (M.op x y) X0)) = X0 := by
    intro X0
    first
    | exact superpose eq392 eq9
    | exact resolve eq9 eq392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392
  have eq413 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op X0 (M.op y (M.op (M.op x y) X0))) := by
    intro X0
    first
    | exact superpose eq399 eq9
    | exact resolve eq9 eq399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq437 : (M.op (σ x) x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) x)) (M.op (M.op x y) (M.op (σ x) x))) := by
    first
    | exact superpose eq138 eq80
    | exact resolve eq80 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq472 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op X0 x) y)) := by
    intro X0
    first
    | exact superpose eq136 eq343
    | exact resolve eq343 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343
  have eq512 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (σ x)) (σ y))) := by
    intro X0
    first
    | exact superpose eq136 eq346
    | exact resolve eq346 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346
  have eq623 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op X0 (M.op (M.op X1 X2) (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X2 X0) (M.op X1 X2) X0
       have i₂ := eq370 X2 X1 X0
       grind)
    | exact superpose eq370 eq9
    | exact resolve eq9 eq370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq662 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op (M.op (M.op (M.op X1 X2) X0) X3) X0)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq54 (M.op X1 X0) (M.op (M.op X1 X2) X0) X2
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq54
    | exact resolve eq54 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq665 : ∀ X0 X1 : G, (M.op (M.op x X0) (M.op (M.op (M.op (M.op x y) X0) X1) X0)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq52 eq54
    | exact resolve eq54 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq668 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X1) X0)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq58 eq54
    | exact resolve eq54 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq672 : ∀ X0 X1 : G, y = (M.op (M.op x y) (M.op (M.op (M.op (M.op x X0) y) X1) y)) := by
    intro X0 X1
    first
    | exact superpose eq55 eq54
    | exact resolve eq54 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq674 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (M.op (σ x) X0) (σ y)) X1) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq57 eq54
    | exact resolve eq54 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq681 : ∀ X0 X1 : G, y = (M.op (M.op (M.op X0 x) y) (M.op (M.op (M.op x y) X1) y)) := by
    intro X0 X1
    first
    | exact superpose eq472 eq54
    | exact resolve eq54 eq472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472
  have eq698 : ∀ X0 X1 : G, (M.op X0 x) = (M.op (M.op (M.op X0 X1) (M.op X0 x)) (M.op (M.op x y) (M.op X0 x))) := by
    intro X0 X1
    first
    | (have i₁ := eq80 (M.op (M.op X1 x) (M.op X1 x))
       have i₂ := eq54 x X1 x
       grind)
    | exact superpose eq54 eq80
    | exact resolve eq80 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq699 : ∀ X0 : G, (M.op x y) = (M.op y (M.op (M.op X0 x) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq89 (M.op (M.op X0 x) (M.op X0 x))
       have i₂ := eq54 x X0 x
       grind)
    | exact superpose eq54 eq89
    | exact resolve eq89 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq744 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X2) X1) X3) X1) = (M.op (M.op (M.op (M.op X0 X1) X4) (M.op (M.op (M.op (M.op X0 X2) X1) X3) X1)) X1) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq56 X1 (M.op (M.op (M.op X0 X2) X1) X3) (M.op X0 X1) X4
       have i₂ := eq56 X1 X0 X2 X3
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq798 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 (M.op (M.op X0 X1) X2)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 X2 (M.op X0 X1) (M.op (M.op X0 X1) X2) (M.op X0 (M.op (M.op X0 X1) X2))
       have i₂ := eq56 (M.op (M.op X0 X1) X2) X0 X1 X2
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq802 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op (M.op (M.op (M.op X0 X2) X1) X3) (M.op X0 X1)) X4) X1) (M.op X0 X1)) = X1 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 X1 (M.op (M.op (M.op (M.op X0 X2) X1) X3) (M.op X0 X1)) X4
       have i₂ := eq56 X1 X0 X2 X3
       grind)
    | exact superpose eq56 eq9
    | exact resolve eq9 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq804 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X1) = (M.op X1 (M.op (M.op (M.op (M.op (M.op (M.op X0 X2) X1) X3) (M.op X0 X1)) X4) (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq54 X0 (M.op (M.op (M.op (M.op X1 X2) X0) X3) (M.op X1 X0)) X2
       have i₂ := eq56 X0 X1 X2 X3
       grind)
    | exact superpose eq56 eq54
    | exact resolve eq54 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq892 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op (M.op X0 x) (M.op x y)) (M.op (M.op y X1) (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq699 eq54
    | exact resolve eq54 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq948 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 (M.op X0 X1)
       have i₂ := eq381 X1 X0
       grind)
    | exact superpose eq381 eq9
    | exact resolve eq9 eq381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1002 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq948 X1 (M.op X0 X0)
       have i₂ := eq948 X0 X0
       grind)
    | exact superpose eq948 eq948
    | exact resolve eq948 eq948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1005 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X1 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) X1 X0
       have i₂ := eq948 X1 X0
       grind)
    | exact superpose eq948 eq9
    | exact resolve eq9 eq948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1008 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq948 X0 X0
       grind)
    | exact superpose eq948 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | exact resolve eq12 eq948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1012 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op X2 (M.op X0 (M.op (M.op X1 X0) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X2 (M.op X1 X0) (M.op X0 X0)
       have i₂ := eq948 X1 X0
       grind)
    | exact superpose eq948 eq54
    | exact resolve eq54 eq948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1686 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq114 X0 X1
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq114
    | (have j0 := eq114 X0 X1
       have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq114 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq1846 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq1002 X0 X1
       grind)
    | exact superpose eq1002 eq9
    | exact resolve eq9 eq1002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1849 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq56 X1 X0 x (M.op (M.op X0 X1) (M.op X0 X1))
       have i₂ := eq1002 (M.op X0 X1) (M.op (M.op X0 x) X1)
       grind)
    | exact superpose eq1002 eq56
    | exact resolve eq56 eq1002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1853 : y = (M.op (M.op y y) (M.op x y)) := by
    first
    | (have i₁ := eq55 (M.op y y)
       have i₂ := eq1002 y x
       grind)
    | exact superpose eq1002 eq55
    | exact resolve eq55 eq1002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq1862 : (σ y) = (M.op (M.op (σ y) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq57 (M.op sF3 sF3)
       have i₂ := eq1002 sF3 sF2
       grind)
    | exact superpose eq1002 eq57
    | exact resolve eq57 eq1002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq1002
  have eq2054 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) ≠ X0 ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op (M.op X1 X0) (M.op X0 X0)) = (k (M.op X1 X0) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X1 X0) (M.op X0 X0)
       have i₂ := eq1846 X0 X1
       grind)
    | exact superpose eq1846 eq13
    | (have j0 := eq13 (M.op X1 X0) (M.op X0 X0)
       grind)
    | exact resolve eq13 eq1846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2067 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op (M.op X1 X0) (M.op X0 X0)) = (k (M.op X1 X0) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2054 X0 X1
       grind)
    | (have r₁ := eq2054 X1 X1
       have r₂ := eq948 X1 X1
       grind)
    | exact resolve eq2054 eq948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2054
  have eq2068 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op (M.op X1 X0) (M.op X0 X0)) = (k (M.op X1 X0) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2067 X0 X1
       have i₂ := eq948 X0 X0
       grind)
    | exact superpose eq948 eq2067
    | (have j0 := eq2067 X0 X1
       grind)
    | exact resolve eq2067 eq948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2067
  have eq2069 : ∀ X0 X1 : G, (k (M.op X1 X0) (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2068 X0 X1
       have i₂ := eq948 X1 X0
       grind)
    | exact superpose eq948 eq2068
    | (have j0 := eq2068 X0 X1
       grind)
    | exact resolve eq2068 eq948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2068
  have eq2418 : (M.op y x) = (M.op (M.op (M.op x y) (M.op y x)) (M.op (M.op x y) (M.op y x))) := by
    first
    | exact superpose eq151 eq80
    | exact resolve eq80 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2580 : ∀ X0 : G, (M.op (M.op (M.op x y) (M.op y X0)) (M.op (M.op x y) (M.op y X0))) = (M.op y (M.op (M.op x y) (M.op y X0))) := by
    intro X0
    first
    | exact superpose eq413 eq54
    | exact resolve eq54 eq413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413
  have eq2621 : (M.op y x) = (M.op y (M.op (M.op x y) (M.op y x))) := by
    first
    | exact superpose eq2580 eq2418
    | exact resolve eq2418 eq2580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2418
  have eq2969 : ∀ X0 : G, (M.op (M.op x X0) (M.op (M.op x (M.op (M.op x y) X0)) X0)) = X0 := by
    intro X0
    first
    | exact superpose eq80 eq665
    | exact resolve eq665 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq2974 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op x (M.op (M.op x y) X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq665 (M.op sF0 X0) X0
       have i₂ := eq9 X0 sF0 (M.op sF0 X0)
       grind)
    | exact superpose eq9 eq665
    | exact resolve eq665 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665
  have eq2996 : ∀ X0 : G, (M.op (M.op x X0) (M.op (M.op x y) X0)) = X0 := by
    intro X0
    first
    | exact superpose eq2974 eq2969
    | exact resolve eq2969 eq2974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2969
  have eq3042 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq668 (M.op sF4 X0) X0
       have i₂ := eq9 X0 sF4 (M.op sF4 X0)
       grind)
    | exact superpose eq9 eq668
    | exact resolve eq668 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668
  have eq3068 : ∀ X0 : G, (M.op X0 (M.op x x)) = (M.op (M.op x x) (M.op (M.op x y) (M.op X0 (M.op x x)))) := by
    intro X0
    first
    | (have i₁ := eq2996 (M.op X0 (M.op x x))
       have i₂ := eq1005 x X0
       grind)
    | exact superpose eq1005 eq2996
    | exact resolve eq2996 eq1005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3093 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op X0 (M.op x (M.op (M.op x y) X0))) := by
    intro X0
    first
    | exact superpose eq2996 eq9
    | exact resolve eq9 eq2996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2996
  have eq3180 : (M.op (M.op x y) (M.op x x)) = (M.op (M.op x x) (M.op x x)) := by
    first
    | (have i₁ := eq2974 (M.op x x)
       have i₂ := eq1005 x sF0
       grind)
    | exact superpose eq1005 eq2974
    | exact resolve eq2974 eq1005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3225 : x = (M.op (M.op x y) (M.op x x)) := by
    first
    | (have i₁ := eq3180
       have i₂ := eq948 x x
       grind)
    | exact superpose eq948 eq3180
    | exact resolve eq3180 eq948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3180
  have eq3271 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq3042 (M.op sF2 sF2)
       have i₂ := eq1005 sF2 sF4
       grind)
    | exact superpose eq1005 eq3042
    | exact resolve eq3042 eq1005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3042
  have eq3316 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq3271
       have i₂ := eq948 sF2 sF2
       grind)
    | exact superpose eq948 eq3271
    | exact resolve eq3271 eq948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3271
  have eq3808 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op y (M.op (M.op x X0) y)) y)) := by
    intro X0
    first
    | exact superpose eq151 eq672
    | exact resolve eq672 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151 eq672
  have eq3839 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op x X0) y)) := by
    intro X0
    first
    | (have i₁ := eq3808 X0
       have i₂ := eq381 y (M.op x X0)
       grind)
    | exact superpose eq381 eq3808
    | exact resolve eq3808 eq381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3808
  have eq3874 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) (M.op (M.op (σ x) X0) (σ y))) (σ y))) := by
    intro X0
    first
    | exact superpose eq156 eq674
    | exact resolve eq674 eq156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156 eq674
  have eq3901 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq3874 X0
       have i₂ := eq381 sF3 (M.op sF2 X0)
       grind)
    | exact superpose eq381 eq3874
    | exact resolve eq3874 eq381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3874
  have eq5517 : (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq329
       have i₂ := eq99 y
       grind)
    | exact superpose eq99 eq329
    | (have j1 := eq99 (σ y)
       grind)
    | exact resolve eq329 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5880 : ∀ X0 : G, (M.op x (M.op (M.op x y) (M.op X0 x))) = (M.op (M.op (M.op x y) (M.op X0 x)) (M.op (M.op x y) (M.op X0 x))) := by
    intro X0
    first
    | exact superpose eq3093 eq623
    | exact resolve eq623 eq3093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3093
  have eq7681 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op y x) (M.op x y)) := by
    first
    | exact superpose eq892 eq54
    | exact resolve eq54 eq892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq892
  have eq12994 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op (M.op X0 X1) X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq662 X2 X0 X1 (M.op (M.op X0 X1) X2)
       have i₂ := eq1849 (M.op X0 X1) X2
       grind)
    | exact superpose eq1849 eq662
    | exact resolve eq662 eq1849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1849
  have eq13489 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 X2) (M.op X1 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12994 (M.op X1 X2) X0 (M.op X1 X0)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12994
    | exact resolve eq12994 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13490 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op (M.op X1 X2) (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12994 (M.op X1 X2) X0 (M.op X2 X0)
       have i₂ := eq370 X2 X1 X0
       grind)
    | exact superpose eq370 eq12994
    | exact resolve eq12994 eq370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370
  have eq14513 : (M.op y y) = (M.op (M.op (M.op x y) x) y) := by
    first
    | exact superpose eq681 eq54
    | exact resolve eq54 eq681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq681
  have eq14938 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X1 X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq798 X1 X0 (M.op X0 X1)
       have i₂ := eq623 X1 X1 X0
       grind)
    | exact superpose eq623 eq798
    | exact resolve eq798 eq623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623
  have eq14939 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq798 X0 X1 (M.op X0 X0)
       have i₂ := eq1005 X0 (M.op X0 X1)
       grind)
    | exact superpose eq1005 eq798
    | exact resolve eq798 eq1005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14940 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X0) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq798 (M.op X1 X0) X1 X0
       have i₂ := eq390 X1 (M.op X1 X0) X0
       grind)
    | exact superpose eq390 eq798
    | exact resolve eq798 eq390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14971 : (M.op (σ y) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) := by
    first
    | exact superpose eq512 eq798
    | exact resolve eq798 eq512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512
  have eq15276 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14939 X0 X1
       have i₂ := eq948 X0 X0
       grind)
    | exact superpose eq948 eq14939
    | exact resolve eq14939 eq948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq948 eq14939
  have eq15805 : ∀ X0 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0) (M.op (M.op (σ y) (σ y)) X0)) = X0 := by
    intro X0
    first
    | exact superpose eq14971 eq12994
    | exact resolve eq12994 eq14971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15830 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op x y) X0) (M.op x (M.op (M.op x y) X0))) X0) := by
    intro X0
    first
    | exact superpose eq2974 eq14940
    | exact resolve eq14940 eq2974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15844 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X1 X2) X0) X3) X0) (M.op (M.op (M.op (M.op X1 X2) X0) X3) X0)) = (M.op (M.op X0 (M.op X1 X0)) (M.op (M.op (M.op (M.op X1 X2) X0) X3) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14940 (M.op (M.op (M.op (M.op X1 X2) X0) X3) X0) (M.op X1 X0)
       have i₂ := eq662 X0 X1 X2 X3
       grind)
    | exact superpose eq662 eq14940
    | exact resolve eq14940 eq662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15845 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) (M.op (M.op X1 X2) X0)) = (M.op (M.op X0 (M.op X1 X0)) (M.op (M.op X1 X2) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14940 (M.op (M.op X1 X2) X0) (M.op X1 X0)
       have i₂ := eq12994 X1 X2 X0
       grind)
    | exact superpose eq12994 eq14940
    | exact resolve eq14940 eq12994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15956 : (M.op (M.op (M.op x y) (M.op y x)) (M.op (M.op x y) (M.op y x))) = (M.op (M.op (M.op y x) y) (M.op (M.op x y) (M.op y x))) := by
    first
    | exact superpose eq2621 eq14940
    | exact resolve eq14940 eq2621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16278 : (M.op y (M.op (M.op x y) (M.op y x))) = (M.op (M.op (M.op y x) y) (M.op (M.op x y) (M.op y x))) := by
    first
    | exact superpose eq2580 eq15956
    | exact resolve eq15956 eq2580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2580 eq15956
  have eq16315 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X0)) (M.op (M.op (M.op (M.op X1 X2) X0) X3) X0)) = (M.op (M.op X0 (M.op (M.op (M.op X1 X2) X0) X0)) (M.op (M.op (M.op (M.op X1 X2) X0) X3) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq15844 X0 X1 X2 X3
       have i₂ := eq15845 X0 (M.op (M.op X1 X2) X0) X3
       grind)
    | exact superpose eq15845 eq15844
    | exact resolve eq15844 eq15845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15844
  have eq16332 : (M.op y x) = (M.op (M.op (M.op y x) y) (M.op (M.op x y) (M.op y x))) := by
    first
    | exact superpose eq2621 eq16278
    | exact resolve eq16278 eq2621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2621 eq16278
  have eq18492 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq39 eq330
    | exact resolve eq330 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq330
  have eq18522 : (σ (k y y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq71 eq18492
    | exact resolve eq18492 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18492
  have eq22634 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op (M.op y X1) (M.op x y)) (M.op (M.op X0 x) (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq699 eq13489
    | exact resolve eq13489 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699
  have eq22699 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X1) (σ y)) (M.op (M.op (σ x) X0) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq3901 eq13489
    | exact resolve eq13489 eq3901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3901 eq13489
  have eq23886 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op X0 (σ y))) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15805 (M.op x sF3)
       have i₂ := eq1846 sF3 x
       grind)
    | exact superpose eq1846 eq15805
    | exact resolve eq15805 eq1846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15805
  have eq31346 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op (M.op y X0) (M.op x y)) x) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq22634 eq798
    | exact resolve eq798 eq22634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798 eq22634
  have eq36377 : ∀ X0 : G, x = (M.op (M.op (M.op y X0) x) (M.op (M.op (M.op x y) (M.op x y)) x)) := by
    intro X0
    first
    | exact superpose eq31346 eq662
    | exact resolve eq662 eq31346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662 eq31346
  have eq39240 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op x y)) X2) (M.op X0 (M.op x y))) X3) (M.op X0 (M.op x y))) = (M.op (M.op y (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op x y)) X2) (M.op X0 (M.op x y))) X3) (M.op X0 (M.op x y)))) (M.op X0 (M.op x y))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq399 (M.op (M.op (M.op (M.op (M.op (M.op X0 X2) sF0) X3) (M.op X0 sF0)) x) (M.op X0 sF0))
       have i₂ := eq804 X0 sF0 X2 X3 x
       grind)
    | exact superpose eq804 eq399
    | exact resolve eq399 eq804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399
  have eq44996 : (M.op x y) = (k y (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq1853 eq2069
    | (have j0 := eq2069 (M.op x y) x
       grind)
    | exact resolve eq2069 eq1853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45051 : (M.op (σ x) (σ y)) = (k (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1862 eq2069
    | (have j0 := eq2069 (M.op (σ x) (σ y)) x
       grind)
    | exact resolve eq2069 eq1862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1862 eq2069
  have eq47614 : (M.op (M.op (M.op x y) (M.op (σ x) x)) (M.op (M.op x y) (M.op (σ x) x))) = (M.op (M.op (M.op (σ x) x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) x))) (M.op (M.op x y) (M.op (σ x) x))) := by
    first
    | exact superpose eq437 eq14940
    | exact resolve eq14940 eq437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437
  have eq47616 : (M.op (M.op (M.op (σ x) x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) x))) (M.op (M.op x y) (M.op (σ x) x))) = (M.op x (M.op (M.op x y) (M.op (σ x) x))) := by
    first
    | exact superpose eq5880 eq47614
    | exact resolve eq47614 eq5880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5880 eq47614
  have eq56653 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) X2) X3) X2) X4) X2) (M.op X0 X2)) = X2 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq802 X0 X2 X1 X2 (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) X2) X3) X2) X4) X2)
       have i₂ := eq744 (M.op (M.op X0 X1) X2) X2 X3 X4 (M.op X0 X2)
       grind)
    | exact superpose eq744 eq802
    | exact resolve eq802 eq744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744 eq802
  have eq59424 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1012 (M.op X1 X0) X1 X0
       have i₂ := eq12994 X1 (M.op X1 X0) X0
       grind)
    | exact superpose eq12994 eq1012
    | exact resolve eq1012 eq12994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59438 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y))) (σ y)) := by
    intro X0
    first
    | exact superpose eq22699 eq1012
    | exact resolve eq1012 eq22699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22699
  have eq59715 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op x y)) x) (M.op (M.op X0 (M.op x y)) x)) = (M.op (M.op x y) (M.op (M.op X0 (M.op x y)) x)) := by
    intro X0
    first
    | (have i₁ := eq2974 (M.op (M.op x sF0) x)
       have i₂ := eq1012 sF0 x x
       grind)
    | exact superpose eq1012 eq2974
    | exact resolve eq2974 eq1012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1012 eq2974
  have eq59942 : ∀ X0 : G, (M.op (M.op x (M.op X0 x)) (M.op (M.op X0 (M.op x y)) x)) = (M.op (M.op x y) (M.op (M.op X0 (M.op x y)) x)) := by
    intro X0
    first
    | (have i₁ := eq59715 x
       have i₂ := eq15845 x x sF0
       grind)
    | exact superpose eq15845 eq59715
    | exact resolve eq59715 eq15845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59715
  have eq60061 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op (M.op (M.op (M.op X0 X2) X1) X3) (M.op X0 X1)) X4) (M.op X0 X1)) (M.op (M.op (M.op (M.op (M.op (M.op X0 X2) X1) X3) (M.op X0 X1)) X4) (M.op X0 X1))) = (M.op (M.op X1 (M.op X0 X1)) (M.op (M.op (M.op (M.op (M.op (M.op X0 X2) X1) X3) (M.op X0 X1)) X4) (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq59424 (M.op (M.op (M.op (M.op (M.op (M.op X0 X2) X1) X3) (M.op X0 X1)) X4) (M.op X0 X1)) X1
       have i₂ := eq804 X0 X1 X2 X3 X4
       grind)
    | exact superpose eq804 eq59424
    | exact resolve eq59424 eq804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60138 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op (M.op (M.op X1 X2) X0) X0) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq59424 (M.op X1 X0) (M.op (M.op X1 X2) X0)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq59424
    | exact resolve eq59424 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60144 : ∀ X0 : G, (M.op (M.op (M.op (M.op x y) (M.op x y)) x) (M.op (M.op (M.op x y) (M.op x y)) x)) = (M.op (M.op (M.op (M.op y X0) x) x) (M.op (M.op (M.op x y) (M.op x y)) x)) := by
    intro X0
    first
    | exact superpose eq36377 eq59424
    | exact resolve eq59424 eq36377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36377
  have eq61120 : ∀ X0 : G, (M.op (M.op x (M.op (M.op x y) x)) (M.op (M.op (M.op x y) (M.op x y)) x)) = (M.op (M.op (M.op (M.op y X0) x) x) (M.op (M.op (M.op x y) (M.op x y)) x)) := by
    intro X0
    first
    | (have i₁ := eq60144 X0
       have i₂ := eq15845 x sF0 sF0
       grind)
    | exact superpose eq15845 eq60144
    | exact resolve eq60144 eq15845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60144
  have eq61136 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) (M.op (M.op (M.op (M.op (M.op X0 X2) X1) X3) (M.op X0 X1)) (M.op X0 X1))) (M.op (M.op (M.op (M.op (M.op (M.op X0 X2) X1) X3) (M.op X0 X1)) X4) (M.op X0 X1))) = (M.op (M.op X1 (M.op X0 X1)) (M.op (M.op (M.op (M.op (M.op (M.op X0 X2) X1) X3) (M.op X0 X1)) X4) (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq60061 X0 X1 X2 X3 X4
       have i₂ := eq15845 (M.op X0 X1) (M.op (M.op (M.op (M.op X0 X2) X1) X3) (M.op X0 X1)) X4
       grind)
    | exact superpose eq15845 eq60061
    | exact resolve eq60061 eq15845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60061
  have eq61242 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op (M.op x y) (M.op x y)) x)) = (M.op (M.op (M.op (M.op y X0) x) x) (M.op (M.op (M.op x y) (M.op x y)) x)) := by
    intro X0
    first
    | exact superpose eq59942 eq61120
    | exact resolve eq61120 eq59942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59942 eq61120
  have eq61245 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) (M.op (M.op (M.op X0 X2) X1) (M.op X0 X1))) (M.op (M.op (M.op (M.op (M.op (M.op X0 X2) X1) X3) (M.op X0 X1)) X4) (M.op X0 X1))) = (M.op (M.op X1 (M.op X0 X1)) (M.op (M.op (M.op (M.op (M.op (M.op X0 X2) X1) X3) (M.op X0 X1)) X4) (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq61136 X0 X1 X2 X3 X4
       have i₂ := eq16315 (M.op X0 X1) (M.op (M.op X0 X2) X1) X3 X4
       grind)
    | exact superpose eq16315 eq61136
    | exact resolve eq61136 eq16315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61136
  have eq61300 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X1) (M.op (M.op (M.op (M.op (M.op (M.op X0 X2) X1) X3) (M.op X0 X1)) X4) (M.op X0 X1))) = (M.op (M.op X1 (M.op X0 X1)) (M.op (M.op (M.op (M.op (M.op (M.op X0 X2) X1) X3) (M.op X0 X1)) X4) (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq61245 X0 X1 X2 X3 X4
       have i₂ := eq9 X1 X0 X2
       grind)
    | exact superpose eq9 eq61245
    | exact resolve eq61245 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61245
  have eq92614 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op x y)) X2) (M.op X0 (M.op x y))) X3) (M.op X0 (M.op x y))) (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op x y)) X2) (M.op X0 (M.op x y))) X3) (M.op X0 (M.op x y)))) = (M.op (M.op (M.op X0 (M.op x y)) (M.op x (M.op X0 (M.op x y)))) (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op x y)) X2) (M.op X0 (M.op x y))) X3) (M.op X0 (M.op x y)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq15830 (M.op (M.op (M.op (M.op (M.op (M.op X0 X2) sF0) X3) (M.op X0 sF0)) x) (M.op X0 sF0))
       have i₂ := eq804 X0 sF0 X2 X3 x
       grind)
    | exact superpose eq804 eq15830
    | exact resolve eq15830 eq804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15830
  have eq93010 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op x y)) (M.op x (M.op X0 (M.op x y)))) (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op x y)) X2) (M.op X0 (M.op x y))) X3) (M.op X0 (M.op x y)))) = (M.op (M.op (M.op X0 (M.op x y)) (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op x y)) X2) (M.op X0 (M.op x y))) (M.op X0 (M.op x y)))) (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op x y)) X2) (M.op X0 (M.op x y))) X3) (M.op X0 (M.op x y)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq92614 X0 X1 X2 X2
       have i₂ := eq15845 (M.op X0 sF0) (M.op (M.op (M.op (M.op X0 X1) sF0) X2) (M.op X0 sF0)) X2
       grind)
    | exact superpose eq15845 eq92614
    | exact resolve eq92614 eq15845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92614
  have eq93044 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op x y)) (M.op x (M.op X0 (M.op x y)))) (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op x y)) X2) (M.op X0 (M.op x y))) X3) (M.op X0 (M.op x y)))) = (M.op (M.op (M.op X0 (M.op x y)) (M.op (M.op (M.op X0 X1) (M.op x y)) (M.op X0 (M.op x y)))) (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op x y)) X2) (M.op X0 (M.op x y))) X3) (M.op X0 (M.op x y)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq93010 X0 X1 X2 X3
       have i₂ := eq16315 (M.op X0 sF0) (M.op (M.op X0 X1) sF0) X2 X3
       grind)
    | exact superpose eq16315 eq93010
    | exact resolve eq93010 eq16315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16315 eq93010
  have eq93067 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op x y)) (M.op x (M.op X0 (M.op x y)))) (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op x y)) X2) (M.op X0 (M.op x y))) X3) (M.op X0 (M.op x y)))) = (M.op (M.op (M.op X0 (M.op x y)) (M.op x y)) (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op x y)) X2) (M.op X0 (M.op x y))) X3) (M.op X0 (M.op x y)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq93044 X1 X2 X2 X3
       have i₂ := eq9 sF0 X1 X2
       grind)
    | exact superpose eq9 eq93044
    | exact resolve eq93044 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93044
  have eq93080 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op x y)) (M.op x (M.op X0 (M.op x y)))) (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op x y)) X2) (M.op X0 (M.op x y))) X3) (M.op X0 (M.op x y)))) = (M.op (M.op (M.op x y) (M.op X0 (M.op x y))) (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op x y)) X2) (M.op X0 (M.op x y))) X3) (M.op X0 (M.op x y)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq93067 X0 X2 X3 x
       have i₂ := eq61300 X0 sF0 X2 X3 x
       grind)
    | exact superpose eq61300 eq93067
    | exact resolve eq93067 eq61300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61300 eq93067
  have eq120885 : (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1686 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1686
    | (have j0 := eq1686 x y
       grind)
    | exact resolve eq1686 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1686
  have eq120933 : (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq120885
    | exact resolve eq120885 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120885
  have eq120934 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq120933
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq120933
    | exact resolve eq120933 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120933
  have eq120935 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq120934
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq120934
    | exact resolve eq120934 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120934
  have eq120936 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq120935
    | exact resolve eq120935 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120935
  have eq120937 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq120936
       have r₂ := eq27
       grind)
    | exact resolve eq120936 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120936
  have eq120938 : (M.op (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq120937
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq120937
    | exact resolve eq120937 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120937
  have eq120939 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq120938
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq120938
    | exact resolve eq120938 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120938
  have eq120940 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq120939
    | exact resolve eq120939 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120939
  have eq120941 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq120940
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq120940
    | exact resolve eq120940 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120940
  have eq121123 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq120941 eq15276
    | exact resolve eq15276 eq120941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121130 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq120941
  have eq121169 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq121123 eq45051
    | exact resolve eq45051 eq121123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45051 eq121123
  have eq121343 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq121169
       have r₂ := eq121130
       grind)
    | exact resolve eq121169 eq121130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121130 eq121169
  have eq121348 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq66 eq121343
    | exact resolve eq121343 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq121343
  have eq121673 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq121348
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq121348
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq121348 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121348
  have eq121706 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq121673
  have eq121716 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq121706
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq121706
    | exact resolve eq121706 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121706
  have eq121722 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq121716
    | exact resolve eq121716 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121716
  have eq121725 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq121722
       have r₂ := eq27
       grind)
    | exact resolve eq121722 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121722
  have eq121727 : (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq121725
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq121725
    | exact resolve eq121725 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121725
  have eq121728 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq121727
  have eq121823 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq121728 eq1008
    | (have r₁ := eq1008 (σ x) x
       have r₂ := eq121728
       grind)
    | (have r₁ := eq1008 x x
       have r₂ := eq121728
       grind)
    | exact resolve eq1008 eq121728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121728
  have eq121910 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq121823 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121823
  have eq122183 : ∀ X0 : G, (τ X0) = (k (τ X0) (τ (σ x))) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2⟩ := hcon
    have f122183_14 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
      intro X0 X1
      grind
    have f122183_15 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
      intro X0
      grind
    have f122183_24 : (τ X0) ≠ (k (τ X0) (τ (σ x))) := by grind
    have f122183_25 : (M.op x y) ≠ (M.op x x) := by grind
    have f122183_26 : x ≠ (M.op x x) := by grind
    have f122183_27 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
      intro X0
      first
      | (have j0 := f122183_15 X0
         grind)
      | (have r₁ := f122183_15 X0
         have r₂ := f122183_25
         grind)
      | exact resolve f122183_15 f122183_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f122183_28 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
      intro X0
      first
      | (have j0 := f122183_27 X0
         grind)
      | (have r₁ := f122183_27 X0
         have r₂ := f122183_26
         grind)
      | exact resolve f122183_27 f122183_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f122183_32 : (τ X0) ≠ (τ (k X0 (σ x))) := by
      first
      | (have i₁ := f122183_24
         have i₂ := f122183_14 X0 (σ x)
         grind)
      | exact superpose f122183_14 f122183_24
      | exact resolve f122183_24 f122183_14
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f122183_33 : (τ X0) ≠ (τ X0) := by
      first
      | (have i₁ := f122183_32
         have i₂ := f122183_28 X0
         grind)
      | exact superpose f122183_28 f122183_32
      | exact resolve f122183_32 f122183_28
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f122183_34 : False := by grind
    exact f122183_34
  clear eq121910
  have eq122247 : ∀ X0 : G, (τ X0) = (k (τ X0) x) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq38 eq122183
    | exact resolve eq122183 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122183
  have eq122271 : ∀ X0 : G, (τ X0) = (k (τ X0) x) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq122247 X0
       have j1 := eq12 (τ X0) x
       grind)
    | (have r₁ := eq122247 X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq122247 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122247
  have eq122285 : ∀ X0 : G, (k X0 x) = X0 ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq122271 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq122271
    | exact resolve eq122271 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122271
  have eq122417 : x = (M.op x x) ∨ x = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq99 x
       have i₂ := eq122285 x
       grind)
    | exact superpose eq122285 eq99
    | (have j0 := eq99 x
       grind)
    | exact resolve eq99 eq122285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122285
  have eq122467 : (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq122417
  have eq123409 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq122467
       grind)
    | exact superpose eq122467 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq122467
       grind)
    | exact resolve eq13 eq122467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123481 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq15276 x x
       have i₂ := eq122467
       grind)
    | exact superpose eq122467 eq15276
    | exact resolve eq15276 eq122467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15276
  have eq123488 : x ≠ (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq122467
  have eq123490 : x = (M.op x y) ∨ (M.op x y) = (k x x) ∨ x = (M.op x x) := by grind
  clear eq123409
  have eq123495 : (M.op x y) = (k x x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq123490
       have r₂ := eq123488
       grind)
    | exact resolve eq123490 eq123488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123490
  have eq123755 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq123481 eq44996
    | exact resolve eq44996 eq123481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44996 eq123481
  have eq123928 : (M.op x y) = (k y x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq123755
       have r₂ := eq123488
       grind)
    | exact resolve eq123755 eq123488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123755
  have eq123964 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq328
       have i₂ := eq123495
       grind)
    | exact superpose eq123495 eq328
    | exact resolve eq328 eq123495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123986 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq123964
    | exact resolve eq123964 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123964
  have eq125070 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq129
       have i₂ := eq123928
       grind)
    | exact superpose eq123928 eq129
    | exact resolve eq129 eq123928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq123928
  have eq125101 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq125070
    | exact resolve eq125070 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125070
  have eq125113 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq125101
       have r₂ := eq27
       grind)
    | exact resolve eq125101 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125101
  have eq149828 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op (M.op x y) X0) x)) = (M.op (M.op (M.op (M.op x y) X0) x) (M.op (M.op (M.op x y) X0) x)) := by
    intro X0
    first
    | exact superpose eq698 eq56
    | exact resolve eq56 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq698
  have eq149890 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op (M.op x y) X0) x)) = (M.op (M.op x (M.op (M.op x y) x)) (M.op (M.op (M.op x y) X0) x)) := by
    intro X0
    first
    | (have i₁ := eq149828 x
       have i₂ := eq15845 x sF0 x
       grind)
    | exact superpose eq15845 eq149828
    | exact resolve eq149828 eq15845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15845 eq149828
  have eq540606 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq123986 eq12
    | (have j0 := eq12 X0 (σ x)
       grind)
    | (have r₁ := eq12 X0 (σ x)
       have r₂ := eq123986
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq123986
       grind)
    | exact resolve eq12 eq123986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123986
  have eq540635 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq540606 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540606
  have eq570831 : ∀ X0 : G, (τ X0) = (k (τ X0) (τ (σ x))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2⟩ := hcon
    have f570831_14 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
      intro X0 X1
      grind
    have f570831_15 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
      intro X0
      grind
    have f570831_24 : (τ X0) ≠ (k (τ X0) (τ (σ x))) := by grind
    have f570831_25 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by grind
    have f570831_26 : x ≠ (M.op x x) := by grind
    have f570831_27 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
      intro X0
      first
      | (have j0 := f570831_15 X0
         grind)
      | (have r₁ := f570831_15 X0
         have r₂ := f570831_25
         grind)
      | exact resolve f570831_15 f570831_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f570831_28 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
      intro X0
      first
      | (have j0 := f570831_27 X0
         grind)
      | (have r₁ := f570831_27 X0
         have r₂ := f570831_26
         grind)
      | exact resolve f570831_27 f570831_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f570831_32 : (τ X0) ≠ (τ (k X0 (σ x))) := by
      first
      | (have i₁ := f570831_24
         have i₂ := f570831_14 X0 (σ x)
         grind)
      | exact superpose f570831_14 f570831_24
      | exact resolve f570831_24 f570831_14
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f570831_33 : (τ X0) ≠ (τ X0) := by
      first
      | (have i₁ := f570831_32
         have i₂ := f570831_28 X0
         grind)
      | exact superpose f570831_28 f570831_32
      | exact resolve f570831_32 f570831_28
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f570831_34 : False := by grind
    exact f570831_34
  clear eq540635
  have eq570836 : ∀ X0 : G, (τ X0) = (k (τ X0) x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq38 eq570831
    | exact resolve eq570831 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570831
  have eq570838 : ∀ X0 : G, (τ X0) = (k (τ X0) x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq570836 X0
       have j1 := eq12 (τ X0) x
       grind)
    | (have r₁ := eq570836 X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq570836 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570836
  have eq570842 : ∀ X0 : G, (k X0 x) = X0 ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq570838 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq570838
    | exact resolve eq570838 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570838
  have eq571169 : x = (M.op x x) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq99 x
       have i₂ := eq570842 x
       grind)
    | exact superpose eq570842 eq99
    | (have j0 := eq99 x
       grind)
    | exact resolve eq99 eq570842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq570842
  have eq571204 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq571169
  have eq571671 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq125113 eq571204
    | exact resolve eq571204 eq125113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125113 eq571204
  have eq572150 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq571671
  have eq572157 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq572150
       have r₂ := eq27
       grind)
    | exact resolve eq572150 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572150
  have eq578108 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq572157 eq1008
    | (have r₁ := eq1008 (σ x) x
       have r₂ := eq572157
       grind)
    | (have r₁ := eq1008 x x
       have r₂ := eq572157
       grind)
    | exact resolve eq1008 eq572157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572157
  have eq578206 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq578108 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578108
  have eq586927 : ∀ X0 : G, (τ X0) = (k (τ X0) (τ (σ x))) ∨ x = (M.op x x) := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f586927_13 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
      intro X0 X1
      grind
    have f586927_14 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
      intro X0
      grind
    have f586927_23 : (τ X0) ≠ (k (τ X0) (τ (σ x))) := by grind
    have f586927_24 : x ≠ (M.op x x) := by grind
    have f586927_25 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
      intro X0
      first
      | (have j0 := f586927_14 X0
         grind)
      | (have r₁ := f586927_14 X0
         have r₂ := f586927_24
         grind)
      | exact resolve f586927_14 f586927_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f586927_29 : (τ X0) ≠ (τ (k X0 (σ x))) := by
      first
      | (have i₁ := f586927_23
         have i₂ := f586927_13 X0 (σ x)
         grind)
      | exact superpose f586927_13 f586927_23
      | exact resolve f586927_23 f586927_13
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f586927_30 : (τ X0) ≠ (τ X0) := by
      first
      | (have i₁ := f586927_29
         have i₂ := f586927_25 X0
         grind)
      | exact superpose f586927_25 f586927_29
      | exact resolve f586927_29 f586927_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f586927_31 : False := by grind
    exact f586927_31
  clear eq213 eq578206
  have eq586985 : ∀ X0 : G, (τ X0) = (k (τ X0) x) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq38 eq586927
    | exact resolve eq586927 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586927
  have eq587003 : ∀ X0 : G, (τ X0) = (k (τ X0) x) := by
    intro X0
    first
    | (have j0 := eq586985 X0
       have j1 := eq12 (τ X0) x
       grind)
    | (have r₁ := eq586985 X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq586985 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586985
  have eq587263 : x = (k x x) := by
    first
    | exact superpose eq38 eq587003
    | exact resolve eq587003 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq587003
  have eq588017 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq328
       have i₂ := eq587263
       grind)
    | exact superpose eq587263 eq328
    | exact resolve eq328 eq587263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328
  have eq588162 : x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq123495
       have i₂ := eq587263
       grind)
    | exact superpose eq587263 eq123495
    | exact resolve eq123495 eq587263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123495 eq587263
  have eq593054 : x = (M.op x x) := by
    first
    | (have r₁ := eq588162
       have r₂ := eq123488
       grind)
    | exact resolve eq588162 eq123488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123488 eq588162
  have eq593077 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq588017
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq588017
    | exact resolve eq588017 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq588017
  have eq593078 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq593077
  have eq596137 : ∀ X0 : G, (M.op X0 x) = (M.op x (M.op (M.op x y) (M.op X0 x))) := by
    intro X0
    first
    | (have i₁ := eq3068 X0
       have i₂ := eq593054
       grind)
    | exact superpose eq593054 eq3068
    | exact resolve eq3068 eq593054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3068
  have eq596138 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq3225
       have i₂ := eq593054
       grind)
    | exact superpose eq593054 eq3225
    | exact resolve eq3225 eq593054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3225
  have eq600928 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq593078 eq3316
    | exact resolve eq3316 eq593078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3316
  have eq602294 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq596138 eq14513
    | exact resolve eq14513 eq596138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14513
  have eq602571 : ∀ X0 : G, (M.op (M.op x x) (M.op (M.op (M.op x y) X0) x)) = (M.op (M.op x y) (M.op (M.op (M.op x y) X0) x)) := by
    intro X0
    first
    | exact superpose eq596138 eq149890
    | exact resolve eq149890 eq596138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149890
  have eq602636 : (M.op (σ x) x) = (M.op (M.op (M.op (σ x) x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) x))) (M.op (M.op x y) (M.op (σ x) x))) := by
    first
    | exact superpose eq596137 eq47616
    | exact resolve eq47616 eq596137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47616 eq596137
  have eq602667 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq600928 eq14971
    | exact resolve eq14971 eq600928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14971
  have eq602716 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op (σ x) (M.op X0 (σ y))) (σ y)) := by
    intro X0
    first
    | exact superpose eq600928 eq23886
    | exact resolve eq23886 eq600928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23886 eq600928
  have eq603380 : ∀ X0 : G, x = (M.op (M.op x y) (M.op (M.op (M.op x y) X0) x)) := by
    intro X0
    first
    | (have i₁ := eq602571 X0
       have i₂ := eq1846 x (M.op sF0 X0)
       grind)
    | exact superpose eq1846 eq602571
    | exact resolve eq602571 eq1846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602571
  have eq603422 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq602294
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq602294
    | exact resolve eq602294 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602294
  have eq603430 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq602716 eq59438
    | exact resolve eq59438 eq602716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59438 eq602716
  have eq603442 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq602667
    | exact resolve eq602667 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq602667
  have eq603481 : ∀ X0 : G, x = (M.op (M.op (M.op (M.op y X0) x) x) (M.op (M.op (M.op x y) (M.op x y)) x)) := by
    intro X0
    first
    | exact superpose eq603380 eq61242
    | exact resolve eq61242 eq603380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61242 eq603380
  have eq604731 : y = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1853
       have i₂ := eq603422
       grind)
    | exact superpose eq603422 eq1853
    | exact resolve eq1853 eq603422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1853
  have eq604762 : y = (M.op x y) ∨ (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq5517
       have i₂ := eq603422
       grind)
    | exact superpose eq603422 eq5517
    | exact resolve eq5517 eq603422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5517
  have eq604812 : y = (M.op x y) ∨ (σ (k y y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq18522
       have i₂ := eq603422
       grind)
    | exact superpose eq603422 eq18522
    | exact resolve eq18522 eq603422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18522
  have eq607173 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (k y y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq603442 eq329
    | exact resolve eq329 eq603442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329
  have eq608442 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq603442 eq603430
    | exact resolve eq603430 eq603442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603430
  have eq608564 : (σ (M.op x y)) = (σ (k y y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq604812
       have i₂ := eq603422
       grind)
    | exact superpose eq603422 eq604812
    | exact resolve eq604812 eq603422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604812
  have eq608579 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq604762
       have i₂ := eq603422
       grind)
    | exact superpose eq603422 eq604762
    | exact resolve eq604762 eq603422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603422 eq604762
  have eq608629 : y = (M.op (M.op y x) (M.op x y)) := by
    first
    | exact superpose eq604731 eq7681
    | exact resolve eq7681 eq604731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7681
  have eq612417 : ∀ X0 : G, x = (M.op (M.op (M.op (M.op y X0) x) x) (M.op y x)) := by
    intro X0
    first
    | exact superpose eq604731 eq603481
    | exact resolve eq603481 eq604731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603481 eq604731
  have eq614023 : (M.op (σ x) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq603442 eq607173
    | exact resolve eq607173 eq603442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607173
  have eq614053 : (σ (M.op x y)) = (σ (k y y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq608564
    | exact resolve eq608564 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608564
  have eq614073 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq603442 eq608579
    | exact resolve eq608579 eq603442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608579
  have eq614099 : x = (M.op (M.op y x) (M.op y x)) := by
    first
    | (have i₁ := eq612417 x
       have i₂ := eq60138 x y x
       grind)
    | exact superpose eq60138 eq612417
    | exact resolve eq612417 eq60138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60138 eq612417
  have eq614380 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq20 eq614073
    | exact resolve eq614073 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614073
  have eq614381 : x = (M.op (M.op x y) (M.op y x)) := by
    first
    | (have i₁ := eq614099
       have i₂ := eq14938 y x
       grind)
    | exact superpose eq14938 eq614099
    | exact resolve eq614099 eq14938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14938 eq614099
  have eq614425 : y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq614380
       have r₂ := eq27
       grind)
    | exact resolve eq614380 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614380
  have eq614426 : x = (M.op (M.op x y) (M.op y x)) := by
    first
    | (have i₁ := eq614381
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq614381
    | exact resolve eq614381 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq614381
  have eq614435 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq603442 eq614425
    | exact resolve eq614425 eq603442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603442 eq614425
  have eq614445 : (M.op y x) = (M.op (M.op (M.op y x) y) x) := by
    first
    | exact superpose eq614426 eq16332
    | exact resolve eq16332 eq614426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16332 eq614426
  have eq614568 : (M.op x x) = (M.op y x) := by
    first
    | (have i₁ := eq614445
       have i₂ := eq14940 x y
       grind)
    | exact superpose eq14940 eq614445
    | exact resolve eq614445 eq14940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614445
  have eq614572 : x = (M.op y x) := by
    first
    | (have i₁ := eq614568
       have i₂ := eq593054
       grind)
    | exact superpose eq593054 eq614568
    | exact resolve eq614568 eq593054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614568
  have eq616936 : y = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq608629
       have i₂ := eq614572
       grind)
    | exact superpose eq614572 eq608629
    | exact resolve eq608629 eq614572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608629 eq614572
  have eq619268 : ∀ X0 : G, (M.op (M.op (σ x) X0) (M.op (σ x) X0)) = X0 := by
    intro X0
    first
    | exact superpose eq593078 eq12994
    | exact resolve eq12994 eq593078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12994
  have eq619274 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (σ x) (M.op (σ x) X0)) X0) := by
    intro X0
    first
    | exact superpose eq593078 eq13490
    | exact resolve eq13490 eq593078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593078
  have eq619303 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq619274 X0
       have i₂ := eq59424 X0 sF2
       grind)
    | exact superpose eq59424 eq619274
    | exact resolve eq619274 eq59424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619274
  have eq620243 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq619268 X0
       have i₂ := eq619303 (M.op sF2 X0)
       grind)
    | exact superpose eq619303 eq619268
    | exact resolve eq619268 eq619303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619268
  have eq622500 : (M.op x x) = (M.op (M.op (M.op x x) (M.op (M.op (σ x) (σ y)) (M.op x x))) (M.op (M.op x y) (M.op x x))) := by
    first
    | exact superpose eq619303 eq602636
    | exact resolve eq602636 eq619303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602636
  have eq623913 : x = (M.op (M.op x (M.op (M.op (σ x) (σ y)) x)) (M.op (M.op x y) x)) := by
    first
    | (have i₁ := eq622500
       have i₂ := eq593054
       grind)
    | exact superpose eq593054 eq622500
    | exact resolve eq622500 eq593054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622500
  have eq627114 : x = (M.op (M.op x (M.op (M.op (σ x) (σ y)) x)) x) := by
    first
    | exact superpose eq596138 eq623913
    | exact resolve eq623913 eq596138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596138 eq623913
  have eq628006 : x = (M.op (M.op (σ x) (σ y)) x) := by
    first
    | (have i₁ := eq627114
       have i₂ := eq381 x sF4
       grind)
    | exact superpose eq381 eq627114
    | exact resolve eq627114 eq381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381 eq627114
  have eq628440 : ∀ X0 : G, (M.op (M.op x X0) (M.op x X0)) = X0 := by
    intro X0
    first
    | exact superpose eq628006 eq390
    | exact resolve eq390 eq628006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390
  have eq628528 : ∀ X0 : G, (M.op x X0) = (M.op (M.op x (M.op x X0)) X0) := by
    intro X0
    first
    | exact superpose eq628006 eq13490
    | exact resolve eq13490 eq628006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13490 eq628006
  have eq628552 : ∀ X0 : G, (M.op X0 X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq628528 X0
       have i₂ := eq59424 X0 x
       grind)
    | exact superpose eq59424 eq628528
    | exact resolve eq628528 eq59424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59424 eq628528
  have eq628572 : ∀ X0 : G, (M.op (σ x) (M.op x X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq628440 X0
       have i₂ := eq619303 (M.op x X0)
       grind)
    | exact superpose eq619303 eq628440
    | exact resolve eq628440 eq619303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619303 eq628440
  have eq634624 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq614435 eq27
    | exact resolve eq27 eq614435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq636880 : ∀ X0 : G, (M.op X0 (M.op x x)) = (M.op (σ x) (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq628572 (M.op X0 (M.op x x))
       have i₂ := eq1005 x X0
       grind)
    | exact superpose eq1005 eq628572
    | exact resolve eq628572 eq1005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1005
  have eq636927 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq628572 eq93
    | exact resolve eq93 eq628572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq637428 : ∀ X0 : G, x = (M.op X0 (M.op x x)) := by
    intro X0
    first
    | exact superpose eq628572 eq636880
    | exact resolve eq636880 eq628572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636880
  have eq637632 : ∀ X0 : G, x = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq637428 X0
       have i₂ := eq593054
       grind)
    | exact superpose eq593054 eq637428
    | exact resolve eq637428 eq593054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593054 eq637428
  have eq644329 : ∀ X0 X2 : G, (M.op (M.op x X2) (M.op X0 X2)) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq56653 X0 x X2 x x
       have i₂ := eq637632 (M.op (M.op (M.op (M.op X0 x) X2) x) X2)
       grind)
    | exact superpose eq637632 eq56653
    | exact resolve eq56653 eq637632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56653 eq637632
  have eq645135 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq614435 eq636927
    | exact resolve eq636927 eq614435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636927
  have eq645382 : ∀ X0 : G, (M.op x X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq628572 eq620243
    | exact resolve eq620243 eq628572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620243
  have eq646607 : ∀ X0 : G, (M.op x (M.op x X0)) = X0 := by
    intro X0
    first
    | exact superpose eq645382 eq628572
    | exact resolve eq628572 eq645382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628572 eq645382
  have eq652284 : ∀ X0 : G, y = (M.op (M.op x y) (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq3839 (M.op x X0)
       have i₂ := eq646607 X0
       grind)
    | exact superpose eq646607 eq3839
    | exact resolve eq3839 eq646607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3839 eq646607
  have eq653532 : ∀ X0 : G, (M.op (M.op X0 y) (M.op X0 y)) = (M.op (M.op y (M.op x y)) (M.op X0 y)) := by
    intro X0
    first
    | exact superpose eq652284 eq14940
    | exact resolve eq14940 eq652284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq653551 : ∀ X0 : G, (M.op x (M.op X0 y)) = (M.op (M.op y (M.op x y)) (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq653532 X0
       have i₂ := eq628552 (M.op X0 y)
       grind)
    | exact superpose eq628552 eq653532
    | exact resolve eq653532 eq628552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653532
  have eq668569 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X0 (M.op x X0)) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14940 (M.op X1 X0) (M.op x X0)
       have i₂ := eq644329 X1 X0
       grind)
    | exact superpose eq644329 eq14940
    | exact resolve eq14940 eq644329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14940 eq644329
  have eq668590 : ∀ X0 X1 : G, (M.op x (M.op X1 X0)) = (M.op (M.op X0 (M.op x X0)) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq668569 X0 X1
       have i₂ := eq628552 (M.op X1 X0)
       grind)
    | exact superpose eq628552 eq668569
    | exact resolve eq668569 eq628552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668569
  have eq668639 : ∀ X0 X1 X2 X3 : G, (M.op x (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op x y)) X2) (M.op X0 (M.op x y))) X3) (M.op X0 (M.op x y)))) = (M.op (M.op (M.op x y) (M.op X0 (M.op x y))) (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op x y)) X2) (M.op X0 (M.op x y))) X3) (M.op X0 (M.op x y)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq93080 X0 X1 X2 X3
       have i₂ := eq668590 (M.op X0 sF0) (M.op (M.op (M.op (M.op (M.op X0 X1) sF0) X2) (M.op X0 sF0)) X3)
       grind)
    | exact superpose eq668590 eq93080
    | exact resolve eq93080 eq668590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93080 eq668590
  have eq676992 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq645135 eq136
    | exact resolve eq136 eq645135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136 eq645135
  have eq677195 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq608442 eq676992
    | exact resolve eq676992 eq608442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608442 eq676992
  have eq677255 : ∀ X0 : G, (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k X0 (σ y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq677195 eq12
    | (have j0 := eq12 X0 (σ y)
       grind)
    | exact resolve eq12 eq677195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq677195
  have eq677666 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq677255 X0
       grind)
    | (have r₁ := eq677255 X0
       have r₂ := eq614435
       grind)
    | exact resolve eq677255 eq614435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614435 eq677255
  have eq678146 : (σ y) = (σ (k y y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq677666 eq71
    | exact resolve eq71 eq677666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq677666
  have eq684375 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq614053
       have i₂ := eq678146
       grind)
    | exact superpose eq678146 eq614053
    | exact resolve eq614053 eq678146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614053 eq678146
  have eq684477 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq684375
  have eq684501 : y = (M.op x y) := by
    first
    | (have r₁ := eq684477
       have r₂ := eq634624
       grind)
    | exact resolve eq684477 eq634624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634624 eq684477
  have eq684514 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq684501 eq20
    | exact resolve eq20 eq684501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq685105 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) y) X2) (M.op X0 y)) X3) (M.op X0 y)) = (M.op (M.op y (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) y) X2) (M.op X0 y)) X3) (M.op X0 y))) (M.op X0 y)) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq684501 eq39240
    | exact resolve eq39240 eq684501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39240
  have eq686510 : y = (M.op x y) := by
    first
    | exact superpose eq684501 eq616936
    | exact resolve eq616936 eq684501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616936
  have eq687438 : ∀ X0 : G, y = (M.op y (M.op X0 y)) := by
    intro X0
    first
    | exact superpose eq684501 eq652284
    | exact resolve eq652284 eq684501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652284
  have eq687498 : ∀ X0 : G, (M.op (M.op y y) (M.op X0 y)) = (M.op x (M.op X0 y)) := by
    intro X0
    first
    | exact superpose eq684501 eq653551
    | exact resolve eq653551 eq684501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653551
  have eq687895 : ∀ X0 X1 X2 X3 : G, (M.op x (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) y) X2) (M.op X0 y)) X3) (M.op X0 y))) = (M.op (M.op y (M.op X0 y)) (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) y) X2) (M.op X0 y)) X3) (M.op X0 y))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq684501 eq668639
    | exact resolve eq668639 eq684501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668639 eq684501
  have eq688431 : ∀ X0 : G, y = (M.op x (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq687498 X0
       have i₂ := eq1846 y X0
       grind)
    | exact superpose eq1846 eq687498
    | exact resolve eq687498 eq1846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1846 eq687498
  have eq688438 : ∀ X0 X1 X2 X3 : G, (M.op y (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) y) X2) (M.op X0 y)) X3) (M.op X0 y))) = (M.op x (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) y) X2) (M.op X0 y)) X3) (M.op X0 y))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq687895 X0 X1 X2 X3
       have i₂ := eq687438 X0
       grind)
    | exact superpose eq687438 eq687895
    | exact resolve eq687895 eq687438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687438 eq687895
  have eq688718 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 y) (M.op X0 y)) = (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) y) X2) (M.op X0 y)) X3) (M.op X0 y)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq685105 X0 X1 X2 X3
       have i₂ := eq804 X0 y X1 X2 X3
       grind)
    | exact superpose eq804 eq685105
    | exact resolve eq685105 eq804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685105
  have eq688821 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq684514
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq684514
    | exact resolve eq684514 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684514
  have eq688841 : ∀ X0 X1 X2 X3 : G, (M.op X0 y) = (M.op x (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) y) X2) (M.op X0 y)) X3) (M.op X0 y))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq688438 X0 X1 X2 X3
       have i₂ := eq804 X0 y X1 X2 X3
       grind)
    | exact superpose eq804 eq688438
    | exact resolve eq688438 eq804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq804 eq688438
  have eq689050 : ∀ X0 X1 X2 X3 : G, (M.op x (M.op X0 y)) = (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) y) X2) (M.op X0 y)) X3) (M.op X0 y)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq688718 X0 X1 X2 X3
       have i₂ := eq628552 (M.op X0 y)
       grind)
    | exact superpose eq628552 eq688718
    | exact resolve eq688718 eq628552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628552 eq688718
  have eq689079 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq688821 eq24
    | exact resolve eq24 eq688821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq690147 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y y)) := by
    first
    | exact superpose eq688821 eq614023
    | exact resolve eq614023 eq688821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614023 eq688821
  have eq692323 : ∀ X0 X1 X2 X3 : G, y = (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) y) X2) (M.op X0 y)) X3) (M.op X0 y)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq689050 X0 X1 X2 X3
       have i₂ := eq688431 X0
       grind)
    | exact superpose eq688431 eq689050
    | exact resolve eq689050 eq688431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688431 eq689050
  have eq693595 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
    first
    | (have r₁ := eq690147
       have r₂ := eq27
       grind)
    | exact resolve eq690147 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690147
  have eq693757 : ∀ X0 : G, (M.op x y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq688841 X0 x x x
       have i₂ := eq692323 X0 x x x
       grind)
    | exact superpose eq692323 eq688841
    | exact resolve eq688841 eq692323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688841 eq692323
  have eq694686 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq693757 X0
       have i₂ := eq686510
       grind)
    | exact superpose eq686510 eq693757
    | exact resolve eq693757 eq686510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686510 eq693757
  have eq696026 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq1008 y x
       have i₂ := eq694686 y
       grind)
    | exact superpose eq694686 eq1008
    | (have r₁ := eq1008 y x
       have r₂ := eq694686 y
       grind)
    | exact resolve eq1008 eq694686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1008 eq694686
  have eq696284 : ∀ X0 : G, (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq696026 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696026
  have eq697439 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq693595
       have i₂ := eq696284 y
       grind)
    | exact superpose eq696284 eq693595
    | exact resolve eq693595 eq696284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693595 eq696284
  have eq697588 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq697439
       have i₂ := eq689079
       grind)
    | exact superpose eq689079 eq697439
    | exact resolve eq697439 eq689079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689079 eq697439
  have eq697998 : False := by grind
  exact eq697998

/-- `Equation221`: `x = (y ◇ (x ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_pyy_pyx_pyy_pyx_Equation221 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law221 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law221.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
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
  have eq82 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq125 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq82 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X0)
       have i₂ := eq82 X0 X1
       grind)
    | exact superpose eq82 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq82 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq82 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq82 X1 X1
       grind)
    | exact resolve eq13 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq82 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq129 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq125 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq130 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq129 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq132 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq130 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq130
    | (have j0 := eq130 X0 X1
       grind)
    | exact resolve eq130 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq136 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq132 X0 X1
       have j1 := eq128 X0 X1
       grind)
    | (have r₁ := eq132 X0 X1
       have r₂ := eq128 X0 X1
       grind)
    | (have r₁ := eq132 X0 (k X1 X0)
       have r₂ := eq128 X0 X1
       grind)
    | (have r₁ := eq132 X0 X0
       have r₂ := eq128 X0 X0
       grind)
    | exact resolve eq132 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq132
  have eq539 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq136 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq136
    | exact resolve eq136 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq553 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq136 x y
       grind)
    | exact superpose eq136 eq16
    | (have j1 := eq136 x y
       grind)
    | exact resolve eq16 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq567 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq539 X0 X1
       have i₂ := eq20 X0 X1
       grind)
    | exact superpose eq20 eq539
    | (have j0 := eq539 X0 X1
       grind)
    | exact resolve eq539 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq539
  have eq568 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq567 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq567
    | exact resolve eq567 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567
  have eq629 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq568 (τ X1) X0
       grind)
    | exact superpose eq568 eq19
    | (have j1 := eq568 (τ X1) X0
       grind)
    | exact resolve eq19 eq568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq568
  have eq786 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq629 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq629
    | exact resolve eq629 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629
  have eq833 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq786 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq786
    | (have j0 := eq786 X0 X1
       grind)
    | exact resolve eq786 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq786
  have eq913 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq553
       have i₂ := eq833 y x
       grind)
    | exact superpose eq833 eq553
    | (have j1 := eq833 (σ y) (σ x)
       grind)
    | (have r₁ := eq553
       have r₂ := eq833 y x
       grind)
    | exact resolve eq553 eq833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq914 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq913
  have eq959 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq914
  have eq965 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq553
       have i₂ := eq959
       grind)
    | exact superpose eq959 eq553
    | exact resolve eq553 eq959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553 eq959
  have eq966 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq965
  have eq967 : (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq966
  have eq984 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq967
  have eq991 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq984
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq984
    | exact resolve eq984 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq984
  have eq997 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq991
       grind)
    | exact superpose eq991 eq16
    | exact resolve eq16 eq991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq991
  have eq1049 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq997
       have i₂ := eq833 y x
       grind)
    | exact superpose eq833 eq997
    | (have j1 := eq833 y x
       grind)
    | (have r₁ := eq997
       have r₂ := eq833 y x
       grind)
    | exact resolve eq997 eq833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq833
  have eq1050 : y = (M.op x x) := by grind
  clear eq1049
  have eq1057 : (M.op x y) = (k y x) := by grind
  clear eq1050
  have eq1094 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq997
       have i₂ := eq1057
       grind)
    | exact superpose eq1057 eq997
    | exact resolve eq997 eq1057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq997 eq1057
  have eq1097 : False := by grind
  exact eq1097
