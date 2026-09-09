import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation883`: `x = y ◇ ((x ◇ y) ◇ (y ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxx_pyx_pyx_pxx_pyx_Equation883 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law883 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law883.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X1) (M.op X1 X1))) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) := by
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
  have eq33 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq33 (σ X0)
       grind)
    | exact superpose eq33 eq15
    | exact resolve eq15 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq33 (τ X0)
       grind)
    | exact superpose eq33 eq18
    | exact resolve eq18 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq37
    | exact resolve eq37 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq40 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq35
    | exact resolve eq35 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq42 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq38
    | exact resolve eq38 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq38
  have eq77 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq9 (σ X0) (σ X0)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq9
    | exact resolve eq9 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq9
    | exact resolve eq9 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq77 X0
       have i₂ := eq40 (M.op X0 X0)
       grind)
    | exact superpose eq40 eq77
    | exact resolve eq77 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq85 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq91 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq85 X0 X1
       have i₂ := eq40 X1
       grind)
    | exact superpose eq40 eq85
    | (have j0 := eq85 X0 X1
       grind)
    | exact resolve eq85 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq94 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq91 X0 X1
       have i₂ := eq40 X1
       grind)
    | exact superpose eq40 eq91
    | (have j0 := eq91 X0 X1
       grind)
    | exact resolve eq91 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq218 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq94 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq94
    | exact resolve eq94 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq265 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq218 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq218
    | (have j0 := eq218 X0 X1
       grind)
    | exact resolve eq218 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq272 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq265 X0 X1
       have j1 := eq79 X1 X0
       grind)
    | (have r₁ := eq265 (σ X0) X0
       have r₂ := eq79 X0 (σ X0)
       grind)
    | (have r₁ := eq265 X1 X0
       have r₂ := eq79 X0 X1
       grind)
    | exact resolve eq265 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq265
  have eq437 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq272 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq272
    | exact resolve eq272 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq444 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq272 (σ X0) X1
       grind)
    | exact superpose eq272 eq15
    | (have j1 := eq272 (σ X0) X1
       grind)
    | exact resolve eq15 eq272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq460 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq437 X0 X1
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq437
    | (have j0 := eq437 X0 X1
       grind)
    | exact resolve eq437 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq437
  have eq471 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq460 X1 (τ X0)
       grind)
    | exact superpose eq460 eq18
    | (have j1 := eq460 X1 (τ X0)
       grind)
    | exact resolve eq18 eq460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq460
  have eq1339 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq471 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq471
    | exact resolve eq471 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq471
  have eq1396 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1339 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1339
    | (have j0 := eq1339 X0 X1
       grind)
    | exact resolve eq1339 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1339
  have eq4625 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq444 x y
       grind)
    | exact superpose eq444 eq16
    | (have j1 := eq444 x y
       grind)
    | exact resolve eq16 eq444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444
  have eq4849 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq4625
       have i₂ := eq1396 x y
       grind)
    | exact superpose eq1396 eq4625
    | (have j1 := eq1396 x y
       grind)
    | (have r₁ := eq4625
       have r₂ := eq1396 x y
       grind)
    | exact resolve eq4625 eq1396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1396 eq4625
  have eq4850 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq4849
  have eq4858 : (σ x) = (M.op (σ y) (M.op (σ (M.op y y)) (σ (M.op y y)))) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq80 y (σ x)
       have i₂ := eq4850
       grind)
    | exact superpose eq4850 eq80
    | exact resolve eq80 eq4850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq4850
  have eq4871 : (σ x) = (M.op (σ y) (σ (M.op (M.op y y) (M.op y y)))) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq4858
       have i₂ := eq40 (M.op y y)
       grind)
    | exact superpose eq40 eq4858
    | exact resolve eq4858 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4858
  have eq4881 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4871
       have i₂ := eq82 y
       grind)
    | exact superpose eq82 eq4871
    | exact resolve eq4871 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq4871
  have eq4991 : ∀ X0 : G, (M.op y (M.op (M.op X0 y) (M.op x y))) = X0 ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq9 X0 y
       have i₂ := eq4881
       grind)
    | exact superpose eq4881 eq9
    | exact resolve eq9 eq4881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5011 : y = (M.op y (M.op (M.op x y) (M.op x y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9 y y
       have i₂ := eq4881
       grind)
    | exact superpose eq4881 eq9
    | exact resolve eq9 eq4881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4881
  have eq5142 : x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4991 x
       have i₂ := eq5011
       grind)
    | exact superpose eq5011 eq4991
    | exact resolve eq4991 eq5011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4991 eq5011
  have eq5149 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq5142
  have eq5306 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5149
       grind)
    | exact superpose eq5149 eq16
    | exact resolve eq16 eq5149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5149
  have eq5310 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq5306
       have r₂ := eq40 x
       grind)
    | exact resolve eq5306 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5306
  have eq5312 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5310
       grind)
    | exact superpose eq5310 eq16
    | exact resolve eq16 eq5310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5313 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq5310
       grind)
    | exact superpose eq5310 eq10
    | exact resolve eq10 eq5310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5310
  have eq5367 : x = y := by
    first
    | (have i₁ := eq5313
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5313
    | exact resolve eq5313 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5313
  have eq5368 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5312
       have i₂ := eq40 x
       grind)
    | exact superpose eq40 eq5312
    | exact resolve eq5312 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq5312
  have eq5370 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5368
       have i₂ := eq5367
       grind)
    | exact superpose eq5367 eq5368
    | exact resolve eq5368 eq5367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5367 eq5368
  have eq5371 : False := by grind
  exact eq5371

/-- `Equation907`: `x = y ◇ ((y ◇ x) ◇ (x ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxx_pyx_pyx_pxx_pyx_Equation907 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law907 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law907.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
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
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq41 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq56 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq58 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq59 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq58 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq70 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq56 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq56 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq56 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq56 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq178 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq70 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq185 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq178 X0 X1
       have j1 := eq59 X0 X1
       grind)
    | (have r₁ := eq178 X0 X1
       have r₂ := eq59 X0 X1
       grind)
    | (have r₁ := eq178 X1 X1
       have r₂ := eq59 X1 X1
       grind)
    | exact resolve eq178 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq178
  have eq471 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq185 (σ X1) (σ X0)
       grind)
    | exact superpose eq185 eq15
    | exact resolve eq15 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq478 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq471 X0 X1
       have i₂ := eq185 X1 X0
       grind)
    | exact superpose eq185 eq471
    | exact resolve eq471 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185 eq471
  have eq481 : False := by grind
  exact eq481

/-- `Equation947`: `x = y ◇ ((z ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if m(X,X) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxx_y_pxx_pyx_pxy_Equation947 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law947 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law947.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X0) (M.op X1 X0))) = X0 := by
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
  clear eq44
  have eq51 : ∀ X0 : G, y = (M.op X0 (M.op (M.op x y) (M.op X0 y))) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y X0 x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y)))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op X2 X0)) = (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X3 X0) (M.op X2 X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X3 X0) (M.op X2 X0)) X1 X2
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op X1 X0)) = (M.op X1 (M.op (M.op X2 (M.op (M.op X3 X0) (M.op X1 X0))) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X3 X0) (M.op X1 X0)) X1 X2
       have i₂ := eq14 X0 X1 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq69 (σ X0)
       grind)
    | exact superpose eq69 eq10
    | exact resolve eq10 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq69 sF2
       grind)
    | exact superpose eq69 eq50
    | exact resolve eq50 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq74 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq73
       have i₂ := eq69 x
       grind)
    | exact superpose eq69 eq73
    | exact resolve eq73 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq76 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq71 X0
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq71
    | exact resolve eq71 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
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
  have eq89 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq84
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq84
    | exact resolve eq84 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq91 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq21 eq89
    | exact resolve eq89 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq92 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
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
  have eq104 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq108 : (σ (k y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq104
       have i₂ := eq69 sF3
       grind)
    | exact superpose eq69 eq104
    | exact resolve eq104 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq110 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq108
       have i₂ := eq69 y
       grind)
    | exact superpose eq69 eq108
    | exact resolve eq108 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq108
  have eq234 : y = (M.op x (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq51 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq51
    | (have j0 := eq51 x
       grind)
    | exact resolve eq51 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq237 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X1 y)) = (M.op X0 (M.op y (M.op X0 (M.op (M.op x y) (M.op X1 y))))) := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq241 : (σ y) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq27 eq52
    | (have j0 := eq52 (σ x)
       grind)
    | exact resolve eq52 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq244 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X1 (σ y))) = (M.op X0 (M.op (σ y) (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op X1 (σ y)))))) := by
    intro X0 X1
    first
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq631 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X3 (M.op (M.op X2 X0) (M.op X1 X0)))) = (M.op X4 (M.op (M.op (M.op X2 X0) (M.op X1 X0)) (M.op X4 (M.op X0 (M.op X3 (M.op (M.op X2 X0) (M.op X1 X0))))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 (M.op (M.op X2 X0) (M.op X1 X0)) X1 X2 X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq652 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X2 X0)) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 X2 X2 X1
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq775 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 (M.op (M.op X4 (M.op (M.op X0 X1) (M.op X2 X1))) X1)) (M.op (M.op X0 X1) (M.op X2 X1))) = (M.op X5 (M.op (M.op (M.op X4 (M.op (M.op X0 X1) (M.op X2 X1))) X1) (M.op X5 (M.op (M.op X3 (M.op (M.op X4 (M.op (M.op X0 X1) (M.op X2 X1))) X1)) (M.op (M.op X0 X1) (M.op X2 X1)))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq53 (M.op (M.op X2 (M.op (M.op X3 X0) (M.op X1 X0))) X0) X1 X1 X3
       have i₂ := eq56 X0 X1 X2 X3
       grind)
    | exact superpose eq56 eq53
    | exact resolve eq53 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq1066 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 y)) = (M.op X0 (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq652 y x X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq652
    | (have j0 := eq652 y x X0
       grind)
    | exact resolve eq652 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1069 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) = (M.op X0 (M.op (σ y) (σ y))) := by
    intro X0
    first
    | exact superpose eq27 eq652
    | (have j0 := eq652 (σ y) (σ x) X0
       grind)
    | exact resolve eq652 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1090 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 x
       have i₂ := eq652 X1 x X0
       grind)
    | exact superpose eq652 eq14
    | exact resolve eq14 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1156 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (M.op X1 (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1090 X1 (σ X0)
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq1090
    | exact resolve eq1090 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq1160 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1090 (M.op X1 X0) X0
       have i₂ := eq652 X0 X1 X0
       grind)
    | exact superpose eq652 eq1090
    | exact resolve eq1090 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1165 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X1 X1 X0 X0
       have i₂ := eq1090 X1 (M.op X0 X1)
       grind)
    | exact superpose eq1090 eq53
    | exact resolve eq53 eq1090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1178 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) (M.op X1 (M.op X0 X0)) X1
       have i₂ := eq1090 (M.op X1 (M.op X0 X0)) X0
       grind)
    | exact superpose eq1090 eq14
    | exact resolve eq14 eq1090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1183 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1165 X0 X1
       have i₂ := eq652 X1 X0 X0
       grind)
    | exact superpose eq652 eq1165
    | exact resolve eq1165 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1165
  have eq1214 : (M.op (M.op x y) (M.op x y)) = (M.op x (M.op y y)) := by
    first
    | (have i₁ := eq1066 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1066
    | (have j0 := eq1066 x
       grind)
    | exact resolve eq1066 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1320 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq27 eq1069
    | (have j0 := eq1069 (σ x)
       grind)
    | exact resolve eq1069 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1744 : (M.op (M.op x y) (M.op x y)) = (M.op y (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))))) := by
    first
    | exact superpose eq234 eq1160
    | exact resolve eq1160 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1746 : (M.op y y) = (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op y y) (M.op (M.op y y) (M.op y y)))) := by
    first
    | (have i₁ := eq1160 (M.op y y) x
       have i₂ := eq1214
       grind)
    | exact superpose eq1214 eq1160
    | exact resolve eq1160 eq1214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1214
  have eq1750 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) := by
    first
    | exact superpose eq241 eq1160
    | exact resolve eq1160 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1752 : (M.op (σ y) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ y) (σ y)) (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))))) := by
    first
    | exact superpose eq1320 eq1160
    | exact resolve eq1160 eq1320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1320
  have eq1781 : (M.op (σ y) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | (have i₁ := eq1752
       have i₂ := eq1090 (M.op sF3 sF3) sF3
       grind)
    | exact superpose eq1090 eq1752
    | exact resolve eq1752 eq1090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1752
  have eq1783 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1750
       have i₂ := eq1090 (M.op sF4 sF4) sF4
       grind)
    | exact superpose eq1090 eq1750
    | exact resolve eq1750 eq1090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1750
  have eq1786 : (M.op y y) = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq1746
       have i₂ := eq1090 (M.op y y) y
       grind)
    | exact superpose eq1090 eq1746
    | exact resolve eq1746 eq1090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1746
  have eq1788 : (M.op y (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1744
       have i₂ := eq1090 (M.op sF0 sF0) sF0
       grind)
    | exact superpose eq1090 eq1744
    | exact resolve eq1744 eq1090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1744
  have eq1887 : (σ y) = (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1783 eq241
    | exact resolve eq241 eq1783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1916 : y = (M.op x (M.op y (M.op x y))) := by
    first
    | exact superpose eq1788 eq234
    | exact resolve eq234 eq1788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2065 : (M.op (σ y) (σ y)) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq1783 eq1781
    | exact resolve eq1781 eq1783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1781
  have eq2130 : (M.op y y) = (M.op (M.op y (M.op x y)) y) := by
    first
    | exact superpose eq1788 eq1786
    | exact resolve eq1786 eq1788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1786
  have eq2647 : ∀ X0 : G, (M.op X0 (M.op y (M.op x y))) = (M.op (M.op x y) (M.op X0 (M.op x y))) := by
    intro X0
    first
    | exact superpose eq1788 eq1183
    | exact resolve eq1183 eq1788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2648 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq1783 eq1183
    | exact resolve eq1183 eq1783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2649 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 y)) = (M.op y (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq1183 X0 y
       have i₂ := eq1066 X0
       grind)
    | exact superpose eq1066 eq1183
    | exact resolve eq1183 eq1066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1066
  have eq2650 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) = (M.op (σ y) (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq1069 eq1183
    | exact resolve eq1183 eq1069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1069
  have eq2671 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X1 X0) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1183 (M.op X1 X0) (M.op X0 (M.op X0 X0))
       have i₂ := eq1160 X0 X1
       grind)
    | exact superpose eq1160 eq1183
    | exact resolve eq1183 eq1160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2674 : (M.op x (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y)))) = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | exact superpose eq234 eq1183
    | exact resolve eq1183 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2682 : (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq241 eq1183
    | exact resolve eq1183 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2772 : (M.op (σ x) (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ y) (M.op (σ x) (σ y))))) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq1783 eq2682
    | exact resolve eq2682 eq1783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2682
  have eq2780 : (M.op x (M.op (M.op y (M.op x y)) (M.op y (M.op x y)))) = (M.op (M.op y (M.op x y)) y) := by
    first
    | exact superpose eq1788 eq2674
    | exact resolve eq2674 eq1788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2674
  have eq2783 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X1 X0) (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq2671 X0 X1
       have i₂ := eq652 (M.op X0 X0) X0 X0
       grind)
    | exact superpose eq652 eq2671
    | exact resolve eq2671 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2671
  have eq2818 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq2065 eq2772
    | exact resolve eq2772 eq2065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2065 eq2772
  have eq2824 : (M.op y y) = (M.op x (M.op (M.op y (M.op x y)) (M.op y (M.op x y)))) := by
    first
    | exact superpose eq2130 eq2780
    | exact resolve eq2780 eq2130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2130 eq2780
  have eq2825 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2783 X0 X1
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq2783
    | exact resolve eq2783 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2783
  have eq2841 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq2818
       have i₂ := eq652 sF4 sF3 sF3
       grind)
    | exact superpose eq652 eq2818
    | exact resolve eq2818 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2818
  have eq2847 : (M.op y y) = (M.op x (M.op y (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq2824
       have i₂ := eq652 sF0 y y
       grind)
    | exact superpose eq652 eq2824
    | exact resolve eq2824 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2824
  have eq2848 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2825 X0 X1
       have i₂ := eq1178 X0 X0
       grind)
    | exact superpose eq1178 eq2825
    | exact resolve eq2825 eq1178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2825
  have eq2855 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq1783 eq2841
    | exact resolve eq2841 eq1783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1783 eq2841
  have eq2858 : (M.op y y) = (M.op x (M.op y (M.op y (M.op x y)))) := by
    first
    | exact superpose eq1788 eq2847
    | exact resolve eq2847 eq1788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1788 eq2847
  have eq4455 : ∀ X0 X1 : G, (M.op y (M.op X1 y)) = (M.op X0 (M.op y (M.op X0 (M.op y (M.op X1 y))))) := by
    intro X0 X1
    first
    | exact superpose eq2649 eq237
    | exact resolve eq237 eq2649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237 eq2649
  have eq4617 : ∀ X0 X1 : G, (M.op (σ y) (M.op X1 (σ y))) = (M.op X0 (M.op (σ y) (M.op X0 (M.op (σ y) (M.op X1 (σ y)))))) := by
    intro X0 X1
    first
    | exact superpose eq2650 eq244
    | exact resolve eq244 eq2650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244 eq2650
  have eq15517 : ∀ X0 X1 X3 X4 : G, (M.op X0 (M.op X3 (M.op X1 (M.op X0 X0)))) = (M.op X4 (M.op (M.op X1 (M.op X0 X0)) (M.op X4 (M.op X0 (M.op X3 (M.op X1 (M.op X0 X0))))))) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq631 X0 x X1 X3 X4
       have i₂ := eq652 X0 X1 x
       grind)
    | exact superpose eq652 eq631
    | exact resolve eq631 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631
  have eq15599 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X0 X1) (M.op X1 X1)))) = (M.op X2 (M.op (M.op (M.op X0 X1) (M.op X1 X1)) (M.op (M.op X0 X1) (M.op X1 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15517 X1 (M.op X0 X1) X2 X2
       have i₂ := eq53 X1 X2 X1 X0
       grind)
    | exact superpose eq53 eq15517
    | exact resolve eq15517 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq15605 : ∀ X0 : G, (M.op y (M.op X0 (M.op y (M.op y y)))) = (M.op X0 (M.op (M.op y (M.op y y)) (M.op y (M.op y y)))) := by
    intro X0
    first
    | (have i₁ := eq15517 y y X0 X0
       have i₂ := eq4455 X0 y
       grind)
    | exact superpose eq4455 eq15517
    | exact resolve eq15517 eq4455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15606 : ∀ X0 : G, (M.op (σ y) (M.op X0 (M.op (σ y) (M.op (σ y) (σ y))))) = (M.op X0 (M.op (M.op (σ y) (M.op (σ y) (σ y))) (M.op (σ y) (M.op (σ y) (σ y))))) := by
    intro X0
    first
    | exact superpose eq4617 eq15517
    | exact resolve eq15517 eq4617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15517
  have eq15642 : ∀ X0 : G, (M.op (σ y) (M.op X0 (M.op (σ y) (M.op (σ y) (σ y))))) = (M.op X0 (M.op (σ y) (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))))) := by
    intro X0
    first
    | (have i₁ := eq15606 X0
       have i₂ := eq652 (M.op sF3 sF3) sF3 sF3
       grind)
    | exact superpose eq652 eq15606
    | exact resolve eq15606 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15606
  have eq15643 : ∀ X0 : G, (M.op y (M.op X0 (M.op y (M.op y y)))) = (M.op X0 (M.op y (M.op (M.op y y) (M.op y y)))) := by
    intro X0
    first
    | (have i₁ := eq15605 X0
       have i₂ := eq652 (M.op y y) y y
       grind)
    | exact superpose eq652 eq15605
    | exact resolve eq15605 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15605
  have eq15649 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X0 X1) (M.op X1 X1)))) = (M.op X2 (M.op (M.op X0 X1) (M.op (M.op X1 X1) (M.op X1 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15599 X0 X1 X2
       have i₂ := eq652 (M.op X1 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq652 eq15599
    | exact resolve eq15599 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15599
  have eq15680 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (σ y) (M.op X0 (M.op (σ y) (M.op (σ y) (σ y))))) := by
    intro X0
    first
    | (have i₁ := eq15642 X0
       have i₂ := eq14 sF3 sF3 sF3
       grind)
    | exact superpose eq14 eq15642
    | exact resolve eq15642 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15642
  have eq15681 : ∀ X0 : G, (M.op X0 y) = (M.op y (M.op X0 (M.op y (M.op y y)))) := by
    intro X0
    first
    | (have i₁ := eq15643 X0
       have i₂ := eq14 y y y
       grind)
    | exact superpose eq14 eq15643
    | exact resolve eq15643 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15643
  have eq15687 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X0 X1) (M.op X1 X1)))) = (M.op X2 (M.op (M.op X0 X1) (M.op X1 (M.op X1 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15649 X0 X1 X2
       have i₂ := eq652 X1 X1 X1
       grind)
    | exact superpose eq652 eq15649
    | exact resolve eq15649 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15649
  have eq15711 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X1 (M.op X2 (M.op (M.op X0 X1) (M.op X1 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15687 X0 X1 X2
       have i₂ := eq1160 X1 X0
       grind)
    | exact superpose eq1160 eq15687
    | exact resolve eq15687 eq1160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15687
  have eq15731 : ∀ X1 X2 : G, (M.op X2 X1) = (M.op X1 (M.op X2 (M.op X1 (M.op X1 X1)))) := by
    intro X1 X2
    first
    | (have i₁ := eq15711 x X1 X2
       have i₂ := eq652 X1 x X1
       grind)
    | exact superpose eq652 eq15711
    | exact resolve eq15711 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15711
  have eq31300 : ∀ X1 X2 X3 X4 X5 : G, (M.op (M.op X3 (M.op (M.op X4 (M.op X2 (M.op X1 X1))) X1)) (M.op X2 (M.op X1 X1))) = (M.op X5 (M.op (M.op (M.op X4 (M.op X2 (M.op X1 X1))) X1) (M.op X5 (M.op (M.op X3 (M.op (M.op X4 (M.op X2 (M.op X1 X1))) X1)) (M.op X2 (M.op X1 X1)))))) := by
    intro X1 X2 X3 X4 X5
    first
    | (have i₁ := eq775 X1 x X2 X3 X4 X5
       have i₂ := eq652 x X1 X2
       grind)
    | exact superpose eq652 eq775
    | exact resolve eq775 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775
  have eq32324 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) (σ y))) = (M.op X0 (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq15680 eq4617
    | exact resolve eq4617 eq15680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4617 eq15680
  have eq32527 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (M.op X0 (σ y)))) := by
    intro X0
    first
    | exact superpose eq32324 eq1090
    | exact resolve eq1090 eq32324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32742 : (σ y) = (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq27 eq32527
    | (have j0 := eq32527 (σ x)
       grind)
    | exact resolve eq32527 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32527
  have eq32825 : (M.op (σ y) (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y))))) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq32742 eq1183
    | exact resolve eq1183 eq32742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32833 : (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ y)) = (M.op (σ y) (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq32825
       have i₂ := eq652 sF4 sF2 sF2
       grind)
    | exact superpose eq652 eq32825
    | exact resolve eq32825 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32825
  have eq32840 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq241 eq32833
    | exact resolve eq32833 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241 eq32833
  have eq33339 : ∀ X0 : G, (M.op y (M.op y y)) = (M.op X0 (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq4455 X0 y
       have i₂ := eq15681 X0
       grind)
    | exact superpose eq15681 eq4455
    | exact resolve eq4455 eq15681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4455 eq15681
  have eq33737 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op X2 (M.op (M.op X0 (M.op X0 X0)) X0)) (M.op X0 (M.op X0 X0)))) (M.op (M.op X0 (M.op X0 X0)) X0)) = (M.op X3 (M.op (M.op (M.op X2 (M.op (M.op X0 (M.op X0 X0)) X0)) (M.op X0 (M.op X0 X0))) (M.op X3 (M.op (M.op X1 (M.op (M.op X2 (M.op (M.op X0 (M.op X0 X0)) X0)) (M.op X0 (M.op X0 X0)))) (M.op (M.op X0 (M.op X0 X0)) X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq31300 (M.op X1 (M.op X1 X1)) X1 X3 x x
       have i₂ := eq15731 X1 (M.op X1 (M.op X1 X1))
       grind)
    | exact superpose eq15731 eq31300
    | exact resolve eq31300 eq15731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31300
  have eq33784 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op X2 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) (M.op X0 X0)) = (M.op X3 (M.op (M.op (M.op X2 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) (M.op X3 (M.op (M.op X1 (M.op (M.op X2 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) (M.op X0 X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq33737 X0 X1 X2 X3
       have i₂ := eq1178 X0 X0
       grind)
    | exact superpose eq1178 eq33737
    | exact resolve eq33737 eq1178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1178 eq33737
  have eq33854 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 (M.op (M.op X2 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) X0)) = (M.op X3 (M.op (M.op (M.op X2 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) (M.op X3 (M.op X0 (M.op (M.op X1 (M.op (M.op X2 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq33784 X1 X1 X2 X3
       have i₂ := eq1183 (M.op X1 (M.op (M.op X2 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))) X1
       grind)
    | exact superpose eq1183 eq33784
    | exact resolve eq33784 eq1183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33784
  have eq33893 : ∀ X0 X1 X3 : G, (M.op X0 (M.op (M.op X1 (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0)))) X0)) = (M.op X3 (M.op (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))) (M.op X3 (M.op X0 (M.op (M.op X1 (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0)))) X0))))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq33854 x X1 X1 X3
       have i₂ := eq652 (M.op x x) X1 x
       grind)
    | exact superpose eq652 eq33854
    | exact resolve eq33854 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33854
  have eq33904 : ∀ X0 X1 X3 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X3 (M.op X0 (M.op X3 (M.op X0 (M.op (M.op X1 X0) X0))))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq33893 X0 X1 X3
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq33893
    | exact resolve eq33893 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33893
  have eq33909 : ∀ X0 X3 : G, (M.op X0 (M.op X0 X0)) = (M.op X3 (M.op X0 (M.op X3 (M.op X0 (M.op X0 X0))))) := by
    intro X0 X3
    first
    | (have i₁ := eq33904 X0 x X3
       have i₂ := eq2848 X0 x
       grind)
    | exact superpose eq2848 eq33904
    | exact resolve eq33904 eq2848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2848 eq33904
  have eq33911 : ∀ X0 X3 : G, (M.op X0 (M.op X0 X0)) = (M.op X3 (M.op X3 X0)) := by
    intro X0 X3
    first
    | (have i₁ := eq33909 X0 X3
       have i₂ := eq15731 X0 X3
       grind)
    | exact superpose eq15731 eq33909
    | exact resolve eq33909 eq15731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15731 eq33909
  have eq33982 : ∀ X0 : G, y = (M.op y (M.op X0 (M.op X0 y))) := by
    intro X0
    first
    | (have i₁ := eq1090 y y
       have i₂ := eq33339 X0
       grind)
    | (have i₁ := eq1090 y y
       have i₂ := eq33339 y
       grind)
    | exact superpose eq33339 eq1090
    | exact resolve eq1090 eq33339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34276 : y = (M.op y (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq33982 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq33982
    | (have j0 := eq33982 x
       grind)
    | exact resolve eq33982 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33982
  have eq34362 : (M.op y (M.op (M.op x (M.op x y)) (M.op x (M.op x y)))) = (M.op (M.op x (M.op x y)) y) := by
    first
    | exact superpose eq34276 eq1183
    | exact resolve eq1183 eq34276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34370 : (M.op (M.op x (M.op x y)) y) = (M.op y (M.op x (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq34362
       have i₂ := eq652 sF0 x x
       grind)
    | exact superpose eq652 eq34362
    | exact resolve eq34362 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652 eq34362
  have eq34377 : (M.op y y) = (M.op (M.op x (M.op x y)) y) := by
    first
    | exact superpose eq234 eq34370
    | exact resolve eq34370 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234 eq34370
  have eq35217 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33911 X1 X2
       have i₂ := eq33911 X1 X0
       grind)
    | (have i₁ := eq33911 X0 x
       have i₂ := eq33911 X0 X0
       grind)
    | exact superpose eq33911 eq33911
    | exact resolve eq33911 eq33911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35303 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1160 X1 X2
       have i₂ := eq33911 X1 X0
       grind)
    | (have i₁ := eq1160 X0 X1
       have i₂ := eq33911 X0 X0
       grind)
    | exact superpose eq33911 eq1160
    | exact resolve eq1160 eq33911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35311 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1090 X1 X1
       have i₂ := eq33911 X1 X0
       grind)
    | (have i₁ := eq1090 X0 X0
       have i₂ := eq33911 X0 X0
       grind)
    | exact superpose eq33911 eq1090
    | exact resolve eq1090 eq33911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1090 eq33911
  have eq35867 : (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) (M.op y y)) := by
    first
    | exact superpose eq34276 eq35311
    | exact resolve eq35311 eq34276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34276
  have eq35897 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq32742 eq35311
    | exact resolve eq35311 eq32742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32742
  have eq36088 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ y))) := by
    first
    | (have i₁ := eq35897
       have i₂ := eq1183 (M.op sF2 sF4) sF3
       grind)
    | exact superpose eq1183 eq35897
    | exact resolve eq35897 eq1183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35897
  have eq36108 : (M.op x (M.op x y)) = (M.op y (M.op (M.op x (M.op x y)) y)) := by
    first
    | (have i₁ := eq35867
       have i₂ := eq1183 (M.op x sF0) y
       grind)
    | exact superpose eq1183 eq35867
    | exact resolve eq35867 eq1183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1183 eq35867
  have eq36264 : (M.op (σ y) (M.op (σ y) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq32840 eq36088
    | exact resolve eq36088 eq32840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32840 eq36088
  have eq36277 : (M.op x (M.op x y)) = (M.op y (M.op y y)) := by
    first
    | exact superpose eq34377 eq36108
    | exact resolve eq36108 eq34377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34377 eq36108
  have eq36526 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq32324 eq36264
    | exact resolve eq36264 eq32324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32324 eq36264
  have eq36613 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq36277
       have i₂ := eq33339 X0
       grind)
    | (have i₁ := eq36277
       have i₂ := eq33339 y
       grind)
    | exact superpose eq33339 eq36277
    | exact resolve eq36277 eq33339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33339 eq36277
  have eq41533 : ∀ X0 : G, (M.op y y) = (M.op x (M.op X0 (M.op X0 (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq2858
       have i₂ := eq35217 y sF0 x
       grind)
    | (have i₁ := eq2858
       have i₂ := eq35217 X0 sF0 y
       grind)
    | exact superpose eq35217 eq2858
    | exact resolve eq2858 eq35217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2858
  have eq41576 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (σ x) (M.op X0 (M.op X0 (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | (have i₁ := eq2855
       have i₂ := eq35217 sF3 sF4 x
       grind)
    | (have i₁ := eq2855
       have i₂ := eq35217 X0 sF4 sF3
       grind)
    | exact superpose eq35217 eq2855
    | exact resolve eq2855 eq35217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2855 eq35217
  have eq50347 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq92 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq50355 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq50347
    | exact resolve eq50347 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50347
  have eq50366 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq50355
       have r₂ := eq28
       grind)
    | exact resolve eq50355 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50355
  have eq50370 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq50366
    | exact resolve eq50366 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50366
  have eq50438 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq50370 eq1160
    | exact resolve eq1160 eq50370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50370
  have eq50452 : (σ x) = (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq2648 eq50438
    | exact resolve eq50438 eq2648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2648 eq50438
  have eq50466 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1887 eq50452
    | exact resolve eq50452 eq1887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1887 eq50452
  have eq50472 : (τ (σ y)) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq50466 eq74
    | exact resolve eq74 eq50466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50466
  have eq50587 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq30 eq50472
    | exact resolve eq50472 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50472
  have eq50588 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by grind
  clear eq50587
  have eq51046 : x = (M.op (M.op x y) (M.op x (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1160 x x
       have i₂ := eq50588
       grind)
    | exact superpose eq50588 eq1160
    | exact resolve eq1160 eq50588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1160 eq50588
  have eq51060 : x = (M.op x (M.op y (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq2647 eq51046
    | exact resolve eq51046 eq2647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2647 eq51046
  have eq51084 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1916 eq51060
    | exact resolve eq51060 eq1916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1916 eq51060
  have eq51119 : ∀ X0 : G, (σ x) = (M.op X0 (M.op X0 (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1156 x X0
       have i₂ := eq51084
       grind)
    | exact superpose eq51084 eq1156
    | exact resolve eq1156 eq51084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1156
  have eq51170 : x = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq35311 x x
       have i₂ := eq51084
       grind)
    | exact superpose eq51084 eq35311
    | exact resolve eq35311 eq51084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35311 eq51084
  have eq51176 : x = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq51170
       have i₂ := eq36613 x
       grind)
    | (have i₁ := eq51170
       have i₂ := eq36613 x
       grind)
    | exact superpose eq36613 eq51170
    | exact resolve eq51170 eq36613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36613 eq51170
  have eq51194 : ∀ X0 : G, (σ x) = (M.op X0 (M.op X0 (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq51119 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq51119
    | (have j0 := eq51119 X0
       grind)
    | exact resolve eq51119 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51119
  have eq51219 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq36526 eq51194
    | (have j0 := eq51194 (σ x)
       grind)
    | exact resolve eq51194 eq36526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36526 eq51194
  have eq51232 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq51219
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq51219
    | exact resolve eq51219 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51219
  have eq51623 : ∀ X0 : G, (M.op x y) = (M.op x (M.op X0 (M.op X0 (M.op x y)))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq51176 eq35303
    | exact resolve eq35303 eq51176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51176
  have eq51628 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq41533 eq51623
    | exact resolve eq51623 eq41533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41533 eq51623
  have eq52336 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X0 (M.op X0 (M.op (σ x) (σ y))))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq51232 eq35303
    | exact resolve eq35303 eq51232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35303 eq51232
  have eq52341 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq41576 eq52336
    | exact resolve eq52336 eq41576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41576 eq52336
  have eq52433 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq110
       have i₂ := eq51628
       grind)
    | exact superpose eq51628 eq110
    | exact resolve eq110 eq51628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq51628
  have eq52597 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21 eq52433
    | exact resolve eq52433 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52433
  have eq54549 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq52597 eq52341
    | exact resolve eq52341 eq52597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52341 eq52597
  have eq54633 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq54549
  have eq54651 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq54633
       have r₂ := eq28
       grind)
    | exact resolve eq54633 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54633
  have eq54678 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq54651 eq30
    | exact resolve eq30 eq54651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq54651
  have eq54896 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq54678
    | exact resolve eq54678 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq54678
  have eq54897 : x = y := by grind
  clear eq54896
  have eq54924 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq54897
       grind)
    | exact superpose eq54897 eq19
    | exact resolve eq19 eq54897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq54925 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq54897
       grind)
    | exact superpose eq54897 eq25
    | exact resolve eq25 eq54897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq54897
  have eq55139 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq54925
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq54925
    | exact resolve eq54925 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq54925
  have eq55169 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq55139 eq27
    | exact resolve eq27 eq55139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq55139
  have eq55571 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq55169 eq74
    | exact resolve eq74 eq55169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq55169
  have eq55673 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq55571
       have i₂ := eq54924
       grind)
    | exact superpose eq54924 eq55571
    | exact resolve eq55571 eq54924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54924 eq55571
  have eq55699 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq55673 eq15
    | exact resolve eq15 eq55673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55673
  have eq55795 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq55699
    | exact resolve eq55699 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq55699
  have eq55828 : False := by grind
  exact eq55828

/-- `Equation947`: `x = y ◇ ((z ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxx_y_pxx_x_pxy_Equation947 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law947 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law947.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X0) (M.op X1 X0))) = X0 := by
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
  clear eq44
  have eq51 : ∀ X0 : G, y = (M.op X0 (M.op (M.op x y) (M.op X0 y))) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y X0 x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y)))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op X2 X0)) = (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X3 X0) (M.op X2 X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X3 X0) (M.op X2 X0)) X1 X2
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op X1 X0)) = (M.op X1 (M.op (M.op X2 (M.op (M.op X3 X0) (M.op X1 X0))) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X3 X0) (M.op X1 X0)) X1 X2
       have i₂ := eq14 X0 X1 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq69 (σ X0)
       grind)
    | exact superpose eq69 eq10
    | exact resolve eq10 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq69 sF2
       grind)
    | exact superpose eq69 eq50
    | exact resolve eq50 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq74 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq73
       have i₂ := eq69 x
       grind)
    | exact superpose eq69 eq73
    | exact resolve eq73 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq76 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq71 X0
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq71
    | exact resolve eq71 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq93 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
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
  have eq98 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
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
  have eq100 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq21 eq98
    | exact resolve eq98 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq101 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
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
  have eq108 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq112 : (σ (k y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq108
       have i₂ := eq69 sF3
       grind)
    | exact superpose eq69 eq108
    | exact resolve eq108 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq114 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq112
       have i₂ := eq69 y
       grind)
    | exact superpose eq69 eq112
    | exact resolve eq112 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq147 : ∀ X0 : G, (σ (k X0 (M.op y y))) = (k (σ X0) (M.op (σ y) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq10 X0 (M.op y y)
       have i₂ := eq114
       grind)
    | exact superpose eq114 eq10
    | exact resolve eq10 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq238 : y = (M.op x (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq51 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq51
    | (have j0 := eq51 x
       grind)
    | exact resolve eq51 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq241 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X1 y)) = (M.op X0 (M.op y (M.op X0 (M.op (M.op x y) (M.op X1 y))))) := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq245 : (σ y) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq27 eq52
    | (have j0 := eq52 (σ x)
       grind)
    | exact resolve eq52 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq248 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X1 (σ y))) = (M.op X0 (M.op (σ y) (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op X1 (σ y)))))) := by
    intro X0 X1
    first
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq730 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X3 (M.op (M.op X2 X0) (M.op X1 X0)))) = (M.op X4 (M.op (M.op (M.op X2 X0) (M.op X1 X0)) (M.op X4 (M.op X0 (M.op X3 (M.op (M.op X2 X0) (M.op X1 X0))))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 (M.op (M.op X2 X0) (M.op X1 X0)) X1 X2 X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq752 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X2 X0)) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 X2 X2 X1
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq872 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 (M.op (M.op X4 (M.op (M.op X0 X1) (M.op X2 X1))) X1)) (M.op (M.op X0 X1) (M.op X2 X1))) = (M.op X5 (M.op (M.op (M.op X4 (M.op (M.op X0 X1) (M.op X2 X1))) X1) (M.op X5 (M.op (M.op X3 (M.op (M.op X4 (M.op (M.op X0 X1) (M.op X2 X1))) X1)) (M.op (M.op X0 X1) (M.op X2 X1)))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq53 (M.op (M.op X2 (M.op (M.op X3 X0) (M.op X1 X0))) X0) X1 X1 X3
       have i₂ := eq56 X0 X1 X2 X3
       grind)
    | exact superpose eq56 eq53
    | exact resolve eq53 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq1227 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 y)) = (M.op X0 (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq752 y x X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq752
    | (have j0 := eq752 y x X0
       grind)
    | exact resolve eq752 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1230 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) = (M.op X0 (M.op (σ y) (σ y))) := by
    intro X0
    first
    | exact superpose eq27 eq752
    | (have j0 := eq752 (σ y) (σ x) X0
       grind)
    | exact resolve eq752 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1253 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 x
       have i₂ := eq752 X1 x X0
       grind)
    | exact superpose eq752 eq14
    | exact resolve eq14 eq752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1324 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (M.op X1 (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1253 X1 (σ X0)
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq1253
    | exact resolve eq1253 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq1329 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1253 (M.op X1 X0) X0
       have i₂ := eq752 X0 X1 X0
       grind)
    | exact superpose eq752 eq1253
    | exact resolve eq1253 eq752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1335 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X1 X1 X0 X0
       have i₂ := eq1253 X1 (M.op X0 X1)
       grind)
    | exact superpose eq1253 eq53
    | exact resolve eq53 eq1253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1350 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) (M.op X1 (M.op X0 X0)) X1
       have i₂ := eq1253 (M.op X1 (M.op X0 X0)) X0
       grind)
    | exact superpose eq1253 eq14
    | exact resolve eq14 eq1253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1355 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1335 X0 X1
       have i₂ := eq752 X1 X0 X0
       grind)
    | exact superpose eq752 eq1335
    | exact resolve eq1335 eq752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1335
  have eq1388 : (M.op (M.op x y) (M.op x y)) = (M.op x (M.op y y)) := by
    first
    | (have i₁ := eq1227 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1227
    | (have j0 := eq1227 x
       grind)
    | exact resolve eq1227 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1516 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq27 eq1230
    | (have j0 := eq1230 (σ x)
       grind)
    | exact resolve eq1230 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1964 : (M.op (M.op x y) (M.op x y)) = (M.op y (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))))) := by
    first
    | exact superpose eq238 eq1329
    | exact resolve eq1329 eq238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1966 : (M.op y y) = (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op y y) (M.op (M.op y y) (M.op y y)))) := by
    first
    | (have i₁ := eq1329 (M.op y y) x
       have i₂ := eq1388
       grind)
    | exact superpose eq1388 eq1329
    | exact resolve eq1329 eq1388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1388
  have eq1970 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) := by
    first
    | exact superpose eq245 eq1329
    | exact resolve eq1329 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1972 : (M.op (σ y) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ y) (σ y)) (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))))) := by
    first
    | exact superpose eq1516 eq1329
    | exact resolve eq1329 eq1516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1516
  have eq2002 : (M.op (σ y) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | (have i₁ := eq1972
       have i₂ := eq1253 (M.op sF3 sF3) sF3
       grind)
    | exact superpose eq1253 eq1972
    | exact resolve eq1972 eq1253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1972
  have eq2004 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1970
       have i₂ := eq1253 (M.op sF4 sF4) sF4
       grind)
    | exact superpose eq1253 eq1970
    | exact resolve eq1970 eq1253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1970
  have eq2007 : (M.op y y) = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq1966
       have i₂ := eq1253 (M.op y y) y
       grind)
    | exact superpose eq1253 eq1966
    | exact resolve eq1966 eq1253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1966
  have eq2009 : (M.op y (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1964
       have i₂ := eq1253 (M.op sF0 sF0) sF0
       grind)
    | exact superpose eq1253 eq1964
    | exact resolve eq1964 eq1253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1964
  have eq2106 : (σ y) = (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq2004 eq245
    | exact resolve eq245 eq2004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2139 : y = (M.op x (M.op y (M.op x y))) := by
    first
    | exact superpose eq2009 eq238
    | exact resolve eq238 eq2009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2358 : (M.op (σ y) (σ y)) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq2004 eq2002
    | exact resolve eq2002 eq2004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2002
  have eq2359 : (M.op y y) = (M.op (M.op y (M.op x y)) y) := by
    first
    | exact superpose eq2009 eq2007
    | exact resolve eq2007 eq2009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2007
  have eq2943 : ∀ X0 : G, (M.op X0 (M.op y (M.op x y))) = (M.op (M.op x y) (M.op X0 (M.op x y))) := by
    intro X0
    first
    | exact superpose eq2009 eq1355
    | exact resolve eq1355 eq2009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2944 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq2004 eq1355
    | exact resolve eq1355 eq2004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2945 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 y)) = (M.op y (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq1355 X0 y
       have i₂ := eq1227 X0
       grind)
    | exact superpose eq1227 eq1355
    | exact resolve eq1355 eq1227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1227
  have eq2946 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) = (M.op (σ y) (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq1230 eq1355
    | exact resolve eq1355 eq1230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1230
  have eq2969 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X1 X0) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1355 (M.op X1 X0) (M.op X0 (M.op X0 X0))
       have i₂ := eq1329 X0 X1
       grind)
    | exact superpose eq1329 eq1355
    | exact resolve eq1355 eq1329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2972 : (M.op x (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y)))) = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | exact superpose eq238 eq1355
    | exact resolve eq1355 eq238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238
  have eq2980 : (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq245 eq1355
    | exact resolve eq1355 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245
  have eq3080 : (M.op (σ x) (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ y) (M.op (σ x) (σ y))))) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq2004 eq2980
    | exact resolve eq2980 eq2004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2980
  have eq3088 : (M.op x (M.op (M.op y (M.op x y)) (M.op y (M.op x y)))) = (M.op (M.op y (M.op x y)) y) := by
    first
    | exact superpose eq2009 eq2972
    | exact resolve eq2972 eq2009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2972
  have eq3091 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X1 X0) (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq2969 X0 X1
       have i₂ := eq752 (M.op X0 X0) X0 X0
       grind)
    | exact superpose eq752 eq2969
    | exact resolve eq2969 eq752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2969
  have eq3129 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq2358 eq3080
    | exact resolve eq3080 eq2358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2358 eq3080
  have eq3135 : (M.op y y) = (M.op x (M.op (M.op y (M.op x y)) (M.op y (M.op x y)))) := by
    first
    | exact superpose eq2359 eq3088
    | exact resolve eq3088 eq2359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2359 eq3088
  have eq3136 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3091 X0 X1
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq3091
    | exact resolve eq3091 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3091
  have eq3152 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq3129
       have i₂ := eq752 sF4 sF3 sF3
       grind)
    | exact superpose eq752 eq3129
    | exact resolve eq3129 eq752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3129
  have eq3158 : (M.op y y) = (M.op x (M.op y (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq3135
       have i₂ := eq752 sF0 y y
       grind)
    | exact superpose eq752 eq3135
    | exact resolve eq3135 eq752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3135
  have eq3159 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3136 X0 X1
       have i₂ := eq1350 X0 X0
       grind)
    | exact superpose eq1350 eq3136
    | exact resolve eq3136 eq1350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3136
  have eq3165 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq2004 eq3152
    | exact resolve eq3152 eq2004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2004 eq3152
  have eq3168 : (M.op y y) = (M.op x (M.op y (M.op y (M.op x y)))) := by
    first
    | exact superpose eq2009 eq3158
    | exact resolve eq3158 eq2009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2009 eq3158
  have eq4742 : ∀ X0 X1 : G, (M.op y (M.op X1 y)) = (M.op X0 (M.op y (M.op X0 (M.op y (M.op X1 y))))) := by
    intro X0 X1
    first
    | exact superpose eq2945 eq241
    | exact resolve eq241 eq2945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241 eq2945
  have eq4929 : ∀ X0 X1 : G, (M.op (σ y) (M.op X1 (σ y))) = (M.op X0 (M.op (σ y) (M.op X0 (M.op (σ y) (M.op X1 (σ y)))))) := by
    intro X0 X1
    first
    | exact superpose eq2946 eq248
    | exact resolve eq248 eq2946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248 eq2946
  have eq16160 : ∀ X0 X1 X3 X4 : G, (M.op X0 (M.op X3 (M.op X1 (M.op X0 X0)))) = (M.op X4 (M.op (M.op X1 (M.op X0 X0)) (M.op X4 (M.op X0 (M.op X3 (M.op X1 (M.op X0 X0))))))) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq730 X0 x X1 X3 X4
       have i₂ := eq752 X0 X1 x
       grind)
    | exact superpose eq752 eq730
    | exact resolve eq730 eq752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730
  have eq16297 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X0 X1) (M.op X1 X1)))) = (M.op X2 (M.op (M.op (M.op X0 X1) (M.op X1 X1)) (M.op (M.op X0 X1) (M.op X1 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16160 X1 (M.op X0 X1) X2 X2
       have i₂ := eq53 X1 X2 X1 X0
       grind)
    | exact superpose eq53 eq16160
    | exact resolve eq16160 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq16305 : ∀ X0 : G, (M.op (σ y) (M.op X0 (M.op (σ y) (M.op (σ y) (σ y))))) = (M.op X0 (M.op (M.op (σ y) (M.op (σ y) (σ y))) (M.op (σ y) (M.op (σ y) (σ y))))) := by
    intro X0
    first
    | exact superpose eq4929 eq16160
    | exact resolve eq16160 eq4929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16160
  have eq16339 : ∀ X0 : G, (M.op (σ y) (M.op X0 (M.op (σ y) (M.op (σ y) (σ y))))) = (M.op X0 (M.op (σ y) (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))))) := by
    intro X0
    first
    | (have i₁ := eq16305 X0
       have i₂ := eq752 (M.op sF3 sF3) sF3 sF3
       grind)
    | exact superpose eq752 eq16305
    | exact resolve eq16305 eq752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16305
  have eq16347 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X0 X1) (M.op X1 X1)))) = (M.op X2 (M.op (M.op X0 X1) (M.op (M.op X1 X1) (M.op X1 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16297 X0 X1 X2
       have i₂ := eq752 (M.op X1 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq752 eq16297
    | exact resolve eq16297 eq752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16297
  have eq16377 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (σ y) (M.op X0 (M.op (σ y) (M.op (σ y) (σ y))))) := by
    intro X0
    first
    | (have i₁ := eq16339 X0
       have i₂ := eq14 sF3 sF3 sF3
       grind)
    | exact superpose eq14 eq16339
    | exact resolve eq16339 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16339
  have eq16385 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X0 X1) (M.op X1 X1)))) = (M.op X2 (M.op (M.op X0 X1) (M.op X1 (M.op X1 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16347 X0 X1 X2
       have i₂ := eq752 X1 X1 X1
       grind)
    | exact superpose eq752 eq16347
    | exact resolve eq16347 eq752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16347
  have eq16409 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X1 (M.op X2 (M.op (M.op X0 X1) (M.op X1 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16385 X0 X1 X2
       have i₂ := eq1329 X1 X0
       grind)
    | exact superpose eq1329 eq16385
    | exact resolve eq16385 eq1329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16385
  have eq16429 : ∀ X1 X2 : G, (M.op X2 X1) = (M.op X1 (M.op X2 (M.op X1 (M.op X1 X1)))) := by
    intro X1 X2
    first
    | (have i₁ := eq16409 x X1 X2
       have i₂ := eq752 X1 x X1
       grind)
    | exact superpose eq752 eq16409
    | exact resolve eq16409 eq752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16409
  have eq19088 : (σ (k (M.op y y) (M.op y y))) = (k (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq147 (M.op y y)
       have i₂ := eq114
       grind)
    | exact superpose eq114 eq147
    | exact resolve eq147 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq19198 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (σ (k (M.op y y) (M.op y y))) := by
    first
    | (have i₁ := eq19088
       have i₂ := eq69 (M.op sF3 sF3)
       grind)
    | exact superpose eq69 eq19088
    | exact resolve eq19088 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19088
  have eq19212 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq19198
       have i₂ := eq69 (M.op y y)
       grind)
    | exact superpose eq69 eq19198
    | exact resolve eq19198 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq19198
  have eq19217 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (σ y) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq19212
       have i₂ := eq752 sF3 sF3 sF3
       grind)
    | exact superpose eq752 eq19212
    | exact resolve eq19212 eq752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19212
  have eq19220 : (M.op (σ y) (M.op (σ y) (σ y))) = (σ (M.op y (M.op y y))) := by
    first
    | (have i₁ := eq19217
       have i₂ := eq752 y y y
       grind)
    | exact superpose eq752 eq19217
    | exact resolve eq19217 eq752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19217
  have eq19227 : (M.op y (M.op y y)) = (τ (M.op (σ y) (M.op (σ y) (σ y)))) := by
    first
    | (have i₁ := eq16 (M.op y (M.op y y))
       have i₂ := eq19220
       grind)
    | exact superpose eq19220 eq16
    | exact resolve eq16 eq19220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19220
  have eq30183 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) (σ y))) = (M.op X0 (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq16377 eq4929
    | exact resolve eq4929 eq16377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4929 eq16377
  have eq30305 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (σ y))) = (M.op X1 (M.op X1 (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq30183 eq30183
    | exact resolve eq30183 eq30183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30183
  have eq31630 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq27 eq30305
    | (have j0 := eq30305 (σ x) X0
       grind)
    | exact resolve eq30305 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30305
  have eq31954 : (M.op y (M.op y y)) = (τ (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq31630 eq19227
    | exact resolve eq19227 eq31630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19227
  have eq34644 : ∀ X1 X2 X3 X4 X5 : G, (M.op (M.op X3 (M.op (M.op X4 (M.op X2 (M.op X1 X1))) X1)) (M.op X2 (M.op X1 X1))) = (M.op X5 (M.op (M.op (M.op X4 (M.op X2 (M.op X1 X1))) X1) (M.op X5 (M.op (M.op X3 (M.op (M.op X4 (M.op X2 (M.op X1 X1))) X1)) (M.op X2 (M.op X1 X1)))))) := by
    intro X1 X2 X3 X4 X5
    first
    | (have i₁ := eq872 X1 x X2 X3 X4 X5
       have i₂ := eq752 x X1 X2
       grind)
    | exact superpose eq752 eq872
    | exact resolve eq872 eq752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq872
  have eq35944 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op X2 (M.op (M.op X0 (M.op X0 X0)) X0)) (M.op X0 (M.op X0 X0)))) (M.op (M.op X0 (M.op X0 X0)) X0)) = (M.op X3 (M.op (M.op (M.op X2 (M.op (M.op X0 (M.op X0 X0)) X0)) (M.op X0 (M.op X0 X0))) (M.op X3 (M.op (M.op X1 (M.op (M.op X2 (M.op (M.op X0 (M.op X0 X0)) X0)) (M.op X0 (M.op X0 X0)))) (M.op (M.op X0 (M.op X0 X0)) X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq34644 (M.op X1 (M.op X1 X1)) X1 X3 x x
       have i₂ := eq16429 X1 (M.op X1 (M.op X1 X1))
       grind)
    | exact superpose eq16429 eq34644
    | exact resolve eq34644 eq16429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34644
  have eq35987 : ∀ X0 : G, (M.op y (M.op y y)) = (M.op X0 (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq4742 X0 y
       have i₂ := eq16429 y X0
       grind)
    | exact superpose eq16429 eq4742
    | exact resolve eq4742 eq16429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4742
  have eq35993 : ∀ X0 : G, (τ (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op X0 (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq35987 X0
       have i₂ := eq31954
       grind)
    | exact superpose eq31954 eq35987
    | exact resolve eq35987 eq31954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31954 eq35987
  have eq36025 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op X2 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) (M.op X0 X0)) = (M.op X3 (M.op (M.op (M.op X2 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) (M.op X3 (M.op (M.op X1 (M.op (M.op X2 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) (M.op X0 X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq35944 X0 X1 X2 X3
       have i₂ := eq1350 X0 X0
       grind)
    | exact superpose eq1350 eq35944
    | exact resolve eq35944 eq1350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1350 eq35944
  have eq36100 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 (M.op (M.op X2 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) X0)) = (M.op X3 (M.op (M.op (M.op X2 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) (M.op X3 (M.op X0 (M.op (M.op X1 (M.op (M.op X2 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq36025 X1 X1 X2 X3
       have i₂ := eq1355 (M.op X1 (M.op (M.op X2 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))) X1
       grind)
    | exact superpose eq1355 eq36025
    | exact resolve eq36025 eq1355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1355 eq36025
  have eq36136 : ∀ X0 X1 X3 : G, (M.op X0 (M.op (M.op X1 (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0)))) X0)) = (M.op X3 (M.op (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))) (M.op X3 (M.op X0 (M.op (M.op X1 (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0)))) X0))))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq36100 x X1 X1 X3
       have i₂ := eq752 (M.op x x) X1 x
       grind)
    | exact superpose eq752 eq36100
    | exact resolve eq36100 eq752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq752 eq36100
  have eq36146 : ∀ X0 X1 X3 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X3 (M.op X0 (M.op X3 (M.op X0 (M.op (M.op X1 X0) X0))))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq36136 X0 X1 X3
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq36136
    | exact resolve eq36136 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36136
  have eq36151 : ∀ X0 X3 : G, (M.op X0 (M.op X0 X0)) = (M.op X3 (M.op X0 (M.op X3 (M.op X0 (M.op X0 X0))))) := by
    intro X0 X3
    first
    | (have i₁ := eq36146 X0 x X3
       have i₂ := eq3159 X0 x
       grind)
    | exact superpose eq3159 eq36146
    | exact resolve eq36146 eq3159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3159 eq36146
  have eq36153 : ∀ X0 X3 : G, (M.op X0 (M.op X0 X0)) = (M.op X3 (M.op X3 X0)) := by
    intro X0 X3
    first
    | (have i₁ := eq36151 X0 X3
       have i₂ := eq16429 X0 X3
       grind)
    | exact superpose eq16429 eq36151
    | exact resolve eq36151 eq16429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16429 eq36151
  have eq36164 : (M.op x (M.op x y)) = (τ (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq35993 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq35993
    | (have j0 := eq35993 x
       grind)
    | exact resolve eq35993 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37305 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq36153 X1 X2
       have i₂ := eq36153 X1 X0
       grind)
    | (have i₁ := eq36153 X0 x
       have i₂ := eq36153 X0 X0
       grind)
    | exact superpose eq36153 eq36153
    | exact resolve eq36153 eq36153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37406 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1329 X1 X2
       have i₂ := eq36153 X1 X0
       grind)
    | (have i₁ := eq1329 X0 X1
       have i₂ := eq36153 X0 X0
       grind)
    | exact superpose eq36153 eq1329
    | exact resolve eq1329 eq36153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37430 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1253 X1 X1
       have i₂ := eq36153 X1 X0
       grind)
    | (have i₁ := eq1253 X0 X0
       have i₂ := eq36153 X0 X0
       grind)
    | exact superpose eq36153 eq1253
    | exact resolve eq1253 eq36153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1253 eq36153
  have eq39762 : ∀ X0 : G, (M.op y y) = (M.op x (M.op X0 (M.op X0 (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq3168
       have i₂ := eq37305 y sF0 x
       grind)
    | (have i₁ := eq3168
       have i₂ := eq37305 X0 sF0 y
       grind)
    | exact superpose eq37305 eq3168
    | exact resolve eq3168 eq37305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3168
  have eq39801 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (σ x) (M.op X0 (M.op X0 (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | (have i₁ := eq3165
       have i₂ := eq37305 sF3 sF4 x
       grind)
    | (have i₁ := eq3165
       have i₂ := eq37305 X0 sF4 sF3
       grind)
    | exact superpose eq37305 eq3165
    | exact resolve eq3165 eq37305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3165 eq37305
  have eq52308 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq101 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq52316 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq52308
    | exact resolve eq52308 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52308
  have eq52327 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq52316
       have r₂ := eq28
       grind)
    | exact resolve eq52316 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52316
  have eq52331 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq52327
    | exact resolve eq52327 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52327
  have eq52404 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq52331 eq1329
    | exact resolve eq1329 eq52331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52331
  have eq52419 : (σ x) = (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq2944 eq52404
    | exact resolve eq52404 eq2944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2944 eq52404
  have eq52434 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq2106 eq52419
    | exact resolve eq52419 eq2106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2106 eq52419
  have eq52441 : (τ (σ y)) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq52434 eq74
    | exact resolve eq74 eq52434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52434
  have eq52564 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq30 eq52441
    | exact resolve eq52441 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52441
  have eq52565 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by grind
  clear eq52564
  have eq53018 : x = (M.op (M.op x y) (M.op x (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1329 x x
       have i₂ := eq52565
       grind)
    | exact superpose eq52565 eq1329
    | exact resolve eq1329 eq52565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1329 eq52565
  have eq53033 : x = (M.op x (M.op y (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq2943 eq53018
    | exact resolve eq53018 eq2943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2943 eq53018
  have eq53057 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2139 eq53033
    | exact resolve eq53033 eq2139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2139 eq53033
  have eq53097 : ∀ X0 : G, (σ x) = (M.op X0 (M.op X0 (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1324 x X0
       have i₂ := eq53057
       grind)
    | exact superpose eq53057 eq1324
    | exact resolve eq1324 eq53057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1324
  have eq53148 : x = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq37430 x x
       have i₂ := eq53057
       grind)
    | exact superpose eq53057 eq37430
    | exact resolve eq37430 eq53057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37430 eq53057
  have eq53156 : x = (τ (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq53148
       have i₂ := eq35993 x
       grind)
    | exact superpose eq35993 eq53148
    | exact resolve eq53148 eq35993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35993 eq53148
  have eq53175 : ∀ X0 : G, (σ x) = (M.op X0 (M.op X0 (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq53097 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq53097
    | (have j0 := eq53097 X0
       grind)
    | exact resolve eq53097 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53097
  have eq53196 : x = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq36164 eq53156
    | exact resolve eq53156 eq36164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36164 eq53156
  have eq53202 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq31630 eq53175
    | (have j0 := eq53175 (σ x)
       grind)
    | exact resolve eq53175 eq31630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31630 eq53175
  have eq53217 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq53202
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq53202
    | exact resolve eq53202 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53202
  have eq54286 : ∀ X0 : G, (M.op x y) = (M.op x (M.op X0 (M.op X0 (M.op x y)))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq53196 eq37406
    | exact resolve eq37406 eq53196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53196
  have eq54293 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq39762 eq54286
    | exact resolve eq54286 eq39762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39762 eq54286
  have eq54519 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X0 (M.op X0 (M.op (σ x) (σ y))))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq53217 eq37406
    | exact resolve eq37406 eq53217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37406 eq53217
  have eq54526 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq39801 eq54519
    | exact resolve eq54519 eq39801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39801 eq54519
  have eq55359 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq114
       have i₂ := eq54293
       grind)
    | exact superpose eq54293 eq114
    | exact resolve eq114 eq54293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq54293
  have eq55521 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21 eq55359
    | exact resolve eq55359 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55359
  have eq57020 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq55521 eq54526
    | exact resolve eq54526 eq55521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54526 eq55521
  have eq57112 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq57020
  have eq57131 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq57112
       have r₂ := eq28
       grind)
    | exact resolve eq57112 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57112
  have eq57157 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq57131 eq30
    | exact resolve eq30 eq57131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq57131
  have eq57370 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq57157
    | exact resolve eq57157 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq57157
  have eq57371 : x = y := by grind
  clear eq57370
  have eq57404 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq57371
       grind)
    | exact superpose eq57371 eq19
    | exact resolve eq19 eq57371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq57405 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq57371
       grind)
    | exact superpose eq57371 eq25
    | exact resolve eq25 eq57371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq57371
  have eq57621 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq57405
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq57405
    | exact resolve eq57405 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq57405
  have eq59095 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq57621 eq27
    | exact resolve eq27 eq57621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq57621
  have eq59514 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq59095 eq74
    | exact resolve eq74 eq59095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq59095
  have eq59624 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq59514
       have i₂ := eq57404
       grind)
    | exact superpose eq57404 eq59514
    | exact resolve eq59514 eq57404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57404 eq59514
  have eq59652 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq59624 eq15
    | exact resolve eq15 eq59624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59624
  have eq59746 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq59652
    | exact resolve eq59652 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq59652
  have eq59778 : False := by grind
  exact eq59778

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxx_y_pxx_x_pxy_Equation960 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (M.op X0 X1) := by
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
  clear eq18
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
       have i₂ := eq9 X0 X2 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
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
  have eq35 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq60 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq85 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq35 (τ X0)
       grind)
    | exact superpose eq35 eq19
    | exact resolve eq19 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq86 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq85 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq85
    | exact resolve eq85 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq94 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq86 X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq86
    | exact resolve eq86 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq86
  have eq98 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq94 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq94
    | exact resolve eq94 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 X0
       have i₂ := eq25 X0 X0
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 X3
       have i₂ := eq25 X1 X0
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X0 (M.op X1 X0))) (M.op (M.op X1 X0) (M.op X4 X4))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq24 (M.op X1 X0) X2 X3 X4
       have i₂ := eq25 X1 X0
       grind)
    | exact superpose eq25 eq24
    | exact resolve eq24 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X0 X1)) (M.op (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) (M.op X4 X4))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq24 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) X2 X3 X4
       have i₂ := eq24 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq24 eq24
    | exact resolve eq24 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq24 X4 X2 X3 (M.op X1 X0)
       have i₂ := eq25 X1 X0
       grind)
    | exact superpose eq25 eq24
    | exact resolve eq24 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X2) (M.op (M.op (M.op X3 X4) (M.op (M.op X0 X0) (M.op X0 X0))) (M.op (M.op X3 X4) (M.op (M.op X0 X0) (M.op X0 X0))))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq24 (M.op (M.op X3 X4) (M.op (M.op X0 X0) (M.op X0 X0))) X1 X2 (M.op X0 X0)
       have i₂ := eq24 (M.op X0 X0) X3 X4 X0
       grind)
    | exact superpose eq24 eq24
    | exact resolve eq24 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq25 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
       have i₂ := eq24 X0 x x X3
       grind)
    | exact superpose eq24 eq25
    | exact resolve eq25 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) X2) ∨ (M.op X0 X1) = (k (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op (M.op X1 X2) (M.op (M.op X1 X2) (M.op X1 X2))) X1
       have i₂ := eq24 (M.op X1 X2) X1 X2 (M.op X1 X2)
       grind)
    | exact superpose eq24 eq12
    | (have r₁ := eq12 (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op (M.op X1 X2) (M.op X0 X0))) (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op (M.op X1 X2) (M.op X0 X0)))))
       have r₂ := eq24 X0 X1 X2 (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op (M.op X1 X2) (M.op X0 X0)))
       grind)
    | exact resolve eq12 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) X2 X3
       have i₂ := eq24 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq137 X0 X1 X2 X3
       have i₂ := eq25 X0 X1
       grind)
    | exact superpose eq25 eq137
    | exact resolve eq137 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq139 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) X2) ∨ (M.op X0 X1) = (k (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq136 X0 X1 X2
       have i₂ := eq25 X0 X1
       grind)
    | exact superpose eq25 eq136
    | (have j0 := eq136 X0 X1 X2
       grind)
    | exact resolve eq136 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq145 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X2) (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X3 X4) (M.op (M.op X0 X0) (M.op X0 X0))))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq128 X0 X1 X2 X3 X4
       have i₂ := eq25 (M.op X3 X4) (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact superpose eq25 eq128
    | exact resolve eq128 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq147 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X0 X1)) (M.op (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) (M.op X4 X4))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq120 X0 X1 X2 X3 X4
       have i₂ := eq25 X0 X1
       grind)
    | exact superpose eq25 eq120
    | exact resolve eq120 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq148 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) X2) ∨ (M.op X0 X1) ≠ (M.op (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq139 X0 X1 X2
       have i₂ := eq25 X0 X1
       grind)
    | exact superpose eq25 eq139
    | (have j0 := eq139 X0 X1 X2
       grind)
    | exact resolve eq139 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq151 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X2) (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X3 X4) (M.op X0 (M.op X0 X0))))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq145 X1 X1 X2 X3 X4
       have i₂ := eq25 X1 X1
       grind)
    | exact superpose eq25 eq145
    | exact resolve eq145 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq179 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq60 x y
       grind)
    | exact superpose eq60 eq16
    | (have j1 := eq60 x y
       grind)
    | exact resolve eq16 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq60 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq198 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq25 (σ X0) (σ X0)
       have i₂ := eq98 X0
       grind)
    | exact superpose eq98 eq25
    | exact resolve eq25 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq200 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ (M.op X0 X0)) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq98 X0
       grind)
    | exact superpose eq98 eq9
    | exact resolve eq9 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq206 : ∀ X0 X1 X2 : G, (σ X0) = (M.op X1 (M.op (M.op X2 X1) (σ (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X1 X2
       have i₂ := eq98 X0
       grind)
    | exact superpose eq98 eq9
    | exact resolve eq9 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210 : ∀ X0 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq198 X0
       have i₂ := eq98 (M.op X0 X0)
       grind)
    | exact superpose eq98 eq198
    | exact resolve eq198 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq212 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq210 X0
       have i₂ := eq25 X0 X0
       grind)
    | exact superpose eq25 eq210
    | exact resolve eq210 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq400 : ∀ X0 X2 X3 : G, (M.op (M.op X0 (M.op X2 X2)) (M.op X2 (M.op X3 X3))) = X3 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq24 X2 (σ x) (M.op (σ (M.op x x)) (M.op X0 X0)) X3
       have i₂ := eq200 x X0
       grind)
    | exact superpose eq200 eq24
    | exact resolve eq24 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq451 : ∀ X0 : G, (σ X0) = (M.op (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq206 X0 (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) x
       have i₂ := eq132 (σ (M.op X0 X0)) x
       grind)
    | exact superpose eq132 eq206
    | exact resolve eq206 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq458 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq451 X0
       have i₂ := eq25 (σ (M.op X0 X0)) (σ (M.op X0 X0))
       grind)
    | exact superpose eq25 eq451
    | exact resolve eq451 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451
  have eq462 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq458 X0
       have i₂ := eq98 (M.op X0 X0)
       grind)
    | exact superpose eq98 eq458
    | exact resolve eq458 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458
  have eq464 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq462 X0
       have i₂ := eq25 X0 X0
       grind)
    | exact superpose eq25 eq462
    | exact resolve eq462 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462
  have eq681 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq400 X0 X0 X0
       grind)
    | exact superpose eq400 eq9
    | exact resolve eq9 eq400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq688 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq132 (M.op x (M.op x x)) x
       have i₂ := eq400 x x x
       grind)
    | exact superpose eq400 eq132
    | exact resolve eq132 eq400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400
  have eq819 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq688 X2 X3
       have i₂ := eq681 X2 X0 X1
       grind)
    | exact superpose eq681 eq688
    | exact resolve eq688 eq681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq821 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq108 X2
       have i₂ := eq681 X2 X0 X1
       grind)
    | exact superpose eq681 eq108
    | exact resolve eq108 eq681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq872 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq821 (M.op X0 (M.op X0 X0)) X0 X1
       have i₂ := eq108 X0
       grind)
    | exact superpose eq108 eq821
    | exact resolve eq821 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq878 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 (M.op X0 X0)) (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq821 (M.op X2 (M.op X0 X0)) (M.op (M.op x x) (M.op X2 X2)) X1
       have i₂ := eq24 X2 x x X0
       grind)
    | exact superpose eq24 eq821
    | exact resolve eq821 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1083 : (σ y) = (σ (M.op x x)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq179
       have i₂ := eq98 x
       grind)
    | exact superpose eq98 eq179
    | exact resolve eq179 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq1084 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq1083
       have i₂ := eq98 x
       grind)
    | exact superpose eq98 eq1083
    | exact resolve eq1083 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1083
  have eq1124 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq1084
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq1084
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq1084 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1084
  have eq1125 : (σ y) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq1124
  have eq1175 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq113 X0 (M.op X1 X0) X2 X3
       have i₂ := eq681 X0 X0 X1
       grind)
    | exact superpose eq681 eq113
    | exact resolve eq113 eq681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1187 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X1 X2))) = (M.op X2 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq113 (M.op X0 (M.op X1 X2)) (M.op X1 X2) X2 X1
       have i₂ := eq113 (M.op X1 X2) X0 (M.op X1 X2) X0
       grind)
    | exact superpose eq113 eq113
    | exact resolve eq113 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1223 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1175 X0 X1 x x
       have i₂ := eq113 X0 X0 x x
       grind)
    | exact superpose eq113 eq1175
    | exact resolve eq1175 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1175
  have eq1760 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X2) X0) (M.op (M.op (M.op X3 (M.op X0 X0)) (M.op X0 X0)) (M.op X4 X4))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq119 (M.op X0 X0) (M.op X3 (M.op X0 X0)) X1 X2 X4
       have i₂ := eq9 X0 (M.op X0 X0) X3
       grind)
    | exact superpose eq9 eq119
    | exact resolve eq119 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq1882 : ∀ X0 X1 X2 X4 : G, (M.op (M.op (M.op X1 X2) X0) (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X4 X4))) = X4 := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq1760 X0 X1 X2 x X4
       have i₂ := eq1223 (M.op X0 X0) x
       grind)
    | exact superpose eq1223 eq1760
    | exact resolve eq1760 eq1223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1760
  have eq1891 : ∀ X0 X1 X2 X4 : G, (M.op (M.op (M.op X1 X2) X0) (M.op (M.op X0 (M.op X0 X0)) (M.op X4 X4))) = X4 := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq1882 X0 X1 X2 X4
       have i₂ := eq25 X0 X0
       grind)
    | exact superpose eq25 eq1882
    | exact resolve eq1882 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1882
  have eq1975 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0)) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq124 (M.op X0 X0) (M.op X1 (M.op X0 X0)) X2 X3 X4
       have i₂ := eq9 X0 (M.op X0 X0) X1
       grind)
    | exact superpose eq9 eq124
    | exact resolve eq124 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq2069 : ∀ X0 X2 X3 X4 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 X0)) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq1975 X0 x X2 X3 X4
       have i₂ := eq1223 (M.op X0 X0) x
       grind)
    | exact superpose eq1223 eq1975
    | exact resolve eq1975 eq1223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1975
  have eq2100 : ∀ X0 X2 X3 X4 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 X0)) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq2069 X0 X2 X3 X4
       have i₂ := eq25 X0 X0
       grind)
    | exact superpose eq25 eq2069
    | exact resolve eq2069 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2069
  have eq2254 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 (M.op X1 X2))) = (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq138 X1 X2 (M.op X0 (M.op X0 X0)) X0
       have i₂ := eq108 X0
       grind)
    | exact superpose eq108 eq138
    | exact resolve eq138 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2350 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3))) = (M.op X4 (M.op (M.op X5 X4) (M.op X2 X3))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq138 X2 X3 X0 X1
       have i₂ := eq138 X2 X3 X4 X5
       grind)
    | exact superpose eq138 eq138
    | exact resolve eq138 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2380 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X3 (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq113 X3 X2 X3 X2
       have i₂ := eq138 X2 X3 X0 X1
       grind)
    | exact superpose eq138 eq113
    | exact resolve eq113 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2388 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X2 X3)) = (M.op X4 (M.op (M.op X5 X4) (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq113 (M.op X2 X3) X3 X4 X5
       have i₂ := eq138 X2 X3 X0 X1
       grind)
    | exact superpose eq138 eq113
    | exact resolve eq113 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq2587 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 (M.op X3 X0))) X0) = (M.op (M.op (M.op X1 (M.op X2 (M.op X3 X0))) X0) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq821 (M.op X3 X0) X2 (M.op (M.op X1 (M.op X2 (M.op X3 X0))) X0)
       have i₂ := eq819 (M.op X2 (M.op X3 X0)) X1 X0 X3
       grind)
    | exact superpose eq819 eq821
    | exact resolve eq821 eq819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq819 eq821
  have eq2620 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 (M.op X3 X0))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2587 X0 X1 X2 X3
       have i₂ := eq1223 X0 (M.op X1 (M.op X2 (M.op X3 X0)))
       grind)
    | exact superpose eq1223 eq2587
    | exact resolve eq2587 eq1223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1223 eq2587
  have eq4481 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X2) (M.op (M.op (M.op (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) (M.op X0 X0)) X0) (M.op (M.op X3 X4) (M.op (M.op (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) (M.op X0 X0)) X0)))) (M.op (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) (M.op X0 X0))) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq151 (M.op (M.op (M.op X4 X4) (M.op X4 (M.op X4 X4))) (M.op X4 X4)) X1 X2 X3 X4
       have i₂ := eq147 X4 X4 (M.op X4 X4) (M.op X4 (M.op X4 X4)) X4
       grind)
    | exact superpose eq147 eq151
    | exact resolve eq151 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147 eq151
  have eq4613 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X2) (M.op (M.op (M.op X0 (M.op X0 X0)) X0) (M.op (M.op X3 X4) (M.op (M.op X0 (M.op X0 X0)) X0)))) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq4481 X0 X1 X2 X3 X4
       have i₂ := eq688 X0 X0
       grind)
    | exact superpose eq688 eq4481
    | exact resolve eq4481 eq688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4481
  have eq4631 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X2) (M.op (M.op X0 X0) (M.op (M.op X3 X4) (M.op X0 X0)))) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq4613 X0 X1 X2 X3 X4
       have i₂ := eq132 X0 X0
       grind)
    | exact superpose eq132 eq4613
    | exact resolve eq4613 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4613
  have eq5167 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq185 X0 X1
       have i₂ := eq98 X0
       grind)
    | exact superpose eq98 eq185
    | (have j0 := eq185 X0 X1
       grind)
    | exact resolve eq185 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq5168 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5167 X0 X1
       have i₂ := eq98 X0
       grind)
    | exact superpose eq98 eq5167
    | (have j0 := eq5167 X0 X1
       grind)
    | exact resolve eq5167 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5167
  have eq5169 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5168 X0 X1
       have i₂ := eq98 X0
       grind)
    | exact superpose eq98 eq5168
    | (have j0 := eq5168 X0 X1
       grind)
    | exact resolve eq5168 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5168
  have eq5176 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5169 (τ X0) (τ X1)
       have i₂ := eq36 X1 X0
       grind)
    | exact superpose eq36 eq5169
    | (have j0 := eq5169 (τ X0) (τ X1)
       grind)
    | exact resolve eq5169 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq5169
  have eq5204 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (τ X1)) = (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5176 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq5176
    | (have j0 := eq5176 X0 X1
       grind)
    | exact resolve eq5176 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5176
  have eq5216 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ X1)) = (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5204 X0 X1
       have i₂ := eq94 X0
       grind)
    | exact superpose eq94 eq5204
    | (have j0 := eq5204 X0 X1
       grind)
    | exact resolve eq5204 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5204
  have eq5223 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (τ X1)) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5216 X0 X1
       have i₂ := eq94 X0
       grind)
    | exact superpose eq94 eq5216
    | (have j0 := eq5216 X0 X1
       grind)
    | exact resolve eq5216 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5216
  have eq5230 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5223 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq5223
    | (have j0 := eq5223 X0 X1
       grind)
    | exact resolve eq5223 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5223
  have eq5233 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5230 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq5230
    | (have j0 := eq5230 X0 X1
       grind)
    | exact resolve eq5230 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5230
  have eq5234 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5233 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5233
    | (have j0 := eq5233 X0 X1
       grind)
    | exact resolve eq5233 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5233
  have eq5235 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5234 X0 X1
       have i₂ := eq94 X0
       grind)
    | exact superpose eq94 eq5234
    | (have j0 := eq5234 X0 X1
       grind)
    | exact resolve eq5234 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq5234
  have eq5289 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X2 X0) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2620 (M.op X1 X0) X2 X0 (M.op X1 (M.op X1 X1))
       have i₂ := eq872 X1 X0
       grind)
    | exact superpose eq872 eq2620
    | exact resolve eq2620 eq872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq872 eq2620
  have eq5419 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X0) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5289 X0 X1 X2
       have i₂ := eq25 X1 X0
       grind)
    | exact superpose eq25 eq5289
    | exact resolve eq5289 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5289
  have eq5571 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) (σ X2)) ∨ (τ (M.op X0 X1)) = (k (τ (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1)))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) X2
       have i₂ := eq148 X0 X1 (σ X2)
       grind)
    | exact superpose eq148 eq23
    | (have j1 := eq148 X0 X1 (σ X2)
       grind)
    | exact resolve eq23 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq148
  have eq9228 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X1)) = (M.op (M.op X0 (M.op X2 X2)) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2100 X1 X0 (M.op X0 (M.op X0 X0)) X2
       have i₂ := eq108 X0
       grind)
    | exact superpose eq108 eq2100
    | exact resolve eq2100 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq27223 : (M.op x x) = (τ (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq1125
       grind)
    | exact superpose eq1125 eq10
    | exact resolve eq10 eq1125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1125
  have eq27293 : y = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq27223
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq27223
    | exact resolve eq27223 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27223
  have eq27294 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq27293
  have eq29272 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2380 (M.op X1 X1) (M.op x x) X1 (M.op X0 X0)
       have i₂ := eq24 X1 x x X0
       grind)
    | exact superpose eq24 eq2380
    | exact resolve eq2380 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq29563 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq29272 X0 X1
       have i₂ := eq5419 X0 (M.op X1 X1) X0
       grind)
    | exact superpose eq5419 eq29272
    | exact resolve eq29272 eq5419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5419 eq29272
  have eq29709 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = (M.op (M.op X1 X1) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq29563 (M.op X1 X0) (M.op X1 X1)
       have i₂ := eq2100 X0 X1 X1 X1
       grind)
    | exact superpose eq2100 eq29563
    | exact resolve eq29563 eq2100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2100
  have eq29726 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op (M.op X2 (M.op X1 X1)) X0) (M.op (M.op X2 (M.op X1 X1)) X0))) = (M.op (M.op (M.op X2 (M.op X1 X1)) X0) (M.op X0 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29563 (M.op (M.op X2 (M.op X1 X1)) X0) X1
       have i₂ := eq681 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq681 eq29563
    | exact resolve eq29563 eq681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29563
  have eq30159 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op (M.op X2 (M.op X1 X1)) X0) (M.op (M.op X2 (M.op X1 X1)) X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29726 X0 X1 X2
       have i₂ := eq688 X0 (M.op X2 (M.op X1 X1))
       grind)
    | exact superpose eq688 eq29726
    | exact resolve eq29726 eq688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29726
  have eq30176 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = (M.op (M.op X1 X1) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq29709 X0 X1
       have i₂ := eq25 X1 X0
       grind)
    | exact superpose eq25 eq29709
    | exact resolve eq29709 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29709
  have eq30291 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op (M.op X2 (M.op X1 X1)) X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30159 X0 X1 X2
       have i₂ := eq25 (M.op X2 (M.op X1 X1)) X0
       grind)
    | exact superpose eq25 eq30159
    | exact resolve eq30159 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30159
  have eq30306 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq30176 X0 X1
       have i₂ := eq688 X0 X1
       grind)
    | exact superpose eq688 eq30176
    | exact resolve eq30176 eq688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30176
  have eq30867 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) X0) = (M.op (M.op X1 X1) (M.op (M.op (M.op X2 X1) X0) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30306 (M.op (M.op X2 X1) X0) X1
       have i₂ := eq681 X0 X1 X2
       grind)
    | exact superpose eq681 eq30306
    | exact resolve eq30306 eq681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681 eq30306
  have eq31300 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30867 X0 X1 X2
       have i₂ := eq688 X0 (M.op X2 X1)
       grind)
    | exact superpose eq688 eq30867
    | exact resolve eq30867 eq688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688 eq30867
  have eq31536 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq31300 X2 X1 X0
       have i₂ := eq31300 X2 X1 X3
       grind)
    | (have i₁ := eq31300 X0 X1 X2
       have i₂ := eq31300 X0 X1 X1
       grind)
    | exact superpose eq31300 eq31300
    | exact resolve eq31300 eq31300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31300
  have eq43427 : ∀ X0 X1 X2 X3 : G, (M.op X3 X0) = (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X2 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq113 X0 (M.op X1 (M.op (M.op X2 X3) (M.op X2 X3))) X3 X2
       have i₂ := eq30291 X0 (M.op X2 X3) X1
       grind)
    | exact superpose eq30291 eq113
    | exact resolve eq113 eq30291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq30291
  have eq43523 : ∀ X0 X1 X2 X3 : G, (M.op X3 X0) = (M.op (M.op X1 (M.op X3 (M.op X2 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq43427 X0 X1 X2 X3
       have i₂ := eq25 X2 X3
       grind)
    | exact superpose eq25 eq43427
    | exact resolve eq43427 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq43427
  have eq50682 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (M.op (σ (M.op X0 X0)) (M.op (σ X0) (σ (M.op X0 X0)))) (σ X1)) ∨ (τ (σ (M.op X0 X0))) = (k (τ (M.op (σ (M.op X0 X0)) (M.op (σ X0) (σ (M.op X0 X0))))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5571 (σ X0) (σ X0) x
       have i₂ := eq98 X0
       grind)
    | exact superpose eq98 eq5571
    | exact resolve eq5571 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5571
  have eq50871 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (M.op (σ (M.op X0 X0)) (σ (M.op X0 (M.op X0 X0)))) (σ X1)) ∨ (τ (σ (M.op X0 X0))) = (k (τ (M.op (σ (M.op X0 X0)) (M.op (σ X0) (σ (M.op X0 X0))))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq50682 X0 X1
       have i₂ := eq212 X0
       grind)
    | exact superpose eq212 eq50682
    | (have j0 := eq50682 X0 X1
       grind)
    | exact resolve eq50682 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50682
  have eq50997 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (σ (M.op X0 X0)) ∨ (τ (σ (M.op X0 X0))) = (k (τ (M.op (σ (M.op X0 X0)) (M.op (σ X0) (σ (M.op X0 X0))))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq50871 X0 X1
       have i₂ := eq464 X0
       grind)
    | exact superpose eq464 eq50871
    | (have j0 := eq50871 X0 X1
       grind)
    | exact resolve eq50871 eq464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50871
  have eq51108 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = (k (τ (M.op (σ (M.op X0 X0)) (σ (M.op X0 (M.op X0 X0))))) X1) ∨ (M.op (σ X0) (σ X1)) ≠ (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq50997 X0 X1
       have i₂ := eq212 X0
       grind)
    | exact superpose eq212 eq50997
    | (have j0 := eq50997 X0 X1
       grind)
    | exact resolve eq50997 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50997
  have eq51218 : ∀ X0 X1 : G, (k (τ (σ X0)) X1) = (τ (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X1)) ≠ (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq51108 X0 X1
       have i₂ := eq464 X0
       grind)
    | exact superpose eq464 eq51108
    | (have j0 := eq51108 X0 X1
       grind)
    | exact resolve eq51108 eq464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464 eq51108
  have eq51311 : ∀ X0 X1 : G, (M.op X0 X0) = (k (τ (σ X0)) X1) ∨ (M.op (σ X0) (σ X1)) ≠ (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq51218 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq51218
    | (have j0 := eq51218 X0 X1
       grind)
    | exact resolve eq51218 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51218
  have eq51367 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq51311 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq51311
    | (have j0 := eq51311 X0 X1
       grind)
    | exact resolve eq51311 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51311
  have eq82456 : ∀ X0 X1 X2 X7 X8 : G, (M.op X1 (M.op (M.op X2 X1) X0)) = (M.op X7 (M.op (M.op X8 X7) X0)) := by
    intro X0 X1 X2 X7 X8
    first
    | (have i₁ := eq2350 X0 X1 (M.op (M.op X1 X2) (M.op (M.op X0 X0) (M.op (M.op x x) (M.op X0 X0)))) (M.op X0 (M.op X0 X0)) x x
       have i₂ := eq4631 X0 X1 X2 x x
       grind)
    | exact superpose eq4631 eq2350
    | exact resolve eq2350 eq4631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2350 eq4631
  have eq90734 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 (M.op X1 X1)) (M.op X1 X2))) = (M.op (M.op X2 X2) (M.op (M.op X0 (M.op X1 X1)) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1187 X1 X1 X1
       have i₂ := eq9228 X0 X1 X2
       grind)
    | exact superpose eq9228 eq1187
    | exact resolve eq1187 eq9228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9228
  have eq91699 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op (M.op X0 (M.op X1 X1)) (M.op X1 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq90734 X0 X1 X2
       have i₂ := eq878 X1 X2 X0
       grind)
    | exact superpose eq878 eq90734
    | exact resolve eq90734 eq878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq878 eq90734
  have eq112525 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X2))) = (M.op X2 (M.op X2 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2254 X0 X1 X2
       have i₂ := eq1187 X2 X1 X2
       grind)
    | exact superpose eq1187 eq2254
    | exact resolve eq2254 eq1187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1187 eq2254
  have eq113378 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X0 (M.op X1 X0))) X4) = (M.op (M.op X2 (M.op X3 (M.op X1 X0))) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq31536 X2 (M.op X3 (M.op X1 X0)) X4 (M.op X3 (M.op X3 X3))
       have i₂ := eq112525 X3 X1 X0
       grind)
    | exact superpose eq112525 eq31536
    | exact resolve eq31536 eq112525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31536 eq112525
  have eq113787 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X4) = (M.op (M.op X2 (M.op X3 (M.op X1 X0))) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq113378 X0 X1 X2 X3 X4
       have i₂ := eq43523 X4 X0 X1 X0
       grind)
    | exact superpose eq43523 eq113378
    | exact resolve eq113378 eq43523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43523 eq113378
  have eq124331 : ∀ X0 X1 X4 X5 X6 X7 : G, (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)) X0) = (M.op X4 (M.op (M.op X5 X4) (M.op X6 (M.op (M.op X7 X6) X0)))) := by
    intro X0 X1 X4 X5 X6 X7
    first
    | (have i₁ := eq2388 X0 X1 (M.op (M.op X1 x) X0) (M.op (M.op X0 (M.op X0 X0)) (M.op X4 X4)) X4 X5
       have i₂ := eq1891 X0 X1 x X4
       grind)
    | exact superpose eq1891 eq2388
    | exact resolve eq2388 eq1891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1891 eq2388
  have eq126249 : ∀ X0 X4 X5 X6 X7 : G, (M.op X0 X0) = (M.op X4 (M.op (M.op X5 X4) (M.op X6 (M.op (M.op X7 X6) X0)))) := by
    intro X0 X4 X5 X6 X7
    first
    | (have i₁ := eq124331 X0 x X4 X5 X6 X7
       have i₂ := eq132 X0 (M.op x (M.op x x))
       grind)
    | exact superpose eq132 eq124331
    | exact resolve eq124331 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq124331
  have eq561775 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X6 X6) = (M.op X5 (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X3 (M.op X4 X5))) X6)))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq126249 X6 X5 X4 (M.op X3 (M.op X4 X5)) X2
       have i₂ := eq82456 (M.op (M.op X2 (M.op X3 (M.op X4 X5))) X6) (M.op X4 X5) X3 X0 X1
       grind)
    | (have i₁ := eq126249 X6 X5 X4 (M.op X3 (M.op X4 X5)) X2
       have i₂ := eq82456 (M.op (M.op X2 (M.op X3 (M.op X4 X5))) X6) X0 X1 (M.op X4 X5) X3
       grind)
    | exact superpose eq82456 eq126249
    | exact resolve eq126249 eq82456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82456 eq126249
  have eq564663 : ∀ X0 X1 X5 X6 : G, (M.op X6 X6) = (M.op X5 (M.op X0 (M.op (M.op X1 X0) (M.op X5 X6)))) := by
    intro X0 X1 X5 X6
    first
    | (have i₁ := eq561775 X0 X1 x x x X5 X6
       have i₂ := eq113787 X5 x x x X6
       grind)
    | exact superpose eq113787 eq561775
    | exact resolve eq561775 eq113787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113787 eq561775
  have eq1689269 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq27294
       grind)
    | exact superpose eq27294 eq12
    | (have j0 := eq12 x x
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq27294
       grind)
    | exact resolve eq12 eq27294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27294
  have eq1689781 : (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq1689269
  have eq1690003 : (k x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq51367 x y
       grind)
    | (have r₁ := eq1689781
       have r₂ := eq51367 x y
       grind)
    | exact resolve eq1689781 eq51367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51367 eq1689781
  have eq1690163 : (M.op x x) ≠ (M.op x x) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq5235 x y
       have i₂ := eq1690003
       grind)
    | exact superpose eq1690003 eq5235
    | (have j0 := eq5235 x y
       grind)
    | (have r₁ := eq5235 x y
       have r₂ := eq1690003
       grind)
    | exact resolve eq5235 eq1690003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5235 eq1690003
  have eq1690189 : (M.op x x) ≠ (M.op x x) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq1690163
  have eq1690190 : (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq1690189
  have eq1694367 : ∀ X0 X1 : G, (M.op y y) = (M.op x (M.op X0 (M.op (M.op X1 X0) (M.op x x)))) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq564663 X0 X1 x y
       have i₂ := eq1690190
       grind)
    | exact superpose eq1690190 eq564663
    | exact resolve eq564663 eq1690190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564663 eq1690190
  have eq1694391 : (M.op x x) = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1694367 x x
       have i₂ := eq2380 x x x x
       grind)
    | exact superpose eq2380 eq1694367
    | exact resolve eq1694367 eq2380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2380 eq1694367
  have eq1695423 : ∀ X0 : G, y = (M.op (M.op x x) (M.op (M.op X0 (M.op x x)) (M.op x x))) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq91699 X0 y y
       have i₂ := eq1694391
       grind)
    | exact superpose eq1694391 eq91699
    | exact resolve eq91699 eq1694391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91699 eq1694391
  have eq1695836 : x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1695423 x
       have i₂ := eq9 x (M.op x x) x
       grind)
    | exact superpose eq9 eq1695423
    | exact resolve eq1695423 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1695423
  have eq1696262 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1695836
       grind)
    | exact superpose eq1695836 eq16
    | exact resolve eq16 eq1695836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1695836
  have eq1696265 : y = (M.op x x) := by
    first
    | (have r₁ := eq1696262
       have r₂ := eq98 x
       grind)
    | exact resolve eq1696262 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq1696262
  have eq1696285 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq212 x
       have i₂ := eq1696265
       grind)
    | exact superpose eq1696265 eq212
    | exact resolve eq212 eq1696265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212 eq1696265
  have eq1697522 : False := by grind
  exact eq1697522
