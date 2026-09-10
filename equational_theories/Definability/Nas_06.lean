import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4447`: `x ◇ (y ◇ x) = (y ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if X = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxx_pyx_pxy_Equation4447 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4447 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4447.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X1) X2) := by
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
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X1) (M.op X1 X1)) X3) = (M.op X2 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op X1 X1) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | (have i₁ := eq14 (M.op X1 X0) X0 X2
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X0) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq14 x X0 X3
       have i₂ := eq14 x X0 X1
       grind)
    | (have i₁ := eq14 (M.op X1 X1) X1 x
       have i₂ := eq14 X0 X1 (M.op X1 (M.op X1 X1))
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 X1) X2 X3
       have i₂ := eq14 X0 X1 (M.op X2 (M.op X1 X1))
       grind)
    | (have i₁ := eq14 X0 X1 X2
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 X1 x
       have i₂ := eq14 X2 X1 x
       grind)
    | (have i₁ := eq14 X0 X1 (M.op X1 (M.op X1 X1))
       have i₂ := eq14 (M.op X1 X1) X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq77 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq81 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq77 sF2
       grind)
    | exact superpose eq77 eq50
    | exact resolve eq50 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq82 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq81
       have i₂ := eq77 x
       grind)
    | exact superpose eq77 eq81
    | exact resolve eq81 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq91 : (σ (k y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq75
       have i₂ := eq77 sF3
       grind)
    | exact superpose eq77 eq75
    | exact resolve eq75 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq92 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq91
       have i₂ := eq77 y
       grind)
    | exact superpose eq77 eq91
    | exact resolve eq91 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq100 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
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
  have eq105 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
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
  have eq106 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq21 eq105
    | exact resolve eq105 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq117 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq92
       grind)
    | exact superpose eq92 eq16
    | exact resolve eq16 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq133 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq136 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq133
       have i₂ := eq77 sF1
       grind)
    | exact superpose eq77 eq133
    | exact resolve eq133 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq138 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq136
       have i₂ := eq77 sF0
       grind)
    | exact superpose eq77 eq136
    | exact resolve eq136 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq159 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq138 eq16
    | exact resolve eq16 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq269 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq35 X0 (τ X0)
       have i₂ := eq77 (τ X0)
       grind)
    | exact superpose eq77 eq35
    | exact resolve eq35 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq280 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq269 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq269
    | exact resolve eq269 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269
  have eq282 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq280 X0
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq280
    | exact resolve eq280 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq280
  have eq670 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq282 X0
       grind)
    | exact superpose eq282 eq16
    | exact resolve eq16 eq282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282
  have eq745 : ∀ X0 : G, (M.op y (M.op x y)) = (M.op X0 (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq56 y x X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq56
    | (have j0 := eq56 y x X0
       grind)
    | exact resolve eq56 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq796 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op y (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq745 x
       have i₂ := eq54 x x X0 X1
       grind)
    | (have i₁ := eq745 (M.op x x)
       have i₂ := eq54 X0 X1 x (M.op x (M.op x x))
       grind)
    | exact superpose eq54 eq745
    | (have j1 := eq54 y x X0 X1
       grind)
    | exact resolve eq745 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq798 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op y (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq745 (M.op x x)
       have i₂ := eq54 X0 X1 x (M.op x (M.op x x))
       grind)
    | (have i₁ := eq745 X0
       have i₂ := eq54 X0 x x x
       grind)
    | exact superpose eq54 eq745
    | exact resolve eq745 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq745
  have eq1064 : ∀ X1 X2 X3 : G, (M.op (M.op (M.op X1 X1) (M.op X1 X1)) X3) = (M.op X2 (M.op y (M.op x y))) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq52 x X1 X2 X3
       have i₂ := eq798 x X1
       grind)
    | (have i₁ := eq52 y x X2 X3
       have i₂ := eq798 x X1
       grind)
    | exact superpose eq798 eq52
    | exact resolve eq52 eq798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq798
  have eq1065 : ∀ X2 : G, (M.op y (M.op x y)) = (M.op X2 (M.op y (M.op x y))) := by
    intro X2
    first
    | (have i₁ := eq1064 x X2 x
       have i₂ := eq796 (M.op x x) x
       grind)
    | exact superpose eq796 eq1064
    | exact resolve eq1064 eq796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1064
  have eq1289 : (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) = (τ (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y))))) := by
    first
    | exact superpose eq159 eq670
    | exact resolve eq670 eq159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159 eq670
  have eq1329 : (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) = (τ (M.op y (M.op x y))) := by
    first
    | (have i₁ := eq1289
       have i₂ := eq796 sF1 (M.op sF1 sF1)
       grind)
    | exact superpose eq796 eq1289
    | exact resolve eq1289 eq796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1289
  have eq1335 : (M.op y (M.op x y)) = (τ (M.op y (M.op x y))) := by
    first
    | (have i₁ := eq1329
       have i₂ := eq796 sF0 (M.op sF0 sF0)
       grind)
    | exact superpose eq796 eq1329
    | exact resolve eq1329 eq796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq796 eq1329
  have eq1339 : (M.op y (M.op x y)) = (σ (M.op y (M.op x y))) := by
    first
    | exact superpose eq1335 eq15
    | exact resolve eq15 eq1335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1335
  have eq13516 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq106 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq13517 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq27 eq13516
    | exact resolve eq13516 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13516
  have eq13528 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq13517
       have r₂ := eq28
       grind)
    | exact resolve eq13517 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13517
  have eq13653 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq13528 eq117
    | exact resolve eq117 eq13528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq13528
  have eq13704 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq30 eq13653
    | exact resolve eq13653 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13653
  have eq13705 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq13704
  have eq13719 : ∀ X0 X1 : G, (M.op y X0) = (M.op y X1) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq53 y X1 x
       have i₂ := eq13705
       grind)
    | exact superpose eq13705 eq53
    | exact resolve eq53 eq13705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq14045 : ∀ X0 : G, y = (M.op y X0) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq13705
       have i₂ := eq13719 y X0
       grind)
    | (have i₁ := eq13705
       have i₂ := eq13719 X0 y
       grind)
    | exact superpose eq13719 eq13705
    | exact resolve eq13705 eq13719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13705 eq13719
  have eq14102 : ∀ X0 : G, y = (M.op y X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq14045 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14045
  have eq14171 : ∀ X0 : G, y = (M.op X0 y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1065 x
       have i₂ := eq14102 sF0
       grind)
    | exact superpose eq14102 eq1065
    | exact resolve eq1065 eq14102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1065
  have eq14175 : y = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1339
       have i₂ := eq14102 sF0
       grind)
    | exact superpose eq14102 eq1339
    | exact resolve eq1339 eq14102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1339 eq14102
  have eq14253 : (σ x) = (σ y) ∨ y = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq14175
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq14175
    | exact resolve eq14175 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14175
  have eq14273 : y = (τ (σ x)) ∨ y = (σ y) ∨ x = y := by
    first
    | exact superpose eq14253 eq30
    | exact resolve eq30 eq14253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14253
  have eq14385 : x = y ∨ y = (σ y) ∨ x = y := by
    first
    | exact superpose eq29 eq14273
    | exact resolve eq14273 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14273
  have eq14386 : y = (σ y) ∨ x = y := by grind
  clear eq14385
  have eq14530 : (M.op (σ x) (σ y)) = (M.op (σ x) y) ∨ x = y := by
    first
    | exact superpose eq14386 eq27
    | exact resolve eq27 eq14386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15543 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq14171 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14171
    | (have j0 := eq14171 x
       grind)
    | exact resolve eq14171 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15597 : y = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq14530
       have i₂ := eq14171 sF2
       grind)
    | exact superpose eq14171 eq14530
    | exact resolve eq14530 eq14171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14171 eq14530
  have eq15599 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op (σ x) (σ y)) := by grind
  clear eq15597
  have eq15645 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq15543 eq30
    | exact resolve eq30 eq15543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15543
  have eq15774 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq15645
    | exact resolve eq15645 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15645
  have eq15775 : y = (M.op x y) ∨ x = y := by grind
  clear eq15774
  have eq15790 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq15775 eq21
    | exact resolve eq21 eq15775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15775
  have eq15919 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq15790
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq15790
    | exact resolve eq15790 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15790
  have eq16135 : y = (σ (M.op x y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq15919 eq14386
    | exact resolve eq14386 eq15919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14386 eq15919
  have eq16146 : y = (σ (M.op x y)) ∨ x = y := by grind
  clear eq16135
  have eq16356 : y = (τ (σ x)) ∨ x = y ∨ y = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15599 eq30
    | exact resolve eq30 eq15599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq15599
  have eq16488 : x = y ∨ x = y ∨ y = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29 eq16356
    | exact resolve eq16356 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq16356
  have eq16489 : y = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq16488
  have eq16509 : y ≠ (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq16489 eq28
    | exact resolve eq28 eq16489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16489
  have eq16512 : x = y := by
    first
    | (have r₁ := eq16509
       have r₂ := eq16146
       grind)
    | exact resolve eq16509 eq16146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16146 eq16509
  have eq16513 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq16512
       grind)
    | exact superpose eq16512 eq19
    | exact resolve eq19 eq16512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq16514 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq16512
       grind)
    | exact superpose eq16512 eq25
    | exact resolve eq25 eq16512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq16512
  have eq16638 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq16514
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq16514
    | exact resolve eq16514 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq16514
  have eq16655 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq16638 eq27
    | exact resolve eq27 eq16638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq16638
  have eq16893 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq16655 eq82
    | exact resolve eq82 eq16655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq16655
  have eq16951 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq16893
       have i₂ := eq16513
       grind)
    | exact superpose eq16513 eq16893
    | exact resolve eq16893 eq16513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16513 eq16893
  have eq16971 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16951 eq15
    | exact resolve eq15 eq16951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16951
  have eq17019 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq16971
    | exact resolve eq16971 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq16971
  have eq17028 : False := by grind
  exact eq17028

/-- `Equation4478`: `x ◇ (y ◇ y) = (x ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyy_x_pyy_pxy_Equation4478 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law4478 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4478.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 X2) X3) := by
    intro X0 X1 X2 X3
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq21 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq17 X1 X0
       grind)
    | exact superpose eq17 eq10
    | exact resolve eq10 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op (τ X0) X1) ∨ (M.op X1 (τ X0)) = X1 := by
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
  have eq33 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq21 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq21
    | exact resolve eq21 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq669 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq25 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq25
    | exact resolve eq25 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq716 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq669 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq669
    | (have j0 := eq669 X0 X1
       grind)
    | exact resolve eq669 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669
  have eq2086 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq716 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq716 X0 X1
       grind)
    | exact superpose eq716 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq716 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq716 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq716 X1 X1
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X0
       have r₂ := eq716 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716
  have eq2090 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2086 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2086
  have eq2091 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq2090 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2090
  have eq2181 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq2091 X1 X0
       grind)
    | exact superpose eq2091 eq10
    | (have j1 := eq2091 X1 X0
       grind)
    | exact resolve eq10 eq2091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2091
  have eq2379 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2181 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq2181
    | (have j0 := eq2181 X0 X1
       grind)
    | exact resolve eq2181 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2181
  have eq2644 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq2379 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2379
  have eq2648 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq2644 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq2644 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq2644 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq2644 (M.op X0 X0) X0
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq2644 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2644
  have eq2717 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq2648 (σ X0) (σ X1)
       grind)
    | exact superpose eq2648 eq15
    | (have j1 := eq2648 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq2648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2725 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq2648 (τ X0) X1
       grind)
    | exact superpose eq2648 eq18
    | (have j1 := eq2648 (τ X0) X1
       grind)
    | exact resolve eq18 eq2648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3088 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2725 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2725
    | exact resolve eq2725 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2725
  have eq3146 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3088 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3088
    | (have j0 := eq3088 X0 X1
       grind)
    | exact resolve eq3088 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3088
  have eq3506 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2717 x y
       grind)
    | exact superpose eq2717 eq16
    | (have j1 := eq2717 x y
       grind)
    | exact resolve eq16 eq2717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3534 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq2717 X1 X0
       grind)
    | exact superpose eq2717 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq2717 X1 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq2717 X0 X1
       grind)
    | exact resolve eq12 eq2717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3536 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq2717 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3538 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq3534 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3534
  have eq3546 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3538 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq3538
    | (have j0 := eq3538 X0 X1
       grind)
    | exact resolve eq3538 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3538
  have eq3575 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3536 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq3536
    | (have j0 := eq3536 (τ X0)
       grind)
    | exact resolve eq3536 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3592 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3575 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3575
    | (have j0 := eq3575 X0
       grind)
    | exact resolve eq3575 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3575
  have eq3607 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3592 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3592
    | (have j0 := eq3592 X0
       grind)
    | exact resolve eq3592 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3592
  have eq3644 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq3607 (τ X0)
       have i₂ := eq33 X0 X0
       grind)
    | exact superpose eq33 eq3607
    | (have j0 := eq3607 (τ X0)
       grind)
    | exact resolve eq3607 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq3607
  have eq3682 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq3506
       have i₂ := eq3146 x y
       grind)
    | exact superpose eq3146 eq3506
    | (have j1 := eq3146 (σ x) (σ y)
       grind)
    | (have r₁ := eq3506
       have r₂ := eq3146 x y
       grind)
    | exact resolve eq3506 eq3146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3146 eq3506
  have eq3687 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq3682
  have eq3701 : ∀ X0 X1 : G, (M.op (σ y) (M.op X0 X0)) = (M.op (σ y) X1) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ y) X0 (σ x) X1
       have i₂ := eq3687
       grind)
    | exact superpose eq3687 eq9
    | exact resolve eq9 eq3687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18049 : ∀ X0 X2 : G, (M.op (σ y) X0) = (M.op (σ y) X2) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    intro X0 X2
    first
    | (have i₁ := eq3701 x X2
       have i₂ := eq3701 x X0
       grind)
    | (have i₁ := eq3701 X0 x
       have i₂ := eq3701 X0 (M.op X0 X0)
       grind)
    | exact superpose eq3701 eq3701
    | exact resolve eq3701 eq3701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3701
  have eq18185 : ∀ X0 X2 : G, (M.op (σ y) X0) = (M.op (σ y) X2) ∨ y = (M.op y x) := by
    intro X0 X2
    first
    | (have j0 := eq18049 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18049
  have eq18370 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq3687
       have i₂ := eq18185 (σ x) X0
       grind)
    | (have i₁ := eq3687
       have i₂ := eq18185 X0 (σ x)
       grind)
    | exact superpose eq18185 eq3687
    | exact resolve eq3687 eq18185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3687 eq18185
  have eq18428 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq18370 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18370
  have eq18525 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (σ y)
       have i₂ := eq18428 X0
       grind)
    | exact superpose eq18428 eq12
    | (have j0 := eq12 X0 (σ y)
       grind)
    | (have r₁ := eq12 X0 (σ y)
       have r₂ := eq18428 X0
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq18428 X0
       grind)
    | exact resolve eq12 eq18428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18428
  have eq18560 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq18525 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18525
  have eq18591 : (τ (σ y)) ≠ (τ (σ y)) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq3644 (σ y)
       have i₂ := eq18560 (σ y)
       grind)
    | exact superpose eq18560 eq3644
    | (have j0 := eq3644 (σ y)
       grind)
    | exact resolve eq3644 eq18560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3644 eq18560
  have eq18633 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ y = (M.op y x) := by grind
  clear eq18591
  have eq18658 : y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq18633
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq18633
    | exact resolve eq18633 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18633
  have eq18717 : ∀ X0 X1 : G, (M.op y (M.op X0 X0)) = (M.op y X1) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq9 y X0 y X1
       have i₂ := eq18658
       grind)
    | exact superpose eq18658 eq9
    | exact resolve eq9 eq18658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20763 : ∀ X0 X2 : G, (M.op y X0) = (M.op y X2) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    intro X0 X2
    first
    | (have i₁ := eq18717 x X2
       have i₂ := eq18717 x X0
       grind)
    | (have i₁ := eq18717 X0 x
       have i₂ := eq18717 X0 (M.op X0 X0)
       grind)
    | exact superpose eq18717 eq18717
    | exact resolve eq18717 eq18717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18717
  have eq20921 : ∀ X0 X2 : G, (M.op y X0) = (M.op y X2) ∨ y = (M.op y x) := by
    intro X0 X2
    first
    | (have j0 := eq20763 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20763
  have eq21112 : ∀ X0 : G, y = (M.op y X0) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq18658
       have i₂ := eq20921 y X0
       grind)
    | (have i₁ := eq18658
       have i₂ := eq20921 X0 y
       grind)
    | exact superpose eq20921 eq18658
    | exact resolve eq18658 eq20921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18658
  have eq21192 : ∀ X0 : G, y ≠ (M.op y X0) ∨ y = (M.op y x) := by
    intro X0
    grind
  clear eq20921
  have eq21199 : ∀ X0 : G, y = (M.op y X0) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq21112 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21112
  have eq21221 : y = (M.op y x) := by
    first
    | (have j0 := eq21199 x
       grind)
    | (have r₁ := eq21199 x
       have r₂ := eq21192 x
       grind)
    | (have r₁ := eq21199 x
       have r₂ := eq21192 x
       grind)
    | exact resolve eq21199 eq21192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21192 eq21199
  have eq21264 : ∀ X0 X1 : G, (M.op y (M.op X0 X0)) = (M.op y X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 y X0 x X1
       have i₂ := eq21221
       grind)
    | exact superpose eq21221 eq9
    | exact resolve eq9 eq21221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21330 : ∀ X0 X2 : G, (M.op y X0) = (M.op y X2) := by
    intro X0 X2
    first
    | (have i₁ := eq21264 x X2
       have i₂ := eq21264 x X0
       grind)
    | (have i₁ := eq21264 X0 x
       have i₂ := eq21264 X0 (M.op X0 X0)
       grind)
    | exact superpose eq21264 eq21264
    | exact resolve eq21264 eq21264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21457 : ∀ X0 X1 : G, y ≠ (M.op y (M.op X0 X0)) ∨ (k X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 y
       have i₂ := eq21264 X0 X1
       grind)
    | (have i₁ := eq12 (M.op X0 X0) y
       have i₂ := eq21264 X0 X1
       grind)
    | exact superpose eq21264 eq12
    | (have j0 := eq12 (M.op X0 X0) y
       grind)
    | exact resolve eq12 eq21264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21264
  have eq21660 : ∀ X0 : G, y = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq21221
       have i₂ := eq21330 x X0
       grind)
    | (have i₁ := eq21221
       have i₂ := eq21330 X0 x
       grind)
    | exact superpose eq21330 eq21221
    | exact resolve eq21221 eq21330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21221 eq21330
  have eq22252 : ∀ X1 : G, y ≠ y ∨ (k X1 y) = X1 := by
    intro X1
    first
    | (have i₁ := eq21457 x X1
       have i₂ := eq21660 (M.op x x)
       grind)
    | exact superpose eq21660 eq21457
    | (have j0 := eq21457 x X1
       grind)
    | (have r₁ := eq21457 x X1
       have r₂ := eq21660 (M.op x x)
       grind)
    | exact resolve eq21457 eq21660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21457
  have eq22263 : ∀ X1 : G, (k X1 y) = X1 := by
    intro X1
    first
    | (have j0 := eq22252 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22252
  have eq22778 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq3536 y
       have i₂ := eq22263 y
       grind)
    | exact superpose eq22263 eq3536
    | (have j0 := eq3536 y
       grind)
    | exact resolve eq3536 eq22263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3536 eq22263
  have eq22813 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq22778
  have eq23699 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X0 (σ y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 (σ y) X1 X2
       have i₂ := eq22813
       grind)
    | exact superpose eq22813 eq9
    | exact resolve eq9 eq22813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22813
  have eq23755 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 x x
       have i₂ := eq23699 X0 x x
       grind)
    | exact superpose eq23699 eq9
    | exact resolve eq9 eq23699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25229 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq23755 X0 y
       have i₂ := eq21660 y
       grind)
    | exact superpose eq21660 eq23755
    | exact resolve eq23755 eq21660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21660
  have eq25335 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X0 y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23699 X0 X1 X2
       have i₂ := eq25229 X0
       grind)
    | exact superpose eq25229 eq23699
    | exact resolve eq23699 eq25229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23699
  have eq25336 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq23755 X0 X1
       have i₂ := eq25229 X0
       grind)
    | exact superpose eq25229 eq23755
    | exact resolve eq23755 eq25229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23755
  have eq25388 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25229 (σ x)
       grind)
    | exact superpose eq25229 eq16
    | exact resolve eq16 eq25229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25229
  have eq42042 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2717 X1 X0
       have i₂ := eq3546 X1 X0
       grind)
    | exact superpose eq3546 eq2717
    | (have j0 := eq2717 X1 X0
       have j1 := eq3546 X0 X1
       grind)
    | exact resolve eq2717 eq3546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2717 eq3546
  have eq42102 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq42042 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42042
  have eq43969 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq42102 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq42102
    | exact resolve eq42102 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42102
  have eq44133 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq43969 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq43969
    | (have j0 := eq43969 X0 X1
       grind)
    | exact resolve eq43969 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq43969
  have eq44135 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq44133 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq44133
    | (have j0 := eq44133 X0 X1
       grind)
    | exact resolve eq44133 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44133
  have eq45663 : ∀ X0 : G, (σ X0) ≠ (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq44135 (σ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44135
  have eq45678 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq45663 X0
       have j1 := eq2648 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq45663 X0
       have r₂ := eq2648 (σ X0) (σ X0)
       grind)
    | exact resolve eq45663 eq2648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2648 eq45663
  have eq45730 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq45678 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq45678
    | exact resolve eq45678 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45678
  have eq46205 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq45730 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq45730
    | exact resolve eq45730 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46296 : ∀ X0 X1 : G, (M.op X1 (σ (k X0 X0))) = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq25336 X1 (σ X0)
       have i₂ := eq45730 X0
       grind)
    | exact superpose eq45730 eq25336
    | exact resolve eq25336 eq45730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46302 : ∀ X0 X1 : G, (M.op (σ X0) y) = (M.op (σ (k X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq25335 (σ X0) (σ X0) X1
       have i₂ := eq45730 X0
       grind)
    | exact superpose eq45730 eq25335
    | exact resolve eq25335 eq45730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46379 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq46205 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq46205
    | exact resolve eq46205 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq46205
  have eq46424 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq46379 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq46379
    | exact resolve eq46379 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46379
  have eq46494 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq45730 X0
       have i₂ := eq46424 X0
       grind)
    | exact superpose eq46424 eq45730
    | exact resolve eq45730 eq46424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45730
  have eq46556 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq46296 X0 X1
       have i₂ := eq46424 X0
       grind)
    | exact superpose eq46424 eq46296
    | exact resolve eq46296 eq46424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46296
  have eq46558 : ∀ X0 X1 : G, (M.op (σ X0) y) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq46302 X0 X1
       have i₂ := eq46424 X0
       grind)
    | exact superpose eq46424 eq46302
    | exact resolve eq46302 eq46424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46302 eq46424
  have eq47839 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) y) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq46494 (M.op X0 X0)
       have i₂ := eq46556 X0 (σ (M.op X0 X0))
       grind)
    | exact superpose eq46556 eq46494
    | exact resolve eq46494 eq46556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46494 eq46556
  have eq47873 : ∀ X0 : G, (σ (M.op (M.op X0 X0) y)) = (M.op (σ (M.op X0 X0)) y) := by
    intro X0
    first
    | (have i₁ := eq47839 X0
       have i₂ := eq25336 (M.op X0 X0) X0
       grind)
    | exact superpose eq25336 eq47839
    | exact resolve eq47839 eq25336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25336 eq47839
  have eq47905 : ∀ X0 : G, (M.op (σ X0) y) = (σ (M.op (M.op X0 X0) y)) := by
    intro X0
    first
    | (have i₁ := eq47873 X0
       have i₂ := eq46558 X0 y
       grind)
    | exact superpose eq46558 eq47873
    | exact resolve eq47873 eq46558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46558 eq47873
  have eq47917 : ∀ X0 : G, (M.op (σ X0) y) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq47905 X0
       have i₂ := eq25335 X0 X0 y
       grind)
    | exact superpose eq25335 eq47905
    | exact resolve eq47905 eq25335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25335 eq47905
  have eq48032 : (M.op (σ x) y) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq25388
       have i₂ := eq47917 x
       grind)
    | exact superpose eq47917 eq25388
    | (have r₁ := eq25388
       have r₂ := eq47917 x
       grind)
    | exact resolve eq25388 eq47917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25388 eq47917
  have eq48035 : False := by grind
  exact eq48035

/-- `Equation4487`: `x ◇ (y ◇ y) = (y ◇ z) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then Y else if m(Y,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_y_y_pxx_pyx_Equation4487 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4487 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4487.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X1 X2) X2) := by
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
  have eq179 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X3) (M.op X1 X3))) = (M.op (M.op X0 (M.op X1 X1)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X2 (M.op X1 X3) X3
       have i₂ := eq16 X0 X1 X3
       grind)
    | (have i₁ := eq16 X0 X0 (M.op X1 X1)
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 : G, (M.op X0 (M.op x x)) = (M.op (M.op x y) y) := by
    intro X0
    first
    | (have i₁ := eq16 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 x y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ x))) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X1) = (M.op X2 (M.op X3 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X2 X3 (M.op X0 X0)
       have i₂ := eq16 (M.op X3 (M.op X0 X0)) X0 X1
       grind)
    | (have i₁ := eq16 X0 X1 X2
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : (σ (M.op y y)) = (k (σ y) (σ (M.op y y))) := by
    first
    | (have i₁ := eq36 (M.op y y)
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq36
    | exact resolve eq36 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : ∀ X1 : G, (M.op (M.op x y) y) = (M.op (M.op x X1) X1) := by
    intro X1
    first
    | (have i₁ := eq16 x x X1
       have i₂ := eq180 x
       grind)
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 (M.op x x)
       have i₂ := eq180 (M.op X1 (M.op x x))
       grind)
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq205 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq181 eq16
    | exact resolve eq16 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq206 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq205 x x
       have i₂ := eq196 x x
       grind)
    | exact superpose eq196 eq205
    | exact resolve eq205 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq219 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op x (M.op X0 X0)) X0 X1
       have i₂ := eq191 (M.op X0 X0)
       grind)
    | exact superpose eq191 eq16
    | exact resolve eq16 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x X1) (M.op x X1))) = (M.op (M.op (M.op x y) y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 (M.op x X1) X1
       have i₂ := eq191 X1
       grind)
    | (have i₁ := eq16 X0 (M.op x y) y
       have i₂ := eq191 X1
       grind)
    | exact superpose eq191 eq16
    | exact resolve eq16 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq222 : ∀ X1 : G, (M.op (M.op x y) y) = (M.op (M.op (M.op x y) y) X1) := by
    intro X1
    first
    | (have i₁ := eq221 x X1
       have i₂ := eq196 x (M.op x X1)
       grind)
    | exact superpose eq196 eq221
    | exact resolve eq221 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq262 : (τ (M.op (σ x) (σ x))) = (k x (τ (M.op (σ x) (σ x)))) := by
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
  have eq273 : (τ (M.op (σ y) (σ y))) = (k y (τ (M.op (σ y) (σ y)))) := by
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
  have eq383 : (M.op (M.op x y) y) = (k (M.op (M.op x y) y) (M.op (M.op x y) y)) := by
    first
    | exact superpose eq222 eq174
    | exact resolve eq174 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq1145 : (M.op x y) = (k y x) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
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
  have eq1154 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
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
  have eq1159 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1160 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1159 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1159
  have eq1247 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1160 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq1160
    | (have j0 := eq1160 (σ X0)
       grind)
    | exact resolve eq1160 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5187 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq1145
       grind)
    | exact superpose eq1145 eq39
    | exact resolve eq39 eq1145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq5188 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq5187
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq5187
    | exact resolve eq5187 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq5187
  have eq5190 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq5188
    | exact resolve eq5188 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5188
  have eq17680 : (σ (M.op (M.op x y) y)) ≠ (σ (M.op (M.op x y) y)) ∨ (σ (M.op (M.op x y) y)) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by
    first
    | exact superpose eq383 eq1247
    | (have j0 := eq1247 (M.op (M.op x y) y)
       grind)
    | exact resolve eq1247 eq383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383
  have eq17716 : (σ (M.op (M.op x y) y)) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by grind
  clear eq17680
  have eq17849 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by
    intro X0 X1
    first
    | exact superpose eq17716 eq183
    | exact resolve eq183 eq17716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq17852 : (M.op (M.op x y) y) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by
    first
    | exact superpose eq17716 eq219
    | exact resolve eq219 eq17716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17855 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (σ (M.op (M.op x y) y)) := by
    intro X0 X1
    first
    | exact superpose eq17716 eq17849
    | exact resolve eq17849 eq17716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17849
  have eq17870 : (M.op (M.op x y) y) = (σ (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq17855 x x
       have i₂ := eq196 x x
       grind)
    | exact superpose eq196 eq17855
    | exact resolve eq17855 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17855
  have eq17880 : (M.op (M.op x y) y) = (τ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq17870 eq15
    | exact resolve eq15 eq17870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18818 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq5190 eq1154
    | exact resolve eq1154 eq5190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18825 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq18818
       have r₂ := eq27
       grind)
    | exact resolve eq18818 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18818
  have eq18931 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq18825 eq273
    | exact resolve eq273 eq18825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273 eq18825
  have eq18976 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq18931
    | exact resolve eq18931 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18931
  have eq18988 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (k y x) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq18976
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq18976
       have r₂ := eq13 x x
       grind)
    | (have r₁ := eq18976
       have r₂ := eq13 y x
       grind)
    | exact resolve eq18976 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18976
  have eq18996 : (τ (σ x)) = (k x (τ (σ x))) ∨ x = (k y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq18988 eq262
    | exact resolve eq262 eq18988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262 eq18988
  have eq19040 : x = (k x x) ∨ x = (k y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq18996
    | exact resolve eq18996 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18996
  have eq19050 : x = (k y x) ∨ x = (k x x) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq19040
       have r₂ := eq13 x x
       grind)
    | exact resolve eq19040 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19040
  have eq19055 : x = (M.op x y) ∨ x = (k x x) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq19050
       have i₂ := eq1145
       grind)
    | exact superpose eq1145 eq19050
    | exact resolve eq19050 eq1145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19058 : x = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op y y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq1145
       have i₂ := eq19050
       grind)
    | exact superpose eq19050 eq1145
    | exact resolve eq1145 eq19050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1145
  have eq19059 : (σ x) = (k (σ y) (σ x)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq19050
       grind)
    | exact superpose eq19050 eq36
    | exact resolve eq36 eq19050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq19050
  have eq19062 : (σ x) = (k (σ y) (σ x)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq19059
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq19059
    | exact resolve eq19059 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19059
  have eq19063 : x = (M.op y y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq1160 x
       grind)
    | (have r₁ := eq19058
       have r₂ := eq1160 x
       grind)
    | exact resolve eq19058 eq1160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19058
  have eq19066 : x = (k x x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq13 x x
       grind)
    | (have r₁ := eq19055
       have r₂ := eq13 x x
       grind)
    | (have r₁ := eq19055
       have r₂ := eq13 y x
       grind)
    | exact resolve eq19055 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19055
  have eq19070 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x x) ∨ x = (M.op y y) ∨ x = (k x x) := by
    first
    | exact superpose eq19062 eq5190
    | exact resolve eq5190 eq19062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5190 eq19062
  have eq19082 : x = (M.op y y) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have j1 := eq1160 x
       grind)
    | (have r₁ := eq19070
       have r₂ := eq1160 x
       grind)
    | exact resolve eq19070 eq1160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1160 eq19070
  have eq19110 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq219 y y
       have i₂ := eq19063
       grind)
    | exact superpose eq19063 eq219
    | exact resolve eq219 eq19063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19063
  have eq19113 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19110
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq19110
    | exact resolve eq19110 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19110
  have eq19151 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1247 x
       have i₂ := eq19066
       grind)
    | exact superpose eq19066 eq1247
    | (have j0 := eq1247 x
       grind)
    | exact resolve eq1247 eq19066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1247 eq19066
  have eq19159 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq19151
  have eq19160 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq19159
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq19159
    | exact resolve eq19159 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19159
  have eq19190 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq219 y y
       have i₂ := eq19082
       grind)
    | exact superpose eq19082 eq219
    | exact resolve eq219 eq19082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19082
  have eq19193 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq19190
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq19190
    | exact resolve eq19190 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19190
  have eq19274 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19113 eq17870
    | exact resolve eq17870 eq19113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19113
  have eq19295 : x = (M.op x x) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq19274
    | exact resolve eq19274 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19274
  have eq19321 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op x X1) (M.op x X1))) = (M.op (M.op X2 x) X1) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq179 X2 x X0 X1
       have i₂ := eq19295
       grind)
    | exact superpose eq19295 eq179
    | exact resolve eq179 eq19295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19327 : ∀ X0 : G, (M.op x x) = (M.op X0 x) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16 X0 x x
       have i₂ := eq19295
       grind)
    | exact superpose eq19295 eq16
    | exact resolve eq16 eq19295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19336 : (M.op x x) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq219 x x
       have i₂ := eq19295
       grind)
    | exact superpose eq19295 eq219
    | exact resolve eq219 eq19295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19339 : x = (M.op (M.op x y) y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19295 eq19336
    | exact resolve eq19336 eq19295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19336
  have eq19343 : ∀ X0 : G, x = (M.op X0 x) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq19295 eq19327
    | exact resolve eq19327 eq19295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19295 eq19327
  have eq19346 : ∀ X1 X2 : G, (M.op (M.op x y) y) = (M.op (M.op X2 x) X1) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    intro X1 X2
    first
    | (have i₁ := eq19321 x X1 X2
       have i₂ := eq196 x (M.op x X1)
       grind)
    | exact superpose eq196 eq19321
    | exact resolve eq19321 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19321
  have eq19353 : ∀ X1 X2 : G, x = (M.op (M.op X2 x) X1) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    intro X1 X2
    first
    | exact superpose eq19339 eq19346
    | exact resolve eq19346 eq19339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19339 eq19346
  have eq19356 : ∀ X1 : G, x = (M.op x X1) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    intro X1
    first
    | exact superpose eq19343 eq19353
    | exact resolve eq19353 eq19343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19343 eq19353
  have eq19859 : x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq19356 y
       grind)
    | exact superpose eq19356 eq18
    | (have j1 := eq19356 y
       grind)
    | exact resolve eq18 eq19356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19356
  have eq19905 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq19859
  have eq21628 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (σ x) X1) (M.op (σ x) X1))) = (M.op (M.op X2 (σ x)) X1) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    intro X0 X1 X2
    first
    | exact superpose eq19160 eq179
    | exact resolve eq179 eq19160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq21634 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op X0 (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq19160 eq16
    | exact resolve eq16 eq19160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21643 : (M.op (M.op x y) y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq19160 eq219
    | exact resolve eq219 eq19160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21646 : (σ x) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq19160 eq21643
    | exact resolve eq21643 eq19160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21643
  have eq21650 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq19160 eq21634
    | exact resolve eq21634 eq19160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19160 eq21634
  have eq21653 : ∀ X1 X2 : G, (M.op (M.op x y) y) = (M.op (M.op X2 (σ x)) X1) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    intro X1 X2
    first
    | (have i₁ := eq21628 x X1 X2
       have i₂ := eq196 x (M.op sF2 X1)
       grind)
    | exact superpose eq196 eq21628
    | exact resolve eq21628 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196 eq21628
  have eq21667 : ∀ X1 X2 : G, (σ x) = (M.op (M.op X2 (σ x)) X1) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    intro X1 X2
    first
    | exact superpose eq21646 eq21653
    | exact resolve eq21653 eq21646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21646 eq21653
  have eq21672 : ∀ X1 : G, (σ x) = (M.op (σ x) X1) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    intro X1
    first
    | exact superpose eq21650 eq21667
    | exact resolve eq21667 eq21650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21650 eq21667
  have eq21728 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq19193 eq17870
    | exact resolve eq17870 eq19193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19193
  have eq21753 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq21728
    | exact resolve eq21728 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21728
  have eq21760 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq19905 eq21753
    | exact resolve eq21753 eq19905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21753
  have eq21790 : (M.op (M.op x y) y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq21760 eq219
    | exact resolve eq219 eq21760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21795 : (M.op x y) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq21760 eq21790
    | exact resolve eq21790 eq21760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21760 eq21790
  have eq21858 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq21795 eq17870
    | exact resolve eq17870 eq21795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17870 eq21795
  have eq21882 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq21858
    | exact resolve eq21858 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21858
  have eq21883 : (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq21882
  have eq21941 : (M.op x y) ≠ (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq21883
  have eq25704 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21672 eq26
    | (have j1 := eq21672 (σ y)
       grind)
    | exact resolve eq26 eq21672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25841 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq187
       have i₂ := eq25704
       grind)
    | exact superpose eq25704 eq187
    | exact resolve eq187 eq25704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq25865 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq219 y y
       have i₂ := eq25704
       grind)
    | exact superpose eq25704 eq219
    | exact resolve eq219 eq25704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25704
  have eq25868 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq25865
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq25865
    | exact resolve eq25865 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25865
  have eq25885 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq25841
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq25841
    | exact resolve eq25841 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25841
  have eq26148 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq25885 eq1154
    | exact resolve eq1154 eq25885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1154 eq25885
  have eq26153 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq26148
  have eq74162 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26153 eq219
    | exact resolve eq219 eq26153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26153
  have eq74193 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq74162
    | exact resolve eq74162 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74162
  have eq74231 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq25868 eq74193
    | exact resolve eq74193 eq25868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74193
  have eq74352 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op X0 (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq74231 eq16
    | exact resolve eq16 eq74231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74361 : (M.op (M.op x y) y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq74231 eq219
    | exact resolve eq219 eq74231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74406 : (σ x) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq74231 eq74361
    | exact resolve eq74361 eq74231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74361
  have eq74410 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq74231 eq74352
    | exact resolve eq74352 eq74231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74231 eq74352
  have eq74436 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq25868 eq74406
    | exact resolve eq74406 eq25868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25868 eq74406
  have eq74467 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq74436 eq206
    | exact resolve eq206 eq74436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq74471 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq74467
    | exact resolve eq74467 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74467
  have eq74475 : (σ x) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq74436 eq74471
    | exact resolve eq74471 eq74436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74436 eq74471
  have eq74677 : (σ x) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq74410 eq219
    | exact resolve eq219 eq74410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74410
  have eq74770 : (σ x) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq74475 eq74677
    | exact resolve eq74677 eq74475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74475 eq74677
  have eq74771 : (σ x) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq74770
  have eq74945 : (σ x) = (τ (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq74771 eq17880
    | exact resolve eq17880 eq74771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17880
  have eq75083 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq74945
    | exact resolve eq74945 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq74945
  have eq75114 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq75083 eq27
    | exact resolve eq27 eq75083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75083
  have eq75124 : x = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq75114
       have r₂ := eq19905
       grind)
    | exact resolve eq75114 eq19905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75114
  have eq75126 : (M.op x y) = (M.op (σ x) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq75124
       grind)
    | exact superpose eq75124 eq18
    | exact resolve eq18 eq75124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75239 : (M.op x y) ≠ (σ x) ∨ x = (M.op x y) := by grind
  have eq75626 : (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq75126 eq21672
    | exact resolve eq21672 eq75126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21672
  have eq75645 : (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq75626
  have eq75657 : x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq75645
       have r₂ := eq75239
       grind)
    | exact resolve eq75645 eq75239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75645
  have eq75671 : (σ x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq75124 eq75657
    | exact resolve eq75657 eq75124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75124 eq75657
  have eq75797 : (M.op (M.op x y) y) = (M.op (σ x) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq219 y y
       have i₂ := eq75671
       grind)
    | exact superpose eq75671 eq219
    | exact resolve eq219 eq75671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219 eq75671
  have eq75831 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq75126 eq75797
    | exact resolve eq75797 eq75126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75126 eq75797
  have eq75961 : (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq75831 eq74771
    | exact resolve eq74771 eq75831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74771 eq75831
  have eq75976 : (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq75961
  have eq76011 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq75976
       have r₂ := eq75239
       grind)
    | exact resolve eq75976 eq75239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75239 eq75976
  have eq76058 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq76011 eq27
    | exact resolve eq27 eq76011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76011
  have eq76068 : x = (M.op x y) := by
    first
    | (have r₁ := eq76058
       have r₂ := eq19905
       grind)
    | exact resolve eq76058 eq19905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19905 eq76058
  have eq76073 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq76068
       grind)
    | exact superpose eq76068 eq18
    | exact resolve eq18 eq76068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq76074 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq76068
       grind)
    | exact superpose eq76068 eq22
    | exact resolve eq22 eq76068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq76068
  have eq76198 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq76074 eq20
    | exact resolve eq20 eq76074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76074
  have eq77268 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq76073 eq222
    | exact resolve eq222 eq76073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq77278 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq76073 eq17716
    | exact resolve eq17716 eq76073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17716
  have eq77281 : (M.op x y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq76073 eq17852
    | exact resolve eq17852 eq76073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17852 eq76073
  have eq77342 : (M.op x y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq77281
    | exact resolve eq77281 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77281
  have eq77345 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq77278
    | exact resolve eq77278 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq77278
  have eq77352 : (M.op x y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq76198 eq77342
    | exact resolve eq77342 eq76198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77342
  have eq77355 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq76198 eq77345
    | exact resolve eq77345 eq76198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76198 eq77345
  have eq77360 : (M.op x y) = (σ x) := by
    first
    | exact superpose eq77352 eq77355
    | exact resolve eq77355 eq77352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77352 eq77355
  have eq77361 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq77360 eq26
    | exact resolve eq26 eq77360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq77458 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq77360 eq21941
    | (have r₁ := eq21941
       have r₂ := eq77360
       grind)
    | exact resolve eq21941 eq77360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21941 eq77360
  have eq77574 : (M.op x y) = (σ (M.op x y)) := by grind
  clear eq77458
  have eq77657 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq77268 eq77361
    | exact resolve eq77361 eq77268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77268 eq77361
  have eq77901 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq77657 eq27
    | exact resolve eq27 eq77657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq77657
  have eq77911 : False := by grind
  exact eq77911

/-- `Equation4517`: `x ◇ (y ◇ z) = (x ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,Y) else if m(Y,X) = m(Y,Y) then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyx_pyy_pyy_y_pyx_Equation4517 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law4517 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4517.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b a ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X2) X3) := by
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
  have eq38 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq41 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq20
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
  clear eq43
  have eq50 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 (M.op X4 X1)) X5) = (M.op X3 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq14 X3 X0 (M.op X4 X1) X5
       have i₂ := eq14 X0 X4 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 X4) X5) = (M.op X3 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq14 X3 (M.op X0 X2) X4 X5
       have i₂ := eq14 X0 X1 X2 X4
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X4) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq14 X0 x X1 X4
       have i₂ := eq14 X0 x X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op x (M.op X0 y)) = (M.op (M.op x y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 x X0 y X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x X0 y X1
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 (σ y))) = (M.op (M.op (σ x) (σ y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) X0 (σ y) X1
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 X1 X2 x
       have i₂ := eq14 X0 X3 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) ≠ (M.op X0 X2) ∨ (k (M.op X0 X2) X3) = (M.op X3 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 (M.op X0 X2) X3
       have i₂ := eq14 X0 X1 X2 X3
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 (M.op X0 X2) X3
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  clear eq36
  have eq86 : (M.op x y) ≠ (M.op x x) ∨ y = (M.op y x) ∨ x = (k y x) := by
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
  have eq87 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 : G, (σ (k X0 (k y x))) = (k (σ X0) (k (σ y) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq10 X0 (k y x)
       have i₂ := eq79
       grind)
    | exact superpose eq79 eq10
    | exact resolve eq10 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq79
       grind)
    | exact superpose eq79 eq16
    | exact resolve eq16 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq79
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq79
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq79 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq112
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq112
    | exact resolve eq112 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq121 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq120
    | exact resolve eq120 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq122 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq121
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq121
    | exact resolve eq121 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq175 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq11 (σ X0) sF2
       grind)
    | exact superpose eq11 eq39
    | (have j1 := eq11 (σ X0) (σ x)
       grind)
    | exact resolve eq39 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (M.op (σ (M.op x y)) (σ X0)) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq11 (σ X0) sF1
       grind)
    | exact superpose eq11 eq41
    | (have j1 := eq11 (σ X0) (σ (M.op x y))
       grind)
    | exact resolve eq41 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq213 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq56 x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq56
    | (have j0 := eq56 x X0
       grind)
    | exact resolve eq56 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq245 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (σ x) (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq213 eq57
    | exact resolve eq57 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq246 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq57
    | (have j0 := eq57 (σ x) X0
       grind)
    | exact resolve eq57 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq281 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq288 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq57 eq246
    | exact resolve eq246 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq325 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq16
    | exact resolve eq16 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq329 : ∀ X0 X1 : G, (σ (k (k X0 (τ X1)) x)) = (k (k (σ X0) X1) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq39 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq39
    | exact resolve eq39 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq330 : ∀ X0 X1 : G, (σ (k (k X0 (τ X1)) y)) = (k (k (σ X0) X1) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq40 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq40
    | exact resolve eq40 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq331 : ∀ X0 X1 : G, (σ (k (k X0 (τ X1)) (M.op x y))) = (k (k (σ X0) X1) (σ (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq41 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq41
    | exact resolve eq41 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq361 : (τ (σ x)) = (k x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq49
       have i₂ := eq88 sF2
       grind)
    | exact superpose eq88 eq49
    | (have j1 := eq88 (σ x)
       grind)
    | exact resolve eq49 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq364 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | exact superpose eq28 eq361
    | exact resolve eq361 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361
  have eq440 : ∀ X0 X1 X2 X3 : G, (M.op (M.op x y) X3) = (M.op x (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq56 (M.op X0 X1) X3
       have i₂ := eq52 X0 X1 y X2
       grind)
    | (have i₁ := eq56 (M.op X0 X1) X3
       have i₂ := eq52 X0 X1 X2 y
       grind)
    | exact superpose eq52 eq56
    | exact resolve eq56 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq443 : ∀ X0 X1 X2 : G, (M.op x (M.op x y)) = (M.op x (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq213 eq440
    | exact resolve eq440 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440
  have eq452 : (M.op (σ x) (M.op x (M.op x y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq246 eq245
    | exact resolve eq245 eq246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245
  have eq476 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op X1 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq58 X0 x y X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq58
    | (have j0 := eq58 X0 x y X1
       grind)
    | exact resolve eq58 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq482 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op X1 (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq58
    | (have j0 := eq58 X0 (σ x) (σ y) X1
       grind)
    | exact resolve eq58 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq520 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (σ x) (M.op X0 (σ y)))) = (M.op X1 (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq57 eq58
    | exact resolve eq58 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq540 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) ≠ X0 ∨ (k X0 (M.op X3 X2)) = (M.op (M.op X3 X2) (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X0 (M.op X3 X2)
       have i₂ := eq58 X0 X3 X2 X1
       grind)
    | (have i₁ := eq13 X0 (M.op X3 X2)
       have i₂ := eq58 X0 X1 X2 X3
       grind)
    | exact superpose eq58 eq13
    | (have j0 := eq13 X0 (M.op X1 X2)
       grind)
    | exact resolve eq13 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq579 : ∀ X1 X2 X3 : G, (M.op X1 (M.op X2 X3)) = (M.op X1 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X1 X2 X3
    first
    | exact superpose eq288 eq520
    | (have j0 := eq520 (σ x) X1 X2 X3
       grind)
    | exact resolve eq520 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520
  have eq591 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq213 eq476
    | exact resolve eq476 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq595 : ∀ X0 X1 : G, (M.op (M.op X0 y) X1) = (M.op X0 (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq476 X0 x
       have i₂ := eq14 X0 x y X1
       grind)
    | exact superpose eq14 eq476
    | (have j1 := eq14 X0 x y X1
       grind)
    | exact resolve eq476 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq608 : ∀ X0 X1 : G, (M.op (M.op X0 y) X1) ≠ (M.op (M.op X0 y) (M.op x y)) ∨ (M.op X1 (M.op X0 y)) = X1 ∨ (M.op X0 y) = (k X1 (M.op X0 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 y)
       have i₂ := eq476 (M.op X0 y) X0
       grind)
    | (have i₁ := eq12 X0 (M.op x y)
       have i₂ := eq476 (M.op x y) X1
       grind)
    | exact superpose eq476 eq12
    | (have j0 := eq12 X1 (M.op X0 y)
       grind)
    | (have r₁ := eq12 (M.op X1 y) (M.op x y)
       have r₂ := eq476 (M.op x y) X1
       grind)
    | (have r₁ := eq12 (M.op x y) (M.op X1 y)
       have r₂ := eq476 (M.op X1 y) X1
       grind)
    | exact resolve eq12 eq476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq630 : ∀ X0 X1 : G, (M.op X1 (M.op X0 y)) = X1 ∨ (M.op X0 y) = (k X1 (M.op X0 y)) := by
    intro X0 X1
    first
    | (have j0 := eq608 X0 X1
       grind)
    | (have r₁ := eq608 X0 x
       have r₂ := eq52 X0 y x (M.op x y)
       grind)
    | (have r₁ := eq608 X0 x
       have r₂ := eq52 X0 y (M.op x y) x
       grind)
    | exact resolve eq608 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608
  have eq631 : ∀ X0 X1 : G, (M.op X0 y) = (k X1 (M.op X0 y)) ∨ (M.op X1 (M.op x y)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq630 X0 X1
       have i₂ := eq476 X1 X0
       grind)
    | (have i₁ := eq630 x X0
       have i₂ := eq476 X0 X1
       grind)
    | exact superpose eq476 eq630
    | (have j0 := eq630 x X1
       grind)
    | exact resolve eq630 eq476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq630
  have eq636 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq213 eq482
    | exact resolve eq482 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482
  have eq806 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) X1) = (M.op (σ x) (M.op X2 (σ y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57 X0 (M.op X0 (M.op X1 X2))
       have i₂ := eq51 X0 X1 X2 sF4 x x
       grind)
    | exact superpose eq51 eq57
    | exact resolve eq57 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq807 : ∀ X0 X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq288 eq806
    | (have j0 := eq806 X0 X1 (σ x)
       grind)
    | exact resolve eq806 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806
  have eq831 : ∀ X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) X1) := by
    intro X1
    first
    | exact superpose eq246 eq807
    | exact resolve eq807 eq246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246 eq807
  have eq840 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq831 x
       have i₂ := eq14 sF2 x sF4 x
       grind)
    | exact superpose eq14 eq831
    | exact resolve eq831 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831
  have eq1440 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op X1 (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq591 X0
       have i₂ := eq58 X0 x sF0 x
       grind)
    | (have i₁ := eq591 X0
       have i₂ := eq58 X0 X1 sF0 x
       grind)
    | exact superpose eq58 eq591
    | exact resolve eq591 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1452 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq452 eq591
    | exact resolve eq591 eq452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452
  have eq2253 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op x y)) = (M.op (M.op (M.op X0 y) (M.op X1 X2)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq50 x X2 x (M.op X0 y) X1 X3
       have i₂ := eq595 X0 (M.op (M.op x X2) x)
       grind)
    | exact superpose eq595 eq50
    | exact resolve eq50 eq595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq2264 : ∀ X0 X3 : G, (M.op X0 (M.op x y)) = (M.op (M.op X0 (M.op x y)) X3) := by
    intro X0 X3
    first
    | (have i₁ := eq2253 X0 x x X3
       have i₂ := eq595 X0 (M.op x x)
       grind)
    | exact superpose eq595 eq2253
    | exact resolve eq2253 eq595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595 eq2253
  have eq2293 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq591 eq636
    | exact resolve eq636 eq591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636
  have eq2412 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op X0 (M.op x y))) := by
    intro X0
    first
    | exact superpose eq2293 eq840
    | exact resolve eq840 eq2293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq840 eq2293
  have eq2413 : ∀ X0 : G, (M.op (σ x) (M.op x y)) = (M.op (σ x) (M.op X0 (M.op x y))) := by
    intro X0
    first
    | exact superpose eq1452 eq2412
    | exact resolve eq2412 eq1452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2412
  have eq2445 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 y)) ≠ (M.op X1 (M.op (M.op x y) X0)) ∨ (M.op X3 X3) = (k (M.op X1 (M.op X2 y)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq70 X1 x (M.op X2 y) X3
       have i₂ := eq56 X2 X0
       grind)
    | exact superpose eq56 eq70
    | (have j0 := eq70 X1 X1 (M.op X2 y) X3
       grind)
    | exact resolve eq70 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2485 : ∀ X0 X2 X3 : G, (M.op x (M.op X0 y)) ≠ (M.op (M.op x y) X2) ∨ (M.op X3 X3) = (k (M.op (M.op x y) X2) X3) := by
    intro X0 X2 X3
    first
    | exact superpose eq56 eq70
    | (have j0 := eq70 (M.op x y) x X2 X3
       grind)
    | exact resolve eq70 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq2503 : ∀ X2 X3 : G, (M.op X3 X3) = (k (M.op (M.op x y) X2) X3) := by
    intro X2 X3
    first
    | (have j0 := eq2485 x X2 X3
       grind)
    | (have r₁ := eq2485 x x X3
       have r₂ := eq56 x x
       grind)
    | exact resolve eq2485 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq2485
  have eq2533 : ∀ X1 X2 X3 : G, (M.op X1 (M.op X2 y)) ≠ (M.op X1 (M.op x (M.op x y))) ∨ (M.op X3 X3) = (k (M.op X1 (M.op X2 y)) X3) := by
    intro X1 X2 X3
    first
    | exact superpose eq213 eq2445
    | (have j0 := eq2445 x X1 X2 X3
       grind)
    | exact resolve eq2445 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2445
  have eq2545 : ∀ X3 : G, (M.op X3 X3) = (k (M.op x (M.op x y)) X3) := by
    intro X3
    first
    | exact superpose eq213 eq2503
    | exact resolve eq2503 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2503
  have eq2560 : ∀ X1 X2 X3 : G, (M.op X1 (M.op X2 y)) ≠ (M.op X1 (M.op x y)) ∨ (M.op X3 X3) = (k (M.op X1 (M.op X2 y)) X3) := by
    intro X1 X2 X3
    first
    | exact superpose eq591 eq2533
    | (have j0 := eq2533 X1 X2 X3
       grind)
    | (have r₁ := eq2533 x x X3
       have r₂ := eq591 x
       grind)
    | exact resolve eq2533 eq591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591 eq2533
  have eq2576 : ∀ X1 X2 X3 : G, (M.op X3 X3) = (k (M.op X1 (M.op X2 y)) X3) := by
    intro X1 X2 X3
    first
    | (have j0 := eq2560 X1 X2 X3
       grind)
    | (have r₁ := eq2560 x x X3
       have r₂ := eq476 x x
       grind)
    | (have r₁ := eq2560 x X1 X3
       have r₂ := eq476 x X1
       grind)
    | exact resolve eq2560 eq476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2560
  have eq2582 : ∀ X1 X3 : G, (M.op X3 X3) = (k (M.op X1 (M.op x y)) X3) := by
    intro X1 X3
    first
    | (have i₁ := eq2576 X1 x X3
       have i₂ := eq476 X1 x
       grind)
    | (have i₁ := eq2576 x x X3
       have i₂ := eq476 x X1
       grind)
    | exact superpose eq476 eq2576
    | (have j0 := eq2576 X1 x X3
       grind)
    | exact resolve eq2576 eq476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476 eq2576
  have eq2661 : ∀ X0 : G, (k (σ (M.op x (M.op x y))) X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | exact superpose eq2545 eq38
    | exact resolve eq38 eq2545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq2765 : ∀ X0 X1 X2 : G, (k (M.op X0 (M.op x y)) X1) = (k (M.op X2 (M.op x y)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2582 X2 X1
       have i₂ := eq2582 X0 X1
       grind)
    | exact superpose eq2582 eq2582
    | exact resolve eq2582 eq2582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3669 : ∀ X0 : G, (k (τ (M.op x (M.op x y))) X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | exact superpose eq2545 eq281
    | exact resolve eq281 eq2545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3672 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op X1 (M.op x y))) X0) := by
    intro X0 X1
    first
    | exact superpose eq2582 eq281
    | exact resolve eq281 eq2582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq4254 : ∀ X0 X1 : G, (M.op x (M.op x y)) = (M.op x (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq443 x x X1
       have i₂ := eq58 x (M.op x x) X1 X0
       grind)
    | (have i₁ := eq443 x x X1
       have i₂ := eq58 x X0 X1 (M.op x x)
       grind)
    | exact superpose eq58 eq443
    | exact resolve eq443 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq4256 : ∀ X0 X1 : G, (M.op x (M.op x y)) = (M.op (M.op x X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq443 x x X0
       have i₂ := eq14 x (M.op x x) X0 X1
       grind)
    | exact superpose eq14 eq443
    | exact resolve eq443 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4264 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X0 (M.op x (M.op x y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 x (M.op x x) x X0 X1 X2
       have i₂ := eq443 x x x
       grind)
    | exact superpose eq443 eq51
    | (have j0 := eq51 x x y X0 X1 X2
       grind)
    | exact resolve eq51 eq443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443
  have eq4309 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X0 (M.op x y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq1440 eq4264
    | exact resolve eq4264 eq1440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4264
  have eq4623 : ∀ X0 X1 X2 : G, (M.op X1 (M.op x y)) = (M.op (k (M.op X0 (M.op x y)) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4309 X1 X1 X2
       have i₂ := eq2582 X0 X1
       grind)
    | exact superpose eq2582 eq4309
    | exact resolve eq4309 eq2582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4853 : ∀ X1 X2 X3 : G, (M.op X1 (M.op X2 X3)) = (M.op X1 (M.op (σ x) (M.op x y))) := by
    intro X1 X2 X3
    first
    | exact superpose eq1452 eq579
    | exact resolve eq579 eq1452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579
  have eq4854 : ∀ X1 X2 X3 : G, (M.op X1 (M.op x y)) = (M.op X1 (M.op X2 X3)) := by
    intro X1 X2 X3
    first
    | exact superpose eq1440 eq4853
    | exact resolve eq4853 eq1440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1440 eq4853
  have eq4869 : ∀ X0 X1 X2 : G, (M.op X2 (M.op x y)) = (M.op X2 (k (M.op X0 (M.op x y)) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4854 X2 X1 X1
       have i₂ := eq2582 X0 X1
       grind)
    | exact superpose eq2582 eq4854
    | exact resolve eq4854 eq2582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4958 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op x y)) = (k (M.op X2 (M.op x y)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2582 X2 (M.op X0 X1)
       have i₂ := eq4854 (M.op X0 X1) X0 X1
       grind)
    | (have i₁ := eq2582 X1 (M.op x y)
       have i₂ := eq4854 (M.op x y) X2 x
       grind)
    | exact superpose eq4854 eq2582
    | exact resolve eq2582 eq4854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5039 : ∀ X0 X1 X2 : G, (M.op X0 (M.op x y)) = (k (M.op X2 (M.op x y)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4958 X0 X1 X2
       have i₂ := eq4309 X0 X1 sF0
       grind)
    | exact superpose eq4309 eq4958
    | exact resolve eq4958 eq4309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4958
  have eq5190 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | exact superpose eq364 eq13
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq364
       grind)
    | exact resolve eq13 eq364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364
  have eq5213 : (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) := by grind
  clear eq5190
  have eq5270 : (τ (σ x)) = (k x x) ∨ x = (k x x) := by
    first
    | exact superpose eq5213 eq49
    | exact resolve eq49 eq5213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq5213
  have eq5271 : x = (k x x) ∨ x = (k x x) := by
    first
    | exact superpose eq28 eq5270
    | exact resolve eq5270 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5270
  have eq5272 : x = (k x x) := by grind
  clear eq5271
  have eq5974 : ∀ X0 X1 X2 : G, (M.op X1 (M.op x y)) = (k (M.op X2 (M.op x y)) (k (M.op X0 (M.op x y)) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5039 X1 X1 X2
       have i₂ := eq2582 X0 X1
       grind)
    | exact superpose eq2582 eq5039
    | exact resolve eq5039 eq2582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7504 : ∀ X0 X1 : G, (σ (k (M.op (τ X0) (τ X0)) x)) = (k (k (σ (M.op X1 (M.op x y))) X0) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq2582 eq329
    | exact resolve eq329 eq2582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12199 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ (M.op x (M.op x y))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq2661 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq2661
    | exact resolve eq2661 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12359 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (k (M.op x (M.op x y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq12199 x
       have i₂ := eq10 (M.op x sF0) x
       grind)
    | exact superpose eq10 eq12199
    | exact resolve eq12199 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12199
  have eq12406 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (σ (k (M.op X0 (M.op x y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq2765 eq12359
    | exact resolve eq12359 eq2765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2765
  have eq15102 : ∀ X0 X1 : G, (k (k (σ (τ (M.op X1 (M.op x y)))) X0) (σ x)) = (σ (k (τ (M.op (σ (τ X0)) (σ (τ X0)))) x)) := by
    intro X0 X1
    first
    | exact superpose eq3672 eq329
    | exact resolve eq329 eq3672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329
  have eq15103 : ∀ X0 X1 : G, (k (k (σ (τ (M.op X1 (M.op x y)))) X0) (σ y)) = (σ (k (τ (M.op (σ (τ X0)) (σ (τ X0)))) y)) := by
    intro X0 X1
    first
    | exact superpose eq3672 eq330
    | exact resolve eq330 eq3672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330
  have eq15104 : ∀ X0 X1 : G, (k (k (σ (τ (M.op X1 (M.op x y)))) X0) (σ (M.op x y))) = (σ (k (τ (M.op (σ (τ X0)) (σ (τ X0)))) (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq3672 eq331
    | exact resolve eq331 eq3672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331
  have eq15132 : ∀ X0 X1 : G, (k (k (σ (τ (M.op X1 (M.op x y)))) X0) (σ (M.op x y))) = (k (M.op (σ (τ X0)) (σ (τ X0))) (σ (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq15104 X0 X1
       have i₂ := eq34 (M.op (σ (τ X0)) (σ (τ X0))) sF0
       grind)
    | exact superpose eq34 eq15104
    | exact resolve eq15104 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15104
  have eq15133 : ∀ X0 X1 : G, (k (k (σ (τ (M.op X1 (M.op x y)))) X0) (σ y)) = (k (M.op (σ (τ X0)) (σ (τ X0))) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq15103 X0 X1
       have i₂ := eq34 (M.op (σ (τ X0)) (σ (τ X0))) y
       grind)
    | exact superpose eq34 eq15103
    | exact resolve eq15103 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15103
  have eq15134 : ∀ X0 X1 : G, (k (k (σ (τ (M.op X1 (M.op x y)))) X0) (σ x)) = (k (M.op (σ (τ X0)) (σ (τ X0))) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq15102 X0 X1
       have i₂ := eq34 (M.op (σ (τ X0)) (σ (τ X0))) x
       grind)
    | exact superpose eq34 eq15102
    | exact resolve eq15102 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15102
  have eq15261 : ∀ X0 X1 : G, (k (k (σ (τ (M.op X1 (M.op x y)))) X0) (σ (M.op x y))) = (k (M.op (σ (τ X0)) (σ (τ X0))) (σ (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq20 eq15132
    | (have j0 := eq15132 X0 X1
       grind)
    | exact resolve eq15132 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15132
  have eq15262 : ∀ X0 X1 : G, (k (k (σ (τ (M.op X1 (M.op x y)))) X0) (σ y)) = (k (M.op (σ (τ X0)) (σ (τ X0))) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq15133 X0 X1
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15133
    | (have j0 := eq15133 X0 X1
       grind)
    | exact resolve eq15133 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15133
  have eq15263 : ∀ X0 X1 : G, (k (k (σ (τ (M.op X1 (M.op x y)))) X0) (σ x)) = (k (M.op (σ (τ X0)) (σ (τ X0))) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq15134 X0 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15134
    | (have j0 := eq15134 X0 X1
       grind)
    | exact resolve eq15134 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15134
  have eq15296 : ∀ X0 X1 : G, (k (M.op X0 X0) (σ (M.op x y))) = (k (k (σ (τ (M.op X1 (M.op x y)))) X0) (σ (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq15261 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq15261
    | exact resolve eq15261 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15261
  have eq15297 : ∀ X0 X1 : G, (k (M.op X0 X0) (σ y)) = (k (k (σ (τ (M.op X1 (M.op x y)))) X0) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq15262 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq15262
    | exact resolve eq15262 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15262
  have eq15298 : ∀ X0 X1 : G, (k (M.op X0 X0) (σ x)) = (k (k (σ (τ (M.op X1 (M.op x y)))) X0) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq15263 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq15263
    | exact resolve eq15263 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15263
  have eq15312 : ∀ X0 X1 : G, (k (M.op X0 X0) (σ (M.op x y))) = (k (k (M.op X1 (M.op x y)) X0) (σ (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq15296 X0 X1
       have i₂ := eq15 (M.op X1 sF0)
       grind)
    | exact superpose eq15 eq15296
    | exact resolve eq15296 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15296
  have eq15313 : ∀ X0 X1 : G, (k (M.op X0 X0) (σ y)) = (k (k (M.op X1 (M.op x y)) X0) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq15297 X0 X1
       have i₂ := eq15 (M.op X1 sF0)
       grind)
    | exact superpose eq15 eq15297
    | exact resolve eq15297 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15297
  have eq15314 : ∀ X0 X1 : G, (k (M.op X0 X0) (σ x)) = (k (k (M.op X1 (M.op x y)) X0) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq15298 X0 X1
       have i₂ := eq15 (M.op X1 sF0)
       grind)
    | exact superpose eq15 eq15298
    | exact resolve eq15298 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15298
  have eq39976 : ∀ X0 X2 X3 : G, (M.op X0 (M.op x y)) ≠ X0 ∨ (k X0 (M.op X3 X2)) = (M.op (M.op X3 X2) (M.op X3 X2)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq540 X0 x X2 X3
       have i₂ := eq4854 X0 x X2
       grind)
    | (have i₁ := eq540 x x y X3
       have i₂ := eq4854 x X2 X3
       grind)
    | exact superpose eq4854 eq540
    | (have j0 := eq540 X0 x y X3
       grind)
    | exact resolve eq540 eq4854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540
  have eq39977 : ∀ X0 X2 X3 : G, (M.op X0 (M.op x y)) ≠ X0 ∨ (k X0 (M.op X3 X2)) = (M.op X3 (M.op x y)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq39976 X0 X2 X3
       have i₂ := eq4309 X3 X2 (M.op X3 X2)
       grind)
    | exact superpose eq4309 eq39976
    | (have j0 := eq39976 X0 X2 X3
       grind)
    | (have r₁ := eq39976 (M.op X0 (M.op x y)) X2 X3
       have r₂ := eq4309 X0 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq39976 eq4309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39976
  have eq50001 : ∀ X0 X1 X2 X3 X4 : G, (M.op (σ x) (M.op X2 (M.op X3 X4))) = (M.op (σ (k X0 x)) X1) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ x)) := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq175 eq51
    | (have j1 := eq175 X0
       grind)
    | exact resolve eq51 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq50019 : ∀ X0 X1 : G, (M.op X1 (M.op x y)) = (M.op X1 (σ (k X0 x))) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq175 eq4854
    | (have j1 := eq175 X0
       grind)
    | exact resolve eq4854 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq50041 : ∀ X0 X1 : G, (M.op (σ x) (M.op x y)) = (M.op (σ (k X0 x)) X1) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq50001 X0 X1 x x x
       have i₂ := eq4854 sF2 x (M.op x x)
       grind)
    | exact superpose eq4854 eq50001
    | (have j0 := eq50001 X0 X1 x x x
       grind)
    | exact resolve eq50001 eq4854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50001
  have eq59267 : ∀ X0 X2 : G, (M.op X0 (M.op x y)) = (k X2 (M.op X0 (M.op x y))) ∨ (M.op X2 (M.op x y)) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq631 (M.op X0 x) x
       have i₂ := eq4309 X0 x y
       grind)
    | exact superpose eq4309 eq631
    | (have j0 := eq631 X0 X2
       grind)
    | exact resolve eq631 eq4309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59283 : ∀ X0 : G, (M.op x (M.op x y)) = (k X0 (M.op x (M.op x y))) ∨ (M.op X0 (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq213 eq631
    | (have j0 := eq631 X0 X0
       grind)
    | exact resolve eq631 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631
  have eq59405 : ∀ X0 : G, (M.op x (M.op x y)) = (k X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq59283 X0
       have j1 := eq39977 X0 (M.op x y) x
       grind)
    | (have r₁ := eq59283 X0
       have r₂ := eq39977 X0 x x
       grind)
    | exact resolve eq59283 eq39977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59283
  have eq59415 : ∀ X0 X2 : G, (M.op X0 (M.op x y)) = (k X2 (M.op X0 (M.op x y))) := by
    intro X0 X2
    first
    | (have j0 := eq59267 X0 X2
       have j1 := eq39977 X2 (M.op x y) X0
       grind)
    | (have r₁ := eq59267 X0 X0
       have r₂ := eq39977 X0 X2 x
       grind)
    | exact resolve eq59267 eq39977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39977 eq59267
  have eq59508 : ∀ X0 : G, (τ (M.op x (M.op x y))) = (k X0 (τ (M.op x (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq59405 eq325
    | exact resolve eq325 eq59405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59512 : ∀ X0 : G, (σ (M.op x (M.op x y))) = (k X0 (σ (M.op x (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq59405 eq34
    | exact resolve eq34 eq59405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59700 : ∀ X0 X1 : G, (τ (M.op X0 (M.op x y))) = (k X1 (τ (M.op X0 (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq59415 eq325
    | exact resolve eq325 eq59415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325 eq59415
  have eq61286 : ∀ X0 : G, (M.op (τ (M.op x (M.op x y))) (M.op x y)) = (k (M.op X0 (M.op x y)) (τ (M.op x (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq59508 eq5974
    | exact resolve eq5974 eq59508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5974
  have eq61340 : (τ (M.op x (M.op x y))) = (M.op (τ (M.op x (M.op x y))) (M.op x y)) := by
    first
    | exact superpose eq59508 eq61286
    | exact resolve eq61286 eq59508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59508 eq61286
  have eq64547 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 (σ (M.op x (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq59512 eq4869
    | exact resolve eq4869 eq59512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4869
  have eq64728 : ∀ X0 : G, (k (k (M.op X0 (M.op x y)) (σ (M.op x (M.op x y)))) (σ (M.op x y))) = (k (M.op (σ (M.op x (M.op x y))) (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq64547 eq15312
    | exact resolve eq15312 eq64547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15312
  have eq64729 : ∀ X0 : G, (k (k (M.op X0 (M.op x y)) (σ (M.op x (M.op x y)))) (σ y)) = (k (M.op (σ (M.op x (M.op x y))) (M.op x y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq64547 eq15313
    | exact resolve eq15313 eq64547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15313
  have eq64730 : ∀ X0 : G, (k (k (M.op X0 (M.op x y)) (σ (M.op x (M.op x y)))) (σ x)) = (k (M.op (σ (M.op x (M.op x y))) (M.op x y)) (σ x)) := by
    intro X0
    first
    | exact superpose eq64547 eq15314
    | exact resolve eq15314 eq64547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15314 eq64547
  have eq64894 : ∀ X0 : G, (M.op (σ x) (σ x)) = (k (k (M.op X0 (M.op x y)) (σ (M.op x (M.op x y)))) (σ x)) := by
    intro X0
    first
    | exact superpose eq2582 eq64730
    | exact resolve eq64730 eq2582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64730
  have eq64895 : ∀ X0 : G, (M.op (σ y) (σ y)) = (k (k (M.op X0 (M.op x y)) (σ (M.op x (M.op x y)))) (σ y)) := by
    intro X0
    first
    | exact superpose eq2582 eq64729
    | exact resolve eq64729 eq2582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64729
  have eq64896 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (k (M.op X0 (M.op x y)) (σ (M.op x (M.op x y)))) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq2582 eq64728
    | exact resolve eq64728 eq2582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64728
  have eq64941 : (M.op (σ x) (σ x)) = (k (σ (M.op x (M.op x y))) (σ x)) := by
    first
    | exact superpose eq59512 eq64894
    | exact resolve eq64894 eq59512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64894
  have eq64942 : (M.op (σ y) (σ y)) = (k (σ (M.op x (M.op x y))) (σ y)) := by
    first
    | exact superpose eq59512 eq64895
    | exact resolve eq64895 eq59512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64895
  have eq64943 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x (M.op x y))) (σ (M.op x y))) := by
    first
    | exact superpose eq59512 eq64896
    | exact resolve eq64896 eq59512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59512 eq64896
  have eq64962 : (M.op (σ x) (σ x)) = (σ (k (M.op x (M.op x y)) x)) := by
    first
    | exact superpose eq39 eq64941
    | exact resolve eq64941 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64941
  have eq64963 : (M.op (σ y) (σ y)) = (σ (k (M.op x (M.op x y)) y)) := by
    first
    | exact superpose eq40 eq64942
    | exact resolve eq64942 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq64942
  have eq64964 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x (M.op x y)) (M.op x y))) := by
    first
    | exact superpose eq41 eq64943
    | exact resolve eq64943 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq64943
  have eq64969 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | exact superpose eq12359 eq64962
    | exact resolve eq64962 eq12359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64962
  have eq64970 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq12359 eq64963
    | exact resolve eq64963 eq12359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64963
  have eq64971 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq12359 eq64964
    | exact resolve eq64964 eq12359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64964
  have eq64972 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op x (M.op x y))) := by
    first
    | exact superpose eq213 eq64971
    | exact resolve eq64971 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64971
  have eq64991 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq64969
       grind)
    | exact superpose eq64969 eq16
    | exact resolve eq16 eq64969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65253 : (σ (k (M.op x (M.op x y)) (M.op x y))) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) := by
    first
    | exact superpose eq64972 eq210
    | exact resolve eq210 eq64972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq65270 : ∀ X0 : G, (k (τ (M.op X0 (M.op x y))) (M.op x (M.op x y))) = (τ (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y))))) := by
    intro X0
    first
    | exact superpose eq64972 eq3672
    | exact resolve eq3672 eq64972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3672
  have eq65271 : ∀ X0 : G, (k (τ (M.op X0 (M.op x y))) (M.op x (M.op x y))) = (τ (M.op (σ (M.op x y)) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq65270 X0
       have i₂ := eq4309 sF1 sF1 (M.op sF1 sF1)
       grind)
    | exact superpose eq4309 eq65270
    | exact resolve eq65270 eq4309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65270
  have eq65283 : (M.op (σ (M.op x y)) (M.op x y)) = (σ (k (M.op x (M.op x y)) (M.op x y))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) := by
    first
    | (have i₁ := eq65253
       have i₂ := eq4854 sF1 sF1 sF1
       grind)
    | exact superpose eq4854 eq65253
    | exact resolve eq65253 eq4854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65253
  have eq65313 : (M.op x (M.op x y)) = (τ (M.op (σ (M.op x y)) (M.op x y))) := by
    first
    | exact superpose eq59405 eq65271
    | exact resolve eq65271 eq59405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59405 eq65271
  have eq65323 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (M.op x y)) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) := by
    first
    | exact superpose eq12359 eq65283
    | exact resolve eq65283 eq12359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12359 eq65283
  have eq65350 : (σ (M.op x (M.op x y))) = (M.op (σ (M.op x y)) (M.op x y)) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) := by
    first
    | exact superpose eq213 eq65323
    | exact resolve eq65323 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65323
  have eq65361 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (M.op x y)) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) := by
    first
    | exact superpose eq64972 eq65350
    | exact resolve eq65350 eq64972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65350
  have eq65370 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (M.op x y)) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (M.op x y)) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) := by
    first
    | (have i₁ := eq65361
       have i₂ := eq4854 sF1 sF1 sF1
       grind)
    | exact superpose eq4854 eq65361
    | exact resolve eq65361 eq4854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4854 eq65361
  have eq65371 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (M.op x y)) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) := by grind
  clear eq65370
  have eq65377 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (M.op x y)) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (M.op x y)) := by
    first
    | (have i₁ := eq65371
       have i₂ := eq4309 sF1 sF1 sF1
       grind)
    | exact superpose eq4309 eq65371
    | exact resolve eq65371 eq4309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65371
  have eq65378 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (M.op x y)) := by grind
  clear eq65377
  have eq65546 : (σ (M.op (M.op x x) (M.op x x))) = (k (σ (M.op x (M.op x y))) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq64991 eq2661
    | exact resolve eq2661 eq64991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64991
  have eq65594 : (σ (M.op (M.op x x) (M.op x x))) = (k (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq64972 eq65546
    | exact resolve eq65546 eq64972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65546
  have eq65614 : (σ (M.op (M.op x x) (M.op x x))) = (k (M.op (σ (M.op x y)) (M.op x y)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq65378 eq65594
    | exact resolve eq65594 eq65378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65594
  have eq65625 : (σ (M.op (M.op x x) (M.op x x))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq2582 eq65614
    | exact resolve eq65614 eq2582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65614
  have eq65628 : (M.op (σ x) (M.op x y)) = (σ (M.op (M.op x x) (M.op x x))) := by
    first
    | (have i₁ := eq65625
       have i₂ := eq4309 sF2 sF2 (M.op sF2 sF2)
       grind)
    | exact superpose eq4309 eq65625
    | exact resolve eq65625 eq4309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65625
  have eq65630 : (σ (M.op x (M.op x y))) = (M.op (σ x) (M.op x y)) := by
    first
    | (have i₁ := eq65628
       have i₂ := eq4256 x (M.op x x)
       grind)
    | exact superpose eq4256 eq65628
    | exact resolve eq65628 eq4256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65628
  have eq65632 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq64972 eq65630
    | exact resolve eq65630 eq64972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65630
  have eq65634 : (M.op (σ x) (M.op x y)) = (M.op (σ (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq65378 eq65632
    | exact resolve eq65632 eq65378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65632
  have eq68519 : ∀ X0 : G, (M.op X0 X0) = (k (τ (M.op x (M.op x y))) X0) := by
    intro X0
    first
    | exact superpose eq61340 eq2582
    | exact resolve eq2582 eq61340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68535 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (k (τ (M.op x (M.op x y))) X0)) := by
    intro X0
    first
    | exact superpose eq61340 eq12406
    | exact resolve eq12406 eq61340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61340
  have eq68618 : ∀ X0 : G, (k (M.op x (M.op x y)) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq68535 x
       have i₂ := eq34 (M.op x sF0) x
       grind)
    | exact superpose eq34 eq68535
    | exact resolve eq68535 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68535
  have eq68710 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | exact superpose eq3669 eq68519
    | exact resolve eq68519 eq3669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3669 eq68519
  have eq69520 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq68710 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq68710
    | exact resolve eq68710 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69709 : ∀ X0 : G, (k (σ (M.op x (M.op x y))) (M.op (σ X0) (σ X0))) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq2661 (M.op (σ X0) (σ X0))
       have i₂ := eq68710 X0
       grind)
    | exact superpose eq68710 eq2661
    | exact resolve eq2661 eq68710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2661 eq68710
  have eq69758 : ∀ X0 : G, (σ (M.op X0 (M.op x y))) = (k (σ (M.op x (M.op x y))) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq69709 X0
       have i₂ := eq4309 X0 X0 (M.op X0 X0)
       grind)
    | exact superpose eq4309 eq69709
    | exact resolve eq69709 eq4309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4309 eq69709
  have eq69925 : ∀ X0 : G, (σ (M.op X0 (M.op x y))) = (k (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | exact superpose eq64972 eq69758
    | exact resolve eq69758 eq64972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69758
  have eq70062 : ∀ X0 : G, (σ (M.op X0 (M.op x y))) = (k (M.op (σ (M.op x y)) (M.op x y)) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | exact superpose eq65378 eq69925
    | exact resolve eq69925 eq65378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69925
  have eq70132 : ∀ X0 : G, (M.op (σ X0) (M.op x y)) = (σ (M.op X0 (M.op x y))) := by
    intro X0
    first
    | exact superpose eq5039 eq70062
    | exact resolve eq70062 eq5039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5039 eq70062
  have eq89479 : ∀ X0 X1 : G, (M.op (σ X0) (M.op x y)) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | exact superpose eq68618 eq4623
    | exact resolve eq4623 eq68618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4623 eq68618
  have eq89622 : ∀ X0 X1 : G, (σ (M.op X0 (M.op x y))) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | exact superpose eq70132 eq89479
    | exact resolve eq89479 eq70132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70132 eq89479
  have eq92629 : ∀ X0 X1 : G, (σ (M.op X0 (M.op x y))) = (M.op (σ (M.op X0 (M.op x y))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2264 (σ (M.op X0 X0)) x
       have i₂ := eq89622 X0 sF0
       grind)
    | exact superpose eq89622 eq2264
    | exact resolve eq2264 eq89622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2264 eq89622
  have eq111895 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq122 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111896 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq111895
    | exact resolve eq111895 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111895
  have eq111909 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq111896
       have r₂ := eq27
       grind)
    | exact resolve eq111896 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111896
  have eq111915 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq111909
    | exact resolve eq111909 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111909
  have eq111923 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq111915 eq87
    | (have r₁ := eq87
       have r₂ := eq111915
       grind)
    | exact resolve eq87 eq111915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq111915
  have eq111989 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by grind
  clear eq111923
  have eq111990 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by grind
  clear eq111989
  have eq112064 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op (σ y) X1) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | exact superpose eq111990 eq52
    | exact resolve eq52 eq111990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112524 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq112064 eq111990
    | exact resolve eq111990 eq112064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111990 eq112064
  have eq112701 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq112524 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112524
  have eq113024 : ∀ X0 : G, (τ (σ y)) = (k X0 (τ (σ y))) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq112701 eq59700
    | exact resolve eq59700 eq112701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59700 eq112701
  have eq113064 : ∀ X0 : G, (σ x) = (k (σ y) (σ x)) ∨ y = (k X0 y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq29 eq113024
    | exact resolve eq113024 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq113024
  have eq113417 : ∀ X0 : G, (τ (σ x)) = (k y x) ∨ y = (k X0 y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq113064 eq95
    | (have j1 := eq113064 X0
       grind)
    | exact resolve eq95 eq113064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq113064
  have eq113438 : ∀ X0 : G, x = (k y x) ∨ y = (k X0 y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq28 eq113417
    | (have j0 := eq113417 X0
       grind)
    | exact resolve eq113417 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113417
  have eq113447 : ∀ X0 : G, y = (k X0 y) ∨ x = (k y x) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq113438 X0
       grind)
    | (have r₁ := eq113438 X0
       have r₂ := eq86
       grind)
    | exact resolve eq113438 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq113438
  have eq113451 : y = (M.op y y) ∨ x = (k y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq2545 eq113447
    | exact resolve eq113447 eq2545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2545
  have eq113562 : (σ y) = (σ (M.op y y)) ∨ x = (k y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq12406 x y
       have i₂ := eq113447 (M.op x sF0)
       grind)
    | exact superpose eq113447 eq12406
    | exact resolve eq12406 eq113447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12406 eq113447
  have eq113621 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (k y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq113562
       have i₂ := eq64970
       grind)
    | exact superpose eq64970 eq113562
    | exact resolve eq113562 eq64970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64970 eq113562
  have eq113675 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (k y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq113621
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq113621
    | exact resolve eq113621 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113621
  have eq113743 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (k y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq4254 y y
       have i₂ := eq113451
       grind)
    | exact superpose eq113451 eq4254
    | exact resolve eq4254 eq113451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113451
  have eq113760 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (k y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq113743
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq113743
    | exact resolve eq113743 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113743
  have eq114099 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (k y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq113675 eq288
    | exact resolve eq288 eq113675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288 eq113675
  have eq114168 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ x = (k y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1452 eq114099
    | exact resolve eq114099 eq1452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1452 eq114099
  have eq114179 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op x y)) ∨ x = (k y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq65634 eq114168
    | exact resolve eq114168 eq65634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114168
  have eq114181 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op x y)) ∨ x = (k y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq114179
    | exact resolve eq114179 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114179
  have eq114308 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) ∨ x = (k y x) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq113760 eq92629
    | exact resolve eq92629 eq113760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113760
  have eq114372 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) ∨ x = (k y x) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq20 eq114308
    | (have j0 := eq114308 X0
       grind)
    | exact resolve eq114308 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114308
  have eq115223 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k y x) ∨ y = (M.op y x) ∨ x = (k y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq114372 eq114181
    | exact resolve eq114181 eq114372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114181 eq114372
  have eq115410 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k y x) ∨ y = (M.op y x) := by grind
  clear eq115223
  have eq115465 : y = (M.op y x) ∨ x = (k y x) := by
    first
    | (have r₁ := eq115410
       have r₂ := eq27
       grind)
    | exact resolve eq115410 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115410
  have eq115496 : ∀ X0 X1 : G, (M.op y X0) = (M.op y X1) ∨ x = (k y x) := by
    intro X0 X1
    first
    | (have i₁ := eq52 y x x x
       have i₂ := eq115465
       grind)
    | exact superpose eq115465 eq52
    | exact resolve eq52 eq115465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq115509 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq4254 y x
       have i₂ := eq115465
       grind)
    | exact superpose eq115465 eq4254
    | exact resolve eq4254 eq115465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115524 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq115509
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq115509
    | exact resolve eq115509 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115509
  have eq115658 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) ∨ x = (k y x) := by
    intro X0
    first
    | exact superpose eq115524 eq92629
    | exact resolve eq92629 eq115524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115524
  have eq115723 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) ∨ x = (k y x) := by
    intro X0
    first
    | exact superpose eq20 eq115658
    | (have j0 := eq115658 X0
       grind)
    | exact resolve eq115658 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115658
  have eq117814 : ∀ X0 : G, y = (M.op y X0) ∨ x = (k y x) ∨ x = (k y x) := by
    intro X0
    first
    | (have i₁ := eq115465
       have i₂ := eq115496 x X0
       grind)
    | (have i₁ := eq115465
       have i₂ := eq115496 X0 x
       grind)
    | exact superpose eq115496 eq115465
    | exact resolve eq115465 eq115496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115465 eq115496
  have eq117984 : ∀ X0 : G, y = (M.op y X0) ∨ x = (k y x) := by
    intro X0
    first
    | (have j0 := eq117814 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117814
  have eq118317 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) ∨ x = (k y x) := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f118317_13 : ∀ X0 X1 : G, (σ (M.op X0 (M.op x y))) = (M.op (σ (M.op X0 (M.op x y))) X1) := by
      intro X0 X1
      grind
    have f118317_14 : ∀ X0 : G, y = (M.op y X0) ∨ x = (k y x) := by
      intro X0
      grind
    have f118317_23 : (σ y) ≠ (M.op (σ y) X0) := by grind
    have f118317_24 : x ≠ (k y x) := by grind
    have f118317_25 : ∀ X0 : G, y = (M.op y X0) := by
      intro X0
      first
      | (have j0 := f118317_14 X0
         grind)
      | (have r₁ := f118317_14 X0
         have r₂ := f118317_24
         grind)
      | exact resolve f118317_14 f118317_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f118317_59 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) := by
      intro X0
      first
      | (have i₁ := f118317_13 y x
         have i₂ := f118317_25 (M.op x y)
         grind)
      | exact superpose f118317_25 f118317_13
      | exact resolve f118317_13 f118317_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f118317_96 : (σ y) ≠ (σ y) := by
      first
      | (have i₁ := f118317_23
         have i₂ := f118317_59 X0
         grind)
      | exact superpose f118317_59 f118317_23
      | (have r₁ := f118317_23
         have r₂ := f118317_59 X0
         grind)
      | exact resolve f118317_23 f118317_59
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f118317_106 : False := by grind
    exact f118317_106
  clear eq117984
  have eq118344 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) ∨ x = (k y x) := by
    intro X0
    first
    | (have i₁ := eq118317 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq118317
    | (have j0 := eq118317 X0
       grind)
    | exact resolve eq118317 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118317
  have eq118831 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ x = (k y x) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f118831_14 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) ∨ x = (k y x) := by
      intro X0
      grind
    have f118831_20 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X2) X3) := by
      intro X0 X1 X2 X3
      grind
    have f118831_23 : (M.op (σ x) (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
    have f118831_24 : x ≠ (k y x) := by grind
    have f118831_25 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) := by
      intro X0
      first
      | (have j0 := f118831_14 X0
         grind)
      | (have r₁ := f118831_14 X0
         have r₂ := f118831_24
         grind)
      | exact resolve f118831_14 f118831_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f118831_32 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X0 (σ y)) := by
      intro X0 X1 X2
      first
      | (have i₁ := f118831_20 X0 (σ y) X1 X2
         have i₂ := f118831_25 X1
         grind)
      | exact superpose f118831_25 f118831_20
      | exact resolve f118831_20 f118831_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f118831_41 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X2)) := by
      intro X0 X1 X2 X3
      first
      | (have i₁ := f118831_20 X0 X1 X2 x
         have i₂ := f118831_20 X0 X3 X2 x
         grind)
      | exact superpose f118831_20 f118831_20
      | exact resolve f118831_20 f118831_20
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f118831_84 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (σ y)) := by
      intro X0 X1 X2
      first
      | (have i₁ := f118831_20 X0 X1 X2 x
         have i₂ := f118831_32 X0 X2 x
         grind)
      | exact superpose f118831_32 f118831_20
      | exact resolve f118831_20 f118831_32
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f118831_437 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ x) (M.op X0 y)) := by
      intro X0
      first
      | (have i₁ := f118831_23
         have i₂ := f118831_41 (σ x) x y X0
         grind)
      | (have i₁ := f118831_23
         have i₂ := f118831_41 (σ x) X0 y x
         grind)
      | exact superpose f118831_41 f118831_23
      | exact resolve f118831_23 f118831_41
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f118831_443 : False := by
      first
      | (have r₁ := f118831_437 x
         have r₂ := f118831_84 (σ x) x y
         grind)
      | exact resolve f118831_437 f118831_84
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f118831_443
  clear eq2413 eq118344
  have eq118915 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op x y)) ∨ x = (k y x) := by
    first
    | exact superpose eq65634 eq118831
    | exact resolve eq118831 eq65634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118831
  have eq118965 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op x y)) ∨ x = (k y x) := by
    first
    | exact superpose eq26 eq118915
    | exact resolve eq118915 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118915
  have eq119324 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k y x) ∨ x = (k y x) := by
    first
    | exact superpose eq118965 eq115723
    | exact resolve eq115723 eq118965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115723 eq118965
  have eq119419 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k y x) := by grind
  clear eq119324
  have eq119447 : x = (k y x) := by
    first
    | (have r₁ := eq119419
       have r₂ := eq27
       grind)
    | exact resolve eq119419 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119419
  have eq119481 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq79
       have i₂ := eq119447
       grind)
    | exact superpose eq119447 eq79
    | exact resolve eq79 eq119447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119492 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq119447
       grind)
    | exact superpose eq119447 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq119447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119493 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq119492
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq119492
    | exact resolve eq119492 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119492
  have eq119503 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq119481
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq119481
    | exact resolve eq119481 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119481
  have eq119506 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq119493
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq119493
    | exact resolve eq119493 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119493
  have eq119512 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq122 eq119503
    | exact resolve eq119503 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq125711 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq64969
       have i₂ := eq119506
       grind)
    | exact superpose eq119506 eq64969
    | exact resolve eq64969 eq119506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119506
  have eq125799 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq125711
    | exact resolve eq125711 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125711
  have eq125837 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq64969
       have i₂ := eq119512
       grind)
    | exact superpose eq119512 eq64969
    | exact resolve eq64969 eq119512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64969 eq119512
  have eq125924 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq125837
    | exact resolve eq125837 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125837
  have eq129115 : ∀ X0 X1 : G, (k (k (σ (M.op X1 (M.op x y))) X0) (σ x)) = (σ (k (τ (M.op X0 X0)) x)) := by
    intro X0 X1
    first
    | (have i₁ := eq7504 X0 X1
       have i₂ := eq69520 X0
       grind)
    | exact superpose eq69520 eq7504
    | exact resolve eq7504 eq69520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7504 eq69520
  have eq129116 : ∀ X0 X1 : G, (k (k (σ (M.op X1 (M.op x y))) X0) (σ x)) = (k (M.op X0 X0) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq129115 X0 X1
       have i₂ := eq34 (M.op X0 X0) x
       grind)
    | exact superpose eq34 eq129115
    | exact resolve eq129115 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq129115
  have eq129117 : ∀ X0 X1 : G, (k (k (σ (M.op X1 (M.op x y))) X0) (σ x)) = (k (M.op X0 X0) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq129116 X0 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq129116
    | (have j0 := eq129116 X0 X1
       grind)
    | exact resolve eq129116 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129116
  have eq129240 : ∀ X0 : G, (k (M.op (k (σ y) (σ x)) (k (σ y) (σ x))) (σ x)) = (k (σ (k (M.op X0 (M.op x y)) (k y x))) (σ x)) := by
    intro X0
    first
    | exact superpose eq93 eq129117
    | exact resolve eq129117 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq129117
  have eq129441 : ∀ X0 : G, (k (M.op (k (σ y) (σ x)) (k (σ y) (σ x))) (σ x)) = (σ (k (k (M.op X0 (M.op x y)) (k y x)) x)) := by
    intro X0
    first
    | exact superpose eq39 eq129240
    | exact resolve eq129240 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq129240
  have eq129528 : (k (M.op (k (σ y) (σ x)) (k (σ y) (σ x))) (σ x)) = (σ (k (M.op (k y x) (k y x)) x)) := by
    first
    | exact superpose eq2582 eq129441
    | exact resolve eq129441 eq2582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2582 eq129441
  have eq129573 : (σ (k (M.op x x) x)) = (k (M.op (k (σ y) (σ x)) (k (σ y) (σ x))) (σ x)) := by
    first
    | (have i₁ := eq129528
       have i₂ := eq119447
       grind)
    | exact superpose eq119447 eq129528
    | exact resolve eq129528 eq119447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129528
  have eq129603 : (σ (k (M.op x x) x)) = (k (M.op (σ x) (σ x)) (σ x)) := by
    first
    | exact superpose eq119503 eq129573
    | exact resolve eq129573 eq119503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129573
  have eq129654 : (k (M.op (σ x) (σ x)) (σ x)) = (σ (M.op x (M.op x x))) ∨ (M.op x x) = (M.op x (M.op x x)) ∨ (M.op x x) = (M.op (M.op x x) x) := by
    first
    | (have i₁ := eq129603
       have i₂ := eq11 (M.op x x) x
       grind)
    | exact superpose eq11 eq129603
    | (have j1 := eq11 (M.op x x) x
       grind)
    | exact resolve eq129603 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129660 : (k (M.op x x) x) = (τ (k (M.op (σ x) (σ x)) (σ x))) := by
    first
    | (have i₁ := eq16 (k (M.op x x) x)
       have i₂ := eq129603
       grind)
    | exact superpose eq129603 eq16
    | exact resolve eq16 eq129603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129603
  have eq129758 : (σ (M.op x (M.op x y))) = (k (M.op (σ x) (σ x)) (σ x)) ∨ (M.op x x) = (M.op x (M.op x x)) ∨ (M.op x x) = (M.op (M.op x x) x) := by
    first
    | (have i₁ := eq129654
       have i₂ := eq4254 x x
       grind)
    | exact superpose eq4254 eq129654
    | exact resolve eq129654 eq4254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129654
  have eq129777 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (M.op (σ x) (σ x)) (σ x)) ∨ (M.op x x) = (M.op x (M.op x x)) ∨ (M.op x x) = (M.op (M.op x x) x) := by
    first
    | exact superpose eq64972 eq129758
    | exact resolve eq129758 eq64972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64972 eq129758
  have eq129781 : (M.op (σ (M.op x y)) (M.op x y)) = (k (M.op (σ x) (σ x)) (σ x)) ∨ (M.op x x) = (M.op x (M.op x x)) ∨ (M.op x x) = (M.op (M.op x x) x) := by
    first
    | exact superpose eq65378 eq129777
    | exact resolve eq129777 eq65378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65378 eq129777
  have eq129783 : (M.op x x) = (M.op x (M.op x y)) ∨ (M.op (σ (M.op x y)) (M.op x y)) = (k (M.op (σ x) (σ x)) (σ x)) ∨ (M.op x x) = (M.op (M.op x x) x) := by
    first
    | (have i₁ := eq129781
       have i₂ := eq4254 x x
       grind)
    | exact superpose eq4254 eq129781
    | exact resolve eq129781 eq4254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129781
  have eq129785 : (M.op x x) = (M.op x (M.op x y)) ∨ (M.op x x) = (M.op x (M.op x y)) ∨ (M.op (σ (M.op x y)) (M.op x y)) = (k (M.op (σ x) (σ x)) (σ x)) := by
    first
    | (have i₁ := eq129783
       have i₂ := eq4256 x x
       grind)
    | exact superpose eq4256 eq129783
    | exact resolve eq129783 eq4256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4256 eq129783
  have eq129786 : (M.op (σ (M.op x y)) (M.op x y)) = (k (M.op (σ x) (σ x)) (σ x)) ∨ (M.op x x) = (M.op x (M.op x y)) := by grind
  clear eq129785
  have eq149115 : (k (M.op x x) x) = (τ (M.op (σ (M.op x y)) (M.op x y))) ∨ (M.op x x) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq129786 eq129660
    | exact resolve eq129660 eq129786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129660 eq129786
  have eq149125 : (M.op x (M.op x y)) = (k (M.op x x) x) ∨ (M.op x x) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq65313 eq149115
    | exact resolve eq149115 eq65313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65313 eq149115
  have eq574623 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 (k (σ y) (σ x))) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq50019 y X0
       have i₂ := eq79
       grind)
    | exact superpose eq79 eq50019
    | (have j0 := eq50019 y x
       grind)
    | exact resolve eq50019 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50019
  have eq575153 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq119503 eq574623
    | exact resolve eq574623 eq119503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574623
  have eq575273 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op X0 (M.op x y)) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq575153 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq575153
    | (have j0 := eq575153 X0
       grind)
    | exact resolve eq575153 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575153
  have eq575343 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op X0 (M.op x y)) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq575273
    | (have j0 := eq575273 X0
       grind)
    | exact resolve eq575273 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575273
  have eq575373 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq575343 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq575343
    | (have j0 := eq575343 X0
       grind)
    | exact resolve eq575343 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575343
  have eq575399 : ∀ X0 X1 : G, (M.op (σ (M.op x y)) (M.op x y)) = (M.op (σ (k X0 x)) X1) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq65634 eq50041
    | (have j0 := eq50041 X0 X1
       grind)
    | exact resolve eq50041 eq65634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50041
  have eq604397 : ∀ X0 : G, (M.op (σ (M.op x y)) (M.op x y)) = (M.op (k (σ y) (σ x)) X0) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq575399 y X0
       have i₂ := eq79
       grind)
    | exact superpose eq79 eq575399
    | (have j0 := eq575399 y x
       grind)
    | exact resolve eq575399 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq575399
  have eq604928 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ (M.op x y)) (M.op x y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq119503 eq604397
    | exact resolve eq604397 eq119503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604397
  have eq605075 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) X0) = (M.op (σ (M.op x y)) (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq604928 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq604928
    | (have j0 := eq604928 X0
       grind)
    | exact resolve eq604928 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604928
  have eq605184 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) X0) = (M.op (σ (M.op x y)) (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq605075
    | (have j0 := eq605075 X0
       grind)
    | exact resolve eq605075 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605075
  have eq605221 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ (M.op x y)) (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq605184 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq605184
    | (have j0 := eq605184 X0
       grind)
    | exact resolve eq605184 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq605184
  have eq2785765 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq575373
  have eq2785781 : (M.op (σ x) (σ y)) ≠ (M.op (σ (M.op x y)) (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq65634 eq2785765
    | exact resolve eq2785765 eq65634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65634 eq2785765
  have eq2790991 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq605221 eq26
    | (have j1 := eq605221 (σ y)
       grind)
    | exact resolve eq26 eq605221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605221
  have eq2791405 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq2790991
       have r₂ := eq2785781
       grind)
    | exact resolve eq2790991 eq2785781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2785781 eq2790991
  have eq2791666 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq2791405 eq125799
    | exact resolve eq125799 eq2791405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125799 eq2791405
  have eq2791963 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2791666
       have r₂ := eq27
       grind)
    | exact resolve eq2791666 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2791666
  have eq2804948 : (σ y) ≠ (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2791963 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq2791963
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq2791963
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq2791963
       grind)
    | exact resolve eq13 eq2791963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2791963
  have eq2805025 : (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq2804948
  have eq2805061 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq119503 eq2805025
    | exact resolve eq2805025 eq119503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119503 eq2805025
  have eq2807984 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2805061 eq125924
    | exact resolve eq125924 eq2805061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125924 eq2805061
  have eq2808239 : y = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq2807984
  have eq2808425 : y ≠ y ∨ (k y x) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq2808239
       grind)
    | exact superpose eq2808239 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq2808239
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq2808239
       grind)
    | exact resolve eq13 eq2808239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2808444 : (M.op x y) = (M.op x (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4254 y x
       have i₂ := eq2808239
       grind)
    | exact superpose eq2808239 eq4254
    | exact resolve eq4254 eq2808239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4254 eq2808239
  have eq2808497 : (k y x) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq2808425
  have eq2808528 : (M.op x y) = (M.op x (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2808444
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2808444
    | exact resolve eq2808444 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2808444
  have eq2808542 : x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2808497
       have i₂ := eq119447
       grind)
    | exact superpose eq119447 eq2808497
    | exact resolve eq2808497 eq119447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119447 eq2808497
  have eq2817337 : (k x x) = (M.op x (M.op x y)) ∨ x = (M.op x (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq149125
       have i₂ := eq2808542
       grind)
    | exact superpose eq2808542 eq149125
    | exact resolve eq149125 eq2808542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149125 eq2808542
  have eq2817621 : x = (M.op x (M.op x y)) ∨ x = (M.op x (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2817337
       have i₂ := eq5272
       grind)
    | exact superpose eq5272 eq2817337
    | exact resolve eq2817337 eq5272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5272 eq2817337
  have eq2817622 : x = (M.op x (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq2817621
  have eq2836451 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2817622 eq2808528
    | exact resolve eq2808528 eq2817622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2808528 eq2817622
  have eq2836631 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq2836451
  have eq2836778 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2836631 eq28
    | exact resolve eq28 eq2836631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2836631
  have eq2837676 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq2836778
    | exact resolve eq2836778 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2836778
  have eq2837677 : x = (M.op x y) := by grind
  clear eq2837676
  have eq2840011 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq2837677 eq20
    | exact resolve eq20 eq2837677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq2840047 : ∀ X0 : G, (M.op x x) = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq2837677 eq213
    | exact resolve eq213 eq2837677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq2841049 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2840011
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2840011
    | exact resolve eq2840011 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2840011
  have eq2847697 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq2841049 eq26
    | exact resolve eq26 eq2841049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq2850191 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq2840047 y
       grind)
    | exact superpose eq2840047 eq18
    | (have j1 := eq2840047 y
       grind)
    | exact resolve eq18 eq2840047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq2850832 : x = (M.op x x) := by
    first
    | exact superpose eq2837677 eq2850191
    | exact resolve eq2850191 eq2837677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2837677 eq2850191
  have eq2851595 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq2850832
       have i₂ := eq2840047 X0
       grind)
    | (have i₁ := eq2850832
       have i₂ := eq2840047 x
       grind)
    | exact superpose eq2840047 eq2850832
    | exact resolve eq2850832 eq2840047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2840047 eq2850832
  have eq2853451 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq92629 x x
       have i₂ := eq2851595 sF0
       grind)
    | exact superpose eq2851595 eq92629
    | exact resolve eq92629 eq2851595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92629 eq2851595
  have eq2853520 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq2853451 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2853451
    | (have j0 := eq2853451 X0
       grind)
    | exact resolve eq2853451 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2853451
  have eq2853899 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq2841049 eq2853520
    | exact resolve eq2853520 eq2841049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2841049 eq2853520
  have eq2876940 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2853899 eq2847697
    | exact resolve eq2847697 eq2853899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2847697 eq2853899
  have eq2877421 : False := by grind
  exact eq2877421

/-- `Equation4520`: `x ◇ (y ◇ z) = (x ◇ w) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,X) else if m(X,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxx_y_pxx_y_pyx_Equation4520 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law4520 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4520.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X3) X2) := by
    intro X0 X1 X2 X3
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
  have eq51 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 X5) (M.op X4 X2)) = (M.op X3 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq14 X3 X0 (M.op X4 X2) X5
       have i₂ := eq14 X0 X4 X2 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X3 X5) X2) = (M.op X3 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq14 X3 (M.op X0 x) X2 X5
       have i₂ := eq14 X0 X1 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X4) X2) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq14 X0 x X2 X4
       have i₂ := eq14 X0 x X2 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op (M.op x y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 x X0 X1 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x X0 X1 y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) X0 X1 (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 X1 X2 x
       have i₂ := eq14 X0 X3 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) ≠ (M.op X3 X2) ∨ (M.op X0 X0) = (k X0 (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X0 (M.op X3 X2)
       have i₂ := eq14 X0 X3 X2 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 (M.op X3 X2)
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op X0 X3) X2)
       have r₂ := eq14 X0 (M.op X0 X3) X2 X3
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq81 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  clear eq25 eq37
  have eq83 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq89 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
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
  have eq93 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq50
       have i₂ := eq11 sF2 sF2
       grind)
    | exact superpose eq11 eq50
    | (have j1 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq50 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq93
  have eq96 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq89
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq80
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq80
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq80 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq105 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq99
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq99
    | exact resolve eq99 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq106 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq21 eq105
    | exact resolve eq105 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq107 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq81
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq81
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq81 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq81
       grind)
    | exact superpose eq81 eq16
    | exact resolve eq16 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq107
  have eq120 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    grind
  have eq124 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq112
       have i₂ := eq11 sF3 sF3
       grind)
    | exact superpose eq11 eq112
    | (have j1 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq112 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq124
  have eq129 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) X1) = (k (M.op X0 X1) (M.op (M.op (M.op X0 X1) X2) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq120 (M.op X1 X2)
       have i₂ := eq14 (M.op X1 X2) X1 X2 x
       grind)
    | exact superpose eq14 eq120
    | exact resolve eq120 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 X2))) = (k (M.op X0 X2) (M.op X0 (M.op X1 (M.op X0 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq120 (M.op X0 x)
       have i₂ := eq14 X0 X1 (M.op X0 x) x
       grind)
    | exact superpose eq14 eq120
    | exact resolve eq120 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq162 : (σ (k (k y y) x)) = (k (k (σ y) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq40 (k y y)
       have i₂ := eq81
       grind)
    | exact superpose eq81 eq40
    | exact resolve eq40 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq219 : (M.op x (M.op x y)) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq57 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq57
    | (have j0 := eq57 x y
       grind)
    | exact resolve eq57 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq220 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X1 X0)) = (M.op x (M.op (M.op x y) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq57 x (M.op X1 X0)
       have i₂ := eq57 X1 X0
       grind)
    | exact superpose eq57 eq57
    | exact resolve eq57 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq222 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (M.op (M.op x X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq57 x X1
       have i₂ := eq14 x x X1 X0
       grind)
    | exact superpose eq14 eq57
    | exact resolve eq57 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq225 : ∀ X0 X1 X2 : G, (M.op x (M.op X1 X2)) = (M.op (M.op (M.op x y) X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 x X1 X2 (M.op x X0)
       have i₂ := eq57 x X0
       grind)
    | exact superpose eq57 eq14
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq226 : ∀ X0 X2 : G, (M.op (M.op x y) X2) = (M.op (M.op (M.op x y) X0) X2) := by
    intro X0 X2
    first
    | (have i₁ := eq225 X0 x X2
       have i₂ := eq57 x X2
       grind)
    | exact superpose eq57 eq225
    | exact resolve eq225 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq227 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op x y) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq220 X1 X1
       have i₂ := eq57 sF0 X1
       grind)
    | exact superpose eq57 eq220
    | exact resolve eq220 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220
  have eq234 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq27 eq58
    | (have j0 := eq58 (σ x) (σ y)
       grind)
    | exact resolve eq58 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq236 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X1) = (M.op (M.op (σ x) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq58 X1 x
       have i₂ := eq14 sF2 X1 x x
       grind)
    | exact superpose eq14 eq58
    | exact resolve eq58 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq248 : (M.op x (M.op x y)) = (M.op x (M.op x (M.op x y))) := by
    first
    | exact superpose eq219 eq57
    | exact resolve eq57 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq251 : (M.op x (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq248
       have i₂ := eq57 x sF0
       grind)
    | exact superpose eq57 eq248
    | exact resolve eq248 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248
  have eq290 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq234 eq58
    | exact resolve eq58 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq295 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq58 eq290
    | exact resolve eq290 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq415 : ∀ X0 X1 : G, (M.op X0 (M.op X1 y)) = (M.op X0 (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq59 X0 x y X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq59
    | (have j0 := eq59 X0 X1 y x
       grind)
    | exact resolve eq59 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq421 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ y))) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq27 eq59
    | (have j0 := eq59 X0 X1 (σ y) (σ x)
       grind)
    | exact resolve eq59 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq561 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) y) = (M.op X0 (M.op X2 (M.op x y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X2 x y X0 X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq52
    | (have j0 := eq52 X2 x y X0 X1
       grind)
    | exact resolve eq52 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1988 : ∀ X0 X1 : G, (M.op (M.op X0 X1) y) = (M.op X0 (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq415 X0 x
       have i₂ := eq14 X0 x y X1
       grind)
    | exact superpose eq14 eq415
    | (have j1 := eq14 X0 x y X1
       grind)
    | exact resolve eq415 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2040 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X0 X1) (M.op x y)) = (M.op X0 (M.op (M.op X3 X4) y)) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq51 X3 X4 y X0 x X1
       have i₂ := eq415 (M.op X0 X1) x
       grind)
    | (have i₁ := eq51 X0 X1 y X3 x x
       have i₂ := eq415 (M.op X3 x) X1
       grind)
    | exact superpose eq415 eq51
    | (have j0 := eq51 X3 X4 y X0 x X1
       grind)
    | exact resolve eq51 eq415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2077 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op x y)) = (M.op X0 (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq2040 X0 X1 x x
       have i₂ := eq415 X0 (M.op x x)
       grind)
    | exact superpose eq415 eq2040
    | exact resolve eq2040 eq415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2040
  have eq2188 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X0 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq70 X0 X1 X2 (M.op X0 X1)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq2238 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq421 X0 X1
       have i₂ := eq14 X0 X1 sF3 x
       grind)
    | exact superpose eq14 eq421
    | (have j1 := eq14 X0 (σ x) (σ y) X1
       grind)
    | exact resolve eq421 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2292 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X0 X1) (M.op (σ x) (σ y))) = (M.op X0 (M.op (M.op X3 X4) (σ y))) := by
    intro X0 X1 X3 X4
    first
    | exact superpose eq421 eq51
    | (have j0 := eq51 X3 X4 (σ y) X0 (σ x) X1
       grind)
    | exact resolve eq51 eq421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq2331 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq421 eq2292
    | exact resolve eq2292 eq421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2292
  have eq2390 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op x y) X0) X2) (M.op X1 X0)) = (k (M.op (M.op x y) X0) (M.op (M.op (M.op (M.op x y) X0) X2) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq129 x (M.op X0 X1) X2
       have i₂ := eq57 X0 X1
       grind)
    | exact superpose eq57 eq129
    | exact resolve eq129 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq2459 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) X2) (M.op X1 X0)) = (k (M.op (M.op x y) X0) (M.op (M.op (M.op x y) X2) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | exact superpose eq226 eq2390
    | exact resolve eq2390 eq226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2390
  have eq2471 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X1 X0)) = (k (M.op (M.op x y) X0) (M.op (M.op x y) (M.op X1 X0))) := by
    intro X0 X1
    first
    | exact superpose eq226 eq2459
    | exact resolve eq2459 eq226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226 eq2459
  have eq2480 : ∀ X0 : G, (M.op (M.op x y) X0) = (k (M.op (M.op x y) X0) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq227 eq2471
    | exact resolve eq2471 eq227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227 eq2471
  have eq2765 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq83 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq2766 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq2765 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2765
  have eq3232 : ∀ X0 X2 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op X2 (M.op x y))) := by
    intro X0 X2
    first
    | (have i₁ := eq561 X0 x X2
       have i₂ := eq1988 X0 x
       grind)
    | exact superpose eq1988 eq561
    | exact resolve eq561 eq1988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561
  have eq3274 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op x y))) = (k (M.op X1 (M.op x y)) (M.op X1 (M.op X0 (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq3232 eq130
    | exact resolve eq130 eq3232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq3355 : ∀ X1 : G, (M.op X1 (M.op x y)) = (k (M.op X1 (M.op x y)) (M.op X1 (M.op x y))) := by
    intro X1
    first
    | exact superpose eq3232 eq3274
    | exact resolve eq3274 eq3232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3232 eq3274
  have eq4725 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X0 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2188 X0 x X2
       have i₂ := eq14 X0 X1 X2 x
       grind)
    | exact superpose eq14 eq2188
    | exact resolve eq2188 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2188
  have eq24039 : (τ (k (σ x) (σ x))) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq96
       grind)
    | exact superpose eq96 eq16
    | exact resolve eq16 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq24065 : (k x x) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq50 eq24039
    | exact resolve eq24039 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24039
  have eq24068 : (k x x) = (M.op x x) := by
    first
    | (have j1 := eq13 x x
       grind)
    | (have r₁ := eq24065
       have r₂ := eq13 x x
       grind)
    | exact resolve eq24065 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24065
  have eq24069 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq24068
       grind)
    | exact superpose eq24068 eq44
    | exact resolve eq44 eq24068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq25378 : ∀ X0 : G, (σ (M.op X0 (M.op x y))) ≠ (σ (M.op X0 (M.op x y))) ∨ (σ (M.op X0 (M.op x y))) = (M.op (σ (M.op X0 (M.op x y))) (σ (M.op X0 (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq3355 eq2766
    | (have j0 := eq2766 (M.op X0 (M.op x y))
       grind)
    | exact resolve eq2766 eq3355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3355
  have eq25384 : ∀ X0 : G, (σ (M.op (M.op x y) X0)) ≠ (σ (M.op (M.op x y) X0)) ∨ (σ (M.op (M.op x y) X0)) = (M.op (σ (M.op (M.op x y) X0)) (σ (M.op (M.op x y) X0))) := by
    intro X0
    first
    | exact superpose eq2480 eq2766
    | (have j0 := eq2766 (M.op (M.op x y) X0)
       grind)
    | exact resolve eq2766 eq2480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2480 eq2766
  have eq25405 : ∀ X0 : G, (σ (M.op (M.op x y) X0)) = (M.op (σ (M.op (M.op x y) X0)) (σ (M.op (M.op x y) X0))) := by
    intro X0
    first
    | (have j0 := eq25384 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25384
  have eq25409 : ∀ X0 : G, (σ (M.op X0 (M.op x y))) = (M.op (σ (M.op X0 (M.op x y))) (σ (M.op X0 (M.op x y)))) := by
    intro X0
    first
    | (have j0 := eq25378 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25378
  have eq26431 : (M.op y y) = (τ (k (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq113
       grind)
    | exact superpose eq113 eq16
    | exact resolve eq16 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq26463 : (k y y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq112 eq26431
    | exact resolve eq26431 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26431
  have eq26466 : (k y y) = (M.op y y) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq26463
       have r₂ := eq13 y y
       grind)
    | exact resolve eq26463 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26463
  have eq26467 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq81
       have i₂ := eq26466
       grind)
    | exact superpose eq26466 eq81
    | exact resolve eq81 eq26466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq26471 : (k (k (σ y) (σ y)) (σ x)) = (σ (k (M.op y y) x)) := by
    first
    | (have i₁ := eq162
       have i₂ := eq26466
       grind)
    | exact superpose eq26466 eq162
    | exact resolve eq162 eq26466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162
  have eq41792 : (M.op x x) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq95
       have i₂ := eq24068
       grind)
    | exact superpose eq24068 eq95
    | exact resolve eq95 eq24068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq41793 : (M.op y y) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq126
       have i₂ := eq26466
       grind)
    | exact superpose eq26466 eq126
    | exact resolve eq126 eq26466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq41805 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq41792 eq15
    | exact resolve eq15 eq41792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41792
  have eq41853 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq41805
       have i₂ := eq24069
       grind)
    | exact superpose eq24069 eq41805
    | exact resolve eq41805 eq24069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41805
  have eq41857 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq41853
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq41853 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41853
  have eq41860 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq41857 eq50
    | exact resolve eq50 eq41857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq41878 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq41860
       have i₂ := eq24068
       grind)
    | exact superpose eq24068 eq41860
    | exact resolve eq41860 eq24068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24068 eq41860
  have eq42205 : (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq41793 eq15
    | exact resolve eq15 eq41793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41793
  have eq42255 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq42205
       have i₂ := eq26467
       grind)
    | exact superpose eq26467 eq42205
    | exact resolve eq42205 eq26467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42205
  have eq42258 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq42255
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq42255 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42255
  have eq42261 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq42258 eq112
    | exact resolve eq112 eq42258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq42278 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq42261
       have i₂ := eq26466
       grind)
    | exact superpose eq26466 eq42261
    | exact resolve eq42261 eq26466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26466 eq42261
  have eq83979 : ∀ X0 : G, (M.op (σ (M.op (M.op x y) X0)) (σ y)) = (M.op (σ (M.op (M.op x y) X0)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq25405 eq2238
    | exact resolve eq2238 eq25405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83985 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op X1 (σ (M.op (M.op x y) X0)))) := by
    intro X0 X1
    first
    | exact superpose eq25405 eq4725
    | exact resolve eq4725 eq25405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25405
  have eq126876 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq106 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126877 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq27 eq126876
    | exact resolve eq126876 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126876
  have eq126888 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq126877
       have r₂ := eq28
       grind)
    | exact resolve eq126877 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126877
  have eq126898 : (τ (σ x)) = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq126888 eq42278
    | exact resolve eq42278 eq126888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42278 eq126888
  have eq127188 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq29 eq126898
    | exact resolve eq126898 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126898
  have eq127189 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by grind
  clear eq127188
  have eq127298 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq127189 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq127189
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq127189
       grind)
    | exact resolve eq13 eq127189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127299 : ∀ X0 X1 : G, (M.op (σ x) X1) = (M.op (σ y) (M.op X0 X1)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    intro X0 X1
    first
    | exact superpose eq127189 eq14
    | exact resolve eq14 eq127189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127437 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq127189 eq2238
    | exact resolve eq2238 eq127189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127450 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by grind
  clear eq127298
  have eq127453 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq27 eq127437
    | exact resolve eq127437 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127437
  have eq132577 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq127450 eq106
    | exact resolve eq106 eq127450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq127450
  have eq132585 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by grind
  clear eq132577
  have eq132695 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (σ (M.op x y))) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq132585 eq421
    | exact resolve eq421 eq132585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132843 : (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq132585 eq2331
    | exact resolve eq2331 eq132585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132585
  have eq144279 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ x = (M.op y y) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq132843 eq127453
    | exact resolve eq127453 eq132843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127453 eq132843
  have eq144465 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ x = (M.op y y) ∨ x = (M.op y x) := by grind
  clear eq144279
  have eq144515 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op y y) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq144465 eq132695
    | exact resolve eq132695 eq144465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132695 eq144465
  have eq144680 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op y y) ∨ x = (M.op y x) := by grind
  clear eq144515
  have eq217535 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq127189 eq127299
    | exact resolve eq127299 eq127189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127299
  have eq218023 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by grind
  clear eq217535
  have eq218696 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq218023 eq127189
    | exact resolve eq127189 eq218023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127189 eq218023
  have eq218912 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by grind
  clear eq218696
  have eq219150 : (τ (σ x)) = (M.op x x) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq218912 eq41878
    | exact resolve eq41878 eq218912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41878 eq218912
  have eq219429 : x = (M.op y y) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq29 eq219150
    | exact resolve eq219150 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq219150
  have eq219468 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq26467
       have i₂ := eq219429
       grind)
    | exact superpose eq219429 eq26467
    | exact resolve eq26467 eq219429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26467
  have eq219479 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 x) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq415 X0 y
       have i₂ := eq219429
       grind)
    | exact superpose eq219429 eq415
    | exact resolve eq415 eq219429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415
  have eq219643 : (M.op x y) = (M.op y (M.op x y)) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1988 y y
       have i₂ := eq219429
       grind)
    | exact superpose eq219429 eq1988
    | exact resolve eq1988 eq219429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219429
  have eq219720 : (M.op x y) = (M.op y (M.op x y)) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq219643
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq219643
    | exact resolve eq219643 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219643
  have eq219860 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq42258 eq219468
    | exact resolve eq219468 eq42258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219468
  have eq219961 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq219860
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq219860
    | exact resolve eq219860 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219860
  have eq220908 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq219720 eq2077
    | exact resolve eq2077 eq219720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2077 eq219720
  have eq220986 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq251 eq220908
    | exact resolve eq220908 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251 eq220908
  have eq221152 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq219961 eq421
    | exact resolve eq421 eq219961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221339 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq219961 eq2238
    | exact resolve eq2238 eq219961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2238 eq219961
  have eq221385 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq27 eq221339
    | exact resolve eq221339 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221339
  have eq223833 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq221385 eq2331
    | exact resolve eq2331 eq221385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221385
  have eq223890 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq295 eq223833
    | exact resolve eq223833 eq295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295 eq223833
  have eq228278 : (M.op x y) = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op y x) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq219479 eq220986
    | exact resolve eq220986 eq219479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219479 eq220986
  have eq228446 : (M.op x y) = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op y x) := by grind
  clear eq228278
  have eq229503 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq24069
       have i₂ := eq228446
       grind)
    | exact superpose eq228446 eq24069
    | exact resolve eq24069 eq228446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228446
  have eq229933 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq41857 eq229503
    | exact resolve eq229503 eq41857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229503
  have eq230036 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq21 eq229933
    | exact resolve eq229933 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229933
  have eq246603 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y x) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq221152 eq223890
    | exact resolve eq223890 eq221152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221152 eq223890
  have eq246670 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y x) := by grind
  clear eq246603
  have eq250507 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y x) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq246670 eq230036
    | exact resolve eq230036 eq246670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230036 eq246670
  have eq250747 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y x) := by grind
  clear eq250507
  have eq250936 : x = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq250747
       have r₂ := eq28
       grind)
    | exact resolve eq250747 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250747
  have eq251096 : ∀ X0 X1 : G, (M.op x X1) = (M.op y (M.op X0 X1)) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq14 y X0 X1 x
       have i₂ := eq250936
       grind)
    | exact superpose eq250936 eq14
    | exact resolve eq14 eq250936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq284036 : (M.op x x) = (M.op y x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq251096 y x
       have i₂ := eq250936
       grind)
    | exact superpose eq250936 eq251096
    | exact resolve eq251096 eq250936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251096
  have eq284686 : (M.op x x) = (M.op y x) ∨ x = (M.op x x) := by grind
  clear eq284036
  have eq285327 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq250936
       have i₂ := eq284686
       grind)
    | exact superpose eq284686 eq250936
    | exact resolve eq250936 eq284686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250936 eq284686
  have eq285567 : x = (M.op x x) := by grind
  clear eq285327
  have eq285820 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq24069
       have i₂ := eq285567
       grind)
    | exact superpose eq285567 eq24069
    | exact resolve eq24069 eq285567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24069
  have eq285830 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq222 x X0
       have i₂ := eq285567
       grind)
    | exact superpose eq285567 eq222
    | exact resolve eq222 eq285567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq285857 : (M.op x x) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq57 x x
       have i₂ := eq285567
       grind)
    | exact superpose eq285567 eq57
    | exact resolve eq57 eq285567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq285859 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op X1 x)) := by
    intro X0 X1
    first
    | (have i₁ := eq59 X0 x x X1
       have i₂ := eq285567
       grind)
    | exact superpose eq285567 eq59
    | exact resolve eq59 eq285567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq286005 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq1988 x x
       have i₂ := eq285567
       grind)
    | exact superpose eq285567 eq1988
    | exact resolve eq1988 eq285567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1988
  have eq286071 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq4725 X0 x x
       have i₂ := eq285567
       grind)
    | exact superpose eq285567 eq4725
    | exact resolve eq4725 eq285567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4725
  have eq286093 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq286005
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq286005
    | exact resolve eq286005 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286005
  have eq286102 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq285857
       have i₂ := eq285567
       grind)
    | exact superpose eq285567 eq285857
    | exact resolve eq285857 eq285567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285857
  have eq286127 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq41857 eq285820
    | exact resolve eq285820 eq41857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41857 eq285820
  have eq286167 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq286127
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq286127
    | exact resolve eq286127 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286127
  have eq286229 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq286093 eq25409
    | exact resolve eq25409 eq286093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25409 eq286093
  have eq286598 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq286229
    | exact resolve eq286229 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286229
  have eq286762 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq286102 eq83979
    | exact resolve eq83979 eq286102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83979
  have eq286763 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 (σ x))) := by
    intro X0
    first
    | exact superpose eq286102 eq83985
    | exact resolve eq83985 eq286102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83985 eq286102
  have eq287141 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq286763 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq286763
    | (have j0 := eq286763 X0
       grind)
    | exact resolve eq286763 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286763
  have eq287142 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq286762
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq286762
    | exact resolve eq286762 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq286762
  have eq287227 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq27 eq287142
    | exact resolve eq287142 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287142
  have eq291829 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq286167 eq236
    | exact resolve eq236 eq286167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236
  have eq291859 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op X1 (σ x))) := by
    intro X0 X1
    first
    | exact superpose eq286167 eq59
    | exact resolve eq59 eq286167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq309381 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq286598 eq144680
    | exact resolve eq144680 eq286598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144680 eq286598
  have eq309679 : x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq309381
       have r₂ := eq28
       grind)
    | exact resolve eq309381 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309381
  have eq361435 : ∀ X0 X1 : G, (M.op X0 x) = (M.op (M.op X0 X1) x) := by
    intro X0 X1
    first
    | (have i₁ := eq285859 X0 x
       have i₂ := eq14 X0 x x X1
       grind)
    | exact superpose eq14 eq285859
    | exact resolve eq285859 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285859
  have eq383536 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op (M.op X0 X1) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq291859 X0 X1
       have i₂ := eq14 X0 X1 sF2 x
       grind)
    | exact superpose eq14 eq291859
    | exact resolve eq291859 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291859
  have eq430777 : (M.op x x) = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq361435 y y
       have i₂ := eq309679
       grind)
    | exact superpose eq309679 eq361435
    | exact resolve eq361435 eq309679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309679 eq361435
  have eq430786 : x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq430777
       have i₂ := eq285567
       grind)
    | exact superpose eq285567 eq430777
    | exact resolve eq430777 eq285567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430777
  have eq430787 : x = (M.op y x) := by grind
  clear eq430786
  have eq431434 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op y X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq53 y x X0 X1
       have i₂ := eq430787
       grind)
    | exact superpose eq430787 eq53
    | exact resolve eq53 eq430787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430787
  have eq443941 : ∀ X0 : G, (M.op (M.op y X0) (M.op y X0)) = (k (M.op y X0) (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq286071 (M.op y X0)
       have i₂ := eq431434 x X0
       grind)
    | exact superpose eq431434 eq286071
    | exact resolve eq286071 eq431434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286071
  have eq444009 : ∀ X0 : G, (M.op (M.op y X0) (M.op y X0)) = (k (M.op y X0) x) := by
    intro X0
    first
    | (have i₁ := eq443941 X0
       have i₂ := eq285567
       grind)
    | exact superpose eq285567 eq443941
    | exact resolve eq443941 eq285567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285567 eq443941
  have eq444596 : ∀ X0 : G, (M.op x (M.op y X0)) = (k (M.op y X0) x) := by
    intro X0
    first
    | (have i₁ := eq444009 X0
       have i₂ := eq431434 (M.op y X0) X0
       grind)
    | exact superpose eq431434 eq444009
    | exact resolve eq444009 eq431434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431434 eq444009
  have eq444870 : ∀ X0 : G, (M.op (M.op x y) X0) = (k (M.op y X0) x) := by
    intro X0
    first
    | (have i₁ := eq444596 X0
       have i₂ := eq57 y X0
       grind)
    | exact superpose eq57 eq444596
    | exact resolve eq444596 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq444596
  have eq445089 : ∀ X0 : G, (M.op x X0) = (k (M.op y X0) x) := by
    intro X0
    first
    | exact superpose eq285830 eq444870
    | exact resolve eq444870 eq285830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285830 eq444870
  have eq466000 : (σ (M.op x y)) = (k (k (σ y) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq26471
       have i₂ := eq445089 y
       grind)
    | exact superpose eq445089 eq26471
    | exact resolve eq26471 eq445089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26471 eq445089
  have eq466041 : (σ (M.op x y)) = (k (M.op (σ y) (σ y)) (σ x)) := by
    first
    | exact superpose eq42258 eq466000
    | exact resolve eq466000 eq42258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42258 eq466000
  have eq466125 : (σ (M.op x y)) = (k (M.op (σ y) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq466041
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq466041
    | exact resolve eq466041 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq466041
  have eq466179 : (σ (M.op x y)) = (k (M.op (σ y) (σ y)) (σ x)) := by
    first
    | exact superpose eq21 eq466125
    | exact resolve eq466125 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq466125
  have eq466340 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) := by
    first
    | exact superpose eq466179 eq11
    | (have j0 := eq11 (M.op (σ y) (σ y)) (σ x)
       grind)
    | exact resolve eq11 eq466179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq466362 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) := by
    first
    | exact superpose eq58 eq466340
    | exact resolve eq466340 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466340
  have eq466365 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) := by
    first
    | exact superpose eq234 eq466362
    | exact resolve eq466362 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234 eq466362
  have eq466368 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) := by
    first
    | exact superpose eq287227 eq466365
    | exact resolve eq466365 eq287227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287227 eq466365
  have eq466370 : (σ x) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) := by
    first
    | (have r₁ := eq466368
       have r₂ := eq28
       grind)
    | exact resolve eq466368 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466368
  have eq466372 : (σ x) = (M.op (M.op (σ y) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) := by
    first
    | exact superpose eq421 eq466370
    | exact resolve eq466370 eq421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421 eq466370
  have eq466374 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) := by
    first
    | exact superpose eq2331 eq466372
    | exact resolve eq466372 eq2331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2331 eq466372
  have eq466376 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq383536 eq466374
    | exact resolve eq466374 eq383536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466374
  have eq569625 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq466376 eq383536
    | exact resolve eq383536 eq466376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383536 eq466376
  have eq569651 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq286167 eq569625
    | exact resolve eq569625 eq286167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569625
  have eq569652 : (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq569651
  have eq570303 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (M.op (σ y) X1) X0) := by
    intro X0 X1
    first
    | exact superpose eq569652 eq53
    | exact resolve eq53 eq569652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq569652
  have eq581155 : ∀ X0 : G, (M.op (M.op (σ y) X0) (M.op (σ y) X0)) = (k (M.op (σ y) X0) (M.op (σ x) (σ x))) := by
    intro X0
    first
    | exact superpose eq570303 eq287141
    | exact resolve eq287141 eq570303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287141
  have eq581183 : ∀ X0 : G, (M.op (M.op (σ y) X0) (M.op (σ y) X0)) = (k (M.op (σ y) X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq286167 eq581155
    | exact resolve eq581155 eq286167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286167 eq581155
  have eq581800 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) X0)) = (k (M.op (σ y) X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq570303 eq581183
    | exact resolve eq581183 eq570303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570303 eq581183
  have eq582098 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (k (M.op (σ y) X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq58 eq581800
    | exact resolve eq581800 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq581800
  have eq582332 : ∀ X0 : G, (M.op (σ x) X0) = (k (M.op (σ y) X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq291829 eq582098
    | exact resolve eq582098 eq291829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291829 eq582098
  have eq630489 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq582332 eq466179
    | exact resolve eq466179 eq582332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466179 eq582332
  have eq630523 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq630489
    | exact resolve eq630489 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq630489
  have eq630597 : False := by grind
  exact eq630597

/-- `Equation4521`: `x ◇ (y ◇ z) = (x ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyy_y_pxy_x_pxy_Equation4521 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4521 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4521.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X3) X3) := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 := by
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
  have eq67 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 X0 X1 X2 x
       have i₂ := eq9 X0 X3 X4 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X1) ≠ (M.op X2 X3) ∨ (k (M.op X2 X3) X0) = (M.op (M.op X2 X3) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 (M.op X2 X3) X0
       have i₂ := eq9 X0 X2 X3 X1
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 (M.op X2 X3) X0
       grind)
    | (have r₁ := eq12 (M.op (M.op X0 X3) X3) X0
       have r₂ := eq9 X0 (M.op X0 X3) X3 X3
       grind)
    | (have r₁ := eq12 (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X0 (M.op X1 X2)))
       have r₂ := eq9 X0 X1 X2 (M.op X0 (M.op X1 X2))
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq469 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X1) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq477 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X1 X2) X2) ∨ (k X3 X0) = (M.op X3 X0) ∨ (M.op X0 X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 X0 X0 X2
       have i₂ := eq14 X3 X0
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X3 X0
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq479 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq505 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq479 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479
  have eq526 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq505 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq505 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq505 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505
  have eq528 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X1 X2) X2) ∨ (k X3 X0) = (M.op X3 X0) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq477 X0 X1 X2 X3
       have j1 := eq12 X3 X0
       grind)
    | (have r₁ := eq477 (M.op (M.op X1 X2) X2) X1 X2 X3
       have r₂ := eq12 (M.op (M.op X1 X2) X2) X1
       grind)
    | (have r₁ := eq477 X0 X1 (M.op X1 X0) X3
       have r₂ := eq12 (M.op X1 X0) (M.op X1 (M.op X1 X0))
       grind)
    | (have r₁ := eq477 X1 X1 X2 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq477 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477
  have eq546 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X0
       have i₂ := eq526 X0 X1
       grind)
    | exact superpose eq526 eq14
    | (have j0 := eq14 X1 X0
       have j1 := eq526 X0 X1
       grind)
    | exact resolve eq14 eq526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq547 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X0)) X0) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X0) X0
       have i₂ := eq526 (σ X0) X1
       grind)
    | exact superpose eq526 eq22
    | (have j1 := eq526 (σ X0) X1
       grind)
    | exact resolve eq22 eq526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq553 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq526 X1 (τ X0)
       grind)
    | exact superpose eq526 eq17
    | (have j1 := eq526 X1 X1
       grind)
    | exact resolve eq17 eq526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq526
  have eq559 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq546 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546
  have eq567 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq547 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq547
    | (have j0 := eq547 X0 X1
       grind)
    | exact resolve eq547 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547
  have eq711 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq567 X1 (σ X0)
       grind)
    | exact superpose eq567 eq15
    | (have j1 := eq567 X1 X1
       grind)
    | exact resolve eq15 eq567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567
  have eq4315 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq553 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq553
    | (have j0 := eq553 X0 X1
       grind)
    | exact resolve eq553 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553
  have eq4385 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4315 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq4315
    | (have j0 := eq4315 X0 X1
       grind)
    | exact resolve eq4315 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4315
  have eq9367 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X1 X1) = X1 ∨ (k X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4385 X0 X1
       have i₂ := eq711 X0 X1
       grind)
    | exact superpose eq711 eq4385
    | (have j0 := eq4385 X0 X1
       have j1 := eq711 X0 X1
       grind)
    | exact resolve eq4385 eq711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711 eq4385
  have eq9412 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq9367 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9367
  have eq11913 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9412 x y
       grind)
    | exact superpose eq9412 eq16
    | (have j1 := eq9412 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq9412 x y
       grind)
    | exact resolve eq16 eq9412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9412
  have eq12027 : y = (k y y) := by grind
  clear eq11913
  have eq12112 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq559 y y
       have i₂ := eq12027
       grind)
    | exact superpose eq12027 eq559
    | (have j0 := eq559 y x
       grind)
    | exact resolve eq559 eq12027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12116 : y = (M.op y y) := by grind
  clear eq12112
  have eq12123 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 y y X1
       have i₂ := eq12116
       grind)
    | exact superpose eq12116 eq9
    | exact resolve eq9 eq12116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12135 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq67 X0 X1 X2 y y
       have i₂ := eq12116
       grind)
    | exact superpose eq12116 eq67
    | exact resolve eq67 eq12116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq12116
  have eq14760 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) X0) = (k (M.op (M.op X0 X1) X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq135 X0 X1 (M.op X0 X1) X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq30316 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq469 y y
       have i₂ := eq12027
       grind)
    | exact superpose eq12027 eq469
    | (have j0 := eq469 y y
       grind)
    | exact resolve eq469 eq12027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469 eq12027
  have eq30451 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq30316
  have eq30588 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq12135 X0 (σ y) (σ y)
       have i₂ := eq30451
       grind)
    | exact superpose eq30451 eq12135
    | exact resolve eq12135 eq30451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12135 eq30451
  have eq30631 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq30588 (σ x)
       grind)
    | exact superpose eq30588 eq16
    | exact resolve eq16 eq30588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30588
  have eq33168 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X0) = (k (M.op X0 X1) X0) ∨ (k X3 X1) = (M.op X3 X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq14760 X1 x
       have i₂ := eq528 X0 X1 x X3
       grind)
    | exact superpose eq528 eq14760
    | (have j1 := eq528 X0 X1 x (M.op X0 X1)
       grind)
    | exact resolve eq14760 eq528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528 eq14760
  have eq905877 : ∀ X0 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq33168 X0 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33168
  have eq905878 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq905877 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905877
  have eq905905 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq905878 X0
       have i₂ := eq559 X0 X1
       grind)
    | exact superpose eq559 eq905878
    | (have j1 := eq559 X0 X0
       grind)
    | exact resolve eq905878 eq559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559
  have eq906311 : ∀ X0 : G, (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq905878 (τ X0)
       grind)
    | exact superpose eq905878 eq18
    | exact resolve eq18 eq905878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq906361 : ∀ X0 : G, (σ (M.op (τ X0) y)) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq906311 X0
       have i₂ := eq12123 (τ X0) (τ X0)
       grind)
    | exact superpose eq12123 eq906311
    | exact resolve eq906311 eq12123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906311
  have eq906483 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq905905 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905905
  have eq906484 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq906483 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906483
  have eq911422 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq906484 (τ X0)
       grind)
    | exact superpose eq906484 eq31
    | exact resolve eq31 eq906484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq911531 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq911422 X0
       have i₂ := eq906484 X0
       grind)
    | exact superpose eq906484 eq911422
    | exact resolve eq911422 eq906484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906484 eq911422
  have eq911946 : ∀ X0 : G, (σ (M.op (τ X0) y)) = (k (σ (τ (M.op X0 X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq906361 X0
       have i₂ := eq911531 X0
       grind)
    | exact superpose eq911531 eq906361
    | exact resolve eq906361 eq911531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906361 eq911531
  have eq912272 : ∀ X0 : G, (σ (M.op (τ X0) y)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq911946 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq911946
    | exact resolve eq911946 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq911946
  have eq912295 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (σ (M.op (τ X0) y)) := by
    intro X0
    first
    | (have i₁ := eq912272 X0
       have i₂ := eq905878 X0
       grind)
    | exact superpose eq905878 eq912272
    | exact resolve eq912272 eq905878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905878 eq912272
  have eq935146 : ∀ X0 : G, (M.op (M.op (σ X0) (σ X0)) (σ X0)) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq912295 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq912295
    | exact resolve eq912295 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq912295
  have eq936314 : ∀ X0 : G, (σ (M.op X0 y)) = (M.op (σ X0) y) := by
    intro X0
    first
    | (have i₁ := eq935146 X0
       have i₂ := eq12123 (σ X0) (σ X0)
       grind)
    | exact superpose eq12123 eq935146
    | exact resolve eq935146 eq12123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12123 eq935146
  have eq937232 : (M.op (σ x) y) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq30631
       have i₂ := eq936314 x
       grind)
    | exact superpose eq936314 eq30631
    | (have r₁ := eq30631
       have r₂ := eq936314 x
       grind)
    | exact resolve eq30631 eq936314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30631 eq936314
  have eq937388 : False := by grind
  exact eq937388

/-- `Equation727`: `x = y ◇ (y ◇ ((z ◇ y) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,X) else if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pyx_y_pyx_x_pxy_Equation727 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law727 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law727.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X1) X0))) = X0 := by
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
  have eq50 : ∀ X0 : G, (M.op y (M.op y (M.op (M.op x y) X0))) = X0 := by
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
  have eq51 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) (M.op (M.op X3 (M.op X2 X1)) X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X2 X1) (M.op (M.op X3 (M.op X2 X1)) X0)) X1 X2
       have i₂ := eq14 X0 (M.op X2 X1) X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq66 (σ X0)
       grind)
    | exact superpose eq66 eq10
    | exact resolve eq10 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq66 sF2
       grind)
    | exact superpose eq66 eq49
    | exact resolve eq49 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq71 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq70
       have i₂ := eq66 x
       grind)
    | exact superpose eq66 eq70
    | exact resolve eq70 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq73 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq68 X0
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq68
    | exact resolve eq68 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq89 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
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
  clear eq44
  have eq94 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq89
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq89
    | exact resolve eq89 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq96 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq94
    | exact resolve eq94 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq97 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
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
  have eq104 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq108 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq104
       have i₂ := eq66 sF3
       grind)
    | exact superpose eq66 eq104
    | exact resolve eq104 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq110 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq108
       have i₂ := eq66 y
       grind)
    | exact superpose eq66 eq108
    | exact resolve eq108 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq144 : ∀ X0 : G, (σ (k X0 (M.op y y))) = (k (σ X0) (M.op (σ y) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq10 X0 (M.op y y)
       have i₂ := eq110
       grind)
    | exact superpose eq110 eq10
    | exact resolve eq10 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq239 : ∀ X0 X1 : G, (M.op (M.op y (M.op (M.op x y) X0)) (M.op (M.op y (M.op (M.op x y) X0)) (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq243 : ∀ X0 X1 : G, (M.op (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) (M.op (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq474 : (σ (M.op (k x x) (k x x))) = (M.op (k (σ x) (σ x)) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq73 (k x x)
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq73
    | exact resolve eq73 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq73
  have eq493 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (σ (M.op (k x x) (k x x))) := by
    first
    | (have i₁ := eq474
       have i₂ := eq66 sF2
       grind)
    | exact superpose eq66 eq474
    | exact resolve eq474 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474
  have eq495 : (σ (M.op (M.op x x) (M.op x x))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq493
       have i₂ := eq66 x
       grind)
    | exact superpose eq66 eq493
    | exact resolve eq493 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493
  have eq700 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X2)) = (M.op (M.op y (M.op (M.op x y) X0)) (M.op (M.op y (M.op (M.op x y) X0)) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq50 eq53
    | exact resolve eq53 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq710 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op X2 X0) x
       have i₂ := eq53 X1 X0 X2 x
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq827 : ∀ X0 : G, (M.op (M.op x y) (M.op y (M.op y X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq710 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq710
    | (have j0 := eq710 y X0 x
       grind)
    | exact resolve eq710 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq829 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq710
    | (have j0 := eq710 (σ y) X0 (σ x)
       grind)
    | exact resolve eq710 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq830 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) (M.op (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq51 eq710
    | exact resolve eq710 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq843 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op X1 y) X0) := by
    intro X0 X1
    first
    | exact superpose eq50 eq710
    | exact resolve eq710 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq844 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op X1 (σ y)) X0) := by
    intro X0 X1
    first
    | exact superpose eq51 eq710
    | exact resolve eq710 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq855 : ∀ X0 : G, (M.op y (M.op (M.op x y) X0)) = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | exact superpose eq50 eq827
    | exact resolve eq827 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827
  have eq867 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq51 eq829
    | exact resolve eq829 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829
  have eq3919 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op (σ y) (M.op (M.op (σ x) (σ y)) X2))) X0) := by
    intro X0 X1 X2
    first
    | exact superpose eq243 eq710
    | exact resolve eq710 eq243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5096 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    first
    | exact superpose eq239 eq700
    | exact resolve eq700 eq239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239 eq700
  have eq5280 : ∀ X0 : G, y = (M.op x (M.op (M.op X0 x) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq5096 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq5096
    | (have j0 := eq5096 y x X0
       grind)
    | exact resolve eq5096 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5286 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq5096
    | (have j0 := eq5096 (σ y) (σ x) X0
       grind)
    | exact resolve eq5096 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13527 : (σ (k (M.op y y) (M.op y y))) = (k (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq144 (M.op y y)
       have i₂ := eq110
       grind)
    | exact superpose eq110 eq144
    | exact resolve eq144 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq144
  have eq13630 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (σ (k (M.op y y) (M.op y y))) := by
    first
    | (have i₁ := eq13527
       have i₂ := eq66 (M.op sF3 sF3)
       grind)
    | exact superpose eq66 eq13527
    | exact resolve eq13527 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13527
  have eq13638 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq13630
       have i₂ := eq66 (M.op y y)
       grind)
    | exact superpose eq66 eq13630
    | exact resolve eq13630 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq13630
  have eq13640 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq844 eq13638
    | exact resolve eq13638 eq844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13638
  have eq13641 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq867 eq13640
    | exact resolve eq13640 eq867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq867 eq13640
  have eq13642 : (σ (M.op (M.op x y) (M.op y y))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | (have i₁ := eq13641
       have i₂ := eq843 (M.op y y) y
       grind)
    | exact superpose eq843 eq13641
    | exact resolve eq13641 eq843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13641
  have eq13643 : (σ (M.op y (M.op (M.op x y) y))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq855 eq13642
    | exact resolve eq13642 eq855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855 eq13642
  have eq13646 : (M.op y (M.op (M.op x y) y)) = (τ (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y)))) := by
    first
    | exact superpose eq13643 eq16
    | exact resolve eq16 eq13643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47989 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq97 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq47997 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq47989
    | exact resolve eq47989 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47989
  have eq48008 : (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq47997
       have r₂ := eq27
       grind)
    | exact resolve eq47997 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47997
  have eq48012 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq48008
    | exact resolve eq48008 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48008
  have eq48075 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq48012 eq5096
    | exact resolve eq5096 eq48012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48012
  have eq48095 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq5286 eq48075
    | exact resolve eq48075 eq5286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5286 eq48075
  have eq48178 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op (M.op X0 (σ y)) (σ y))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq48095 eq5096
    | exact resolve eq5096 eq48095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48095
  have eq48200 : (σ x) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq844 eq48178
    | (have j0 := eq48178 (σ x)
       grind)
    | exact resolve eq48178 eq844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844 eq48178
  have eq49304 : (τ (σ x)) = (M.op y (M.op (M.op x y) y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq48200 eq13646
    | exact resolve eq13646 eq48200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13646 eq48200
  have eq49435 : x = (M.op y (M.op (M.op x y) y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq28 eq49304
    | exact resolve eq49304 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49304
  have eq49501 : y = (M.op y x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq49435 eq50
    | exact resolve eq50 eq49435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq49435
  have eq49572 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by grind
  clear eq49501
  have eq49752 : ∀ X0 : G, x = (M.op x (M.op (M.op X0 x) (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq5096 x x X0
       have i₂ := eq49572
       grind)
    | exact superpose eq49572 eq5096
    | exact resolve eq5096 eq49572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49572
  have eq49772 : y = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq5280 eq49752
    | exact resolve eq49752 eq5280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5280 eq49752
  have eq49828 : ∀ X0 : G, (M.op x (M.op x (M.op y X0))) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq49772
       grind)
    | exact superpose eq49772 eq14
    | exact resolve eq14 eq49772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49870 : ∀ X0 : G, x = (M.op y (M.op (M.op X0 y) y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq5096 x y X0
       have i₂ := eq49772
       grind)
    | exact superpose eq49772 eq5096
    | exact resolve eq5096 eq49772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5096
  have eq49892 : x = (M.op y (M.op (M.op x y) y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq49870 x
       have i₂ := eq843 y x
       grind)
    | (have i₁ := eq49870 x
       have i₂ := eq843 y x
       grind)
    | exact superpose eq843 eq49870
    | (have j0 := eq49870 x
       grind)
    | exact resolve eq49870 eq843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843 eq49870
  have eq50810 : (σ x) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq49892 eq13643
    | exact resolve eq13643 eq49892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13643 eq49892
  have eq50941 : (σ x) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq50810
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq50810
    | exact resolve eq50810 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50810
  have eq51451 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op (M.op X1 (σ x)) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq50941 eq3919
    | exact resolve eq3919 eq50941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3919
  have eq51454 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (M.op (σ y) X0))) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq50941 eq243
    | exact resolve eq243 eq50941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq51455 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq50941 eq51
    | exact resolve eq51 eq50941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq59090 : x = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq49828 x
       have i₂ := eq49772
       grind)
    | exact superpose eq49772 eq49828
    | exact resolve eq49828 eq49772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49772 eq49828
  have eq59184 : x = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq59090
  have eq59221 : x = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq59184
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq59184
    | exact resolve eq59184 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59184
  have eq59608 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 x) (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq59221 eq710
    | exact resolve eq710 eq59221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710 eq59221
  have eq76016 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq51455 eq51454
    | exact resolve eq51454 eq51455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51454 eq51455
  have eq76124 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq76016
  have eq76166 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq26 eq76124
    | exact resolve eq76124 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76124
  have eq80276 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq495
       have i₂ := eq59608 x
       grind)
    | exact superpose eq59608 eq495
    | exact resolve eq495 eq59608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq495 eq59608
  have eq80385 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq80276
    | exact resolve eq80276 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80276
  have eq82794 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (M.op (σ x) X0))) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq50941 eq830
    | exact resolve eq830 eq50941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830 eq50941
  have eq89604 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq76166 eq82794
    | exact resolve eq82794 eq76166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76166 eq82794
  have eq89716 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq89604
  have eq106272 : (σ (M.op x y)) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq80385 eq51451
    | exact resolve eq51451 eq80385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51451 eq80385
  have eq106387 : (σ (M.op x y)) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq106272
  have eq106543 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq106387 eq89716
    | exact resolve eq89716 eq106387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89716 eq106387
  have eq106641 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq106543
  have eq106681 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq106641
       have r₂ := eq27
       grind)
    | exact resolve eq106641 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106641
  have eq106714 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq106681 eq29
    | exact resolve eq29 eq106681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq106681
  have eq106880 : x = y ∨ x = y := by
    first
    | exact superpose eq28 eq106714
    | exact resolve eq106714 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq106714
  have eq106881 : x = y := by grind
  clear eq106880
  have eq106900 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq106881
       grind)
    | exact superpose eq106881 eq18
    | exact resolve eq18 eq106881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq106901 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq106881
       grind)
    | exact superpose eq106881 eq24
    | exact resolve eq24 eq106881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq106881
  have eq107073 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq106901
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq106901
    | exact resolve eq106901 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq106901
  have eq107096 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq107073 eq26
    | exact resolve eq26 eq107073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq107073
  have eq107509 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq107096 eq71
    | exact resolve eq71 eq107096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq107096
  have eq107666 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq107509
       have i₂ := eq106900
       grind)
    | exact superpose eq106900 eq107509
    | exact resolve eq107509 eq106900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106900 eq107509
  have eq107700 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq107666 eq15
    | exact resolve eq15 eq107666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107666
  have eq107785 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq107700
    | exact resolve eq107700 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq107700
  have eq107806 : False := by grind
  exact eq107806

/-- `Equation746`: `x = y ◇ (z ◇ ((x ◇ y) ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(Y,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pxx_pxy_pyy_pxx_pyx_Equation746 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law746 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law746.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X0 X1) X2))) = X0 := by
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
  clear eq43
  have eq51 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op X0 (M.op (M.op (σ x) (σ y)) X0))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op X0 X2) X1)) (M.op X3 (M.op X0 X3))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op X1 (M.op (M.op X0 X2) X1)) X3
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X2 (M.op (M.op X0 (M.op X3 X1)) X2)) X0)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 X1 (M.op X2 (M.op (M.op X0 (M.op X3 X1)) X2))
       have i₂ := eq14 X0 (M.op X3 X1) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq63 sF2
       grind)
    | exact superpose eq63 eq49
    | exact resolve eq49 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq68 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq67
       have i₂ := eq63 x
       grind)
    | exact superpose eq63 eq67
    | exact resolve eq67 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq67
  have eq98 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  clear eq36
  have eq107 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y y) = (M.op y x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq98
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq98
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq98 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y y) = (M.op y x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq107
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq107
    | exact resolve eq107 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y y) = (M.op y x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq20 eq113
    | exact resolve eq113 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq115 : (M.op y y) = (M.op y x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq114
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq114
    | exact resolve eq114 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq399 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X0) X3) = (M.op (M.op (M.op X1 (M.op X2 X1)) X0) (M.op X4 (M.op X3 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 X3 (M.op X1 (M.op X2 X1)) (M.op (M.op X2 X0) X3) X4
       have i₂ := eq52 X2 X3 X0 X1
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq408 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op X2 X0) X2) X3) X1)) X0) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 (M.op (M.op X2 X0) X2) X1 X3 (M.op X2 (M.op (M.op X2 X0) X2))
       have i₂ := eq52 X2 X2 X0 (M.op (M.op X2 X0) X2)
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq489 : ∀ X0 X1 X2 : G, (σ y) = (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) (M.op (M.op X1 (M.op (M.op X2 (σ x)) X1)) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq491 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 (M.op (M.op X1 (M.op X0 X3)) X4)) = (M.op X1 (M.op (M.op X2 (M.op X0 X2)) X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 X3 X1 X2 (M.op X4 (M.op (M.op X1 (M.op X0 X3)) X4))
       have i₂ := eq53 X1 X3 X4 X0
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq492 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X2) (M.op (M.op X3 (M.op X0 X3)) (M.op X4 (M.op (M.op X1 X0) X4)))) = X2 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 (M.op X4 (M.op (M.op X1 X0) X4)) (M.op X1 X2) X3 X2
       have i₂ := eq52 X1 X4 X0 X2
       grind)
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq495 : ∀ X0 X1 X2 X3 : G, (M.op X3 X0) = (M.op X1 (M.op (M.op (M.op X2 (M.op X3 X2)) X0) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X1 X1 (M.op X2 (M.op X3 X2)) (M.op X3 X0)
       have i₂ := eq52 X3 X1 X0 X2
       grind)
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq498 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X1)) = (M.op X2 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X1 X1 X2 (M.op X2 (M.op X0 X2))
       have i₂ := eq53 X2 X2 X1 X0
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq501 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X0 X1)) X2) X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op (M.op X1 (M.op X0 X1)) X2) X1
       have i₂ := eq53 X1 X1 X2 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq504 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 (M.op (M.op X4 (M.op X0 X2)) X3)) X4) = (M.op (M.op X1 (M.op X0 X1)) (M.op X5 (M.op X2 X5))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq52 X2 X1 (M.op (M.op X3 (M.op (M.op X4 (M.op X0 X2)) X3)) X4) X5
       have i₂ := eq53 X4 X2 X3 X0
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq956 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op (M.op X1 X0) X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq498 (M.op (M.op X1 X0) X1) (M.op X1 (M.op (M.op X1 X0) X1)) X2
       have i₂ := eq52 X1 X1 X0 (M.op (M.op X1 X0) X1)
       grind)
    | exact superpose eq52 eq498
    | exact resolve eq498 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1072 : ∀ X0 : G, (M.op (M.op (M.op y (M.op x y)) X0) x) = X0 := by
    intro X0
    first
    | (have i₁ := eq501 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq501
    | (have j0 := eq501 x y X0
       grind)
    | exact resolve eq501 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1074 : ∀ X0 : G, (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) X0) (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq501
    | (have j0 := eq501 (σ x) (σ y) X0
       grind)
    | exact resolve eq501 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1148 : ∀ X0 : G, x = (M.op (M.op X0 (M.op y (M.op x y))) X0) := by
    intro X0
    first
    | exact superpose eq1072 eq501
    | exact resolve eq501 eq1072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1072
  have eq1169 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) X0) := by
    intro X0
    first
    | exact superpose eq1074 eq501
    | exact resolve eq501 eq1074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1074
  have eq1180 : ∀ X0 : G, x = (M.op (M.op X0 (M.op y X0)) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq1148 sF0
       have i₂ := eq498 y sF0 x
       grind)
    | (have i₁ := eq1148 sF0
       have i₂ := eq498 y x sF0
       grind)
    | exact superpose eq498 eq1148
    | exact resolve eq1148 eq498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1224 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (M.op (σ y) X0)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq1169 sF4
       have i₂ := eq498 sF3 sF4 x
       grind)
    | (have i₁ := eq1169 sF4
       have i₂ := eq498 sF3 x sF4
       grind)
    | exact superpose eq498 eq1169
    | exact resolve eq1169 eq498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498 eq1169
  have eq1261 : ∀ X0 : G, y = (M.op X0 (M.op (M.op (M.op x y) x) X0)) := by
    intro X0
    first
    | exact superpose eq1180 eq53
    | exact resolve eq53 eq1180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1180
  have eq1372 : ∀ X0 : G, (M.op (M.op (σ y) X0) (M.op (M.op (σ x) (σ y)) (σ x))) = X0 := by
    intro X0
    first
    | exact superpose eq1224 eq14
    | exact resolve eq14 eq1224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1520 : (σ x) = (M.op (M.op (M.op (M.op (M.op x y) x) (σ y)) y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1261 eq1224
    | exact resolve eq1224 eq1261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1224 eq1261
  have eq1541 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op X0 (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq1372 eq501
    | exact resolve eq501 eq1372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1372
  have eq1741 : x = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op y (M.op x y)) (σ y))) := by
    first
    | exact superpose eq1541 eq1148
    | exact resolve eq1148 eq1541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1148 eq1541
  have eq4832 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op (M.op (M.op x y) x) X1) X0)) y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq408 y X0 x X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq408
    | (have j0 := eq408 y X0 x X1
       grind)
    | exact resolve eq408 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4840 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1) X0)) (σ y)) = X1 := by
    intro X0 X1
    first
    | exact superpose eq26 eq408
    | (have j0 := eq408 (σ y) X0 (σ x) X1
       grind)
    | exact resolve eq408 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408
  have eq7486 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 (M.op (M.op (σ x) (σ y)) X1)) (σ x)) X0)) X2) = (M.op X3 (M.op (M.op (σ y) X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq489 eq495
    | exact resolve eq495 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489
  have eq7539 : ∀ X2 X3 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X2) = (M.op X3 (M.op (M.op (σ y) X2) X3)) := by
    intro X2 X3
    first
    | (have i₁ := eq7486 x X2 X2 X3
       have i₂ := eq495 sF2 x X2 sF4
       grind)
    | exact superpose eq495 eq7486
    | exact resolve eq7486 eq495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7486
  have eq9445 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) (M.op X0 (M.op (M.op X3 (M.op X1 X3)) X2))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq399 X2 X3 X1 (M.op X0 (M.op (M.op X3 (M.op X1 X3)) X2)) x
       have i₂ := eq14 X0 (M.op (M.op X3 (M.op X1 X3)) X2) x
       grind)
    | exact superpose eq14 eq399
    | exact resolve eq399 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10739 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 (M.op (M.op X2 X0) X1)) = (M.op X2 (M.op (M.op X5 (M.op (M.op (M.op X3 (M.op X4 X3)) X0) X5)) X4)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq491 (M.op (M.op X3 (M.op X4 X3)) X0) X2 X5 X4 X1
       have i₂ := eq501 X4 X3 X0
       grind)
    | exact superpose eq501 eq491
    | exact resolve eq491 eq501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491 eq501
  have eq11747 : ∀ X0 X1 X2 X4 : G, (M.op X1 (M.op (M.op X2 X0) X1)) = (M.op X2 (M.op (M.op X4 X0) X4)) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq10739 X0 X1 X2 x X4 x
       have i₂ := eq495 X0 x x X4
       grind)
    | exact superpose eq495 eq10739
    | exact resolve eq10739 eq495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq495 eq10739
  have eq12099 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op (M.op X2 (M.op (M.op (σ x) (σ y)) X2)) (σ x)) (M.op X3 (M.op (M.op X0 (σ y)) X3)))) = X1 := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq51 eq492
    | exact resolve eq492 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq492
  have eq12638 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op X0 (σ y)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12099 X0 X1 X1 x
       have i₂ := eq399 sF2 X1 sF4 (M.op X0 sF3) x
       grind)
    | exact superpose eq399 eq12099
    | exact resolve eq12099 eq399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399 eq12099
  have eq20573 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op X2 (M.op (M.op X3 X0) X3)) X1)) X2) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq504 (M.op X3 X0) x X3 X1 X2 x
       have i₂ := eq52 X3 x X0 x
       grind)
    | exact superpose eq52 eq504
    | exact resolve eq504 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq504
  have eq58356 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op X1 (M.op X0 X1)) (σ y))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7539 (M.op (M.op X0 (M.op x X0)) sF3) X0
       have i₂ := eq53 X0 X0 sF3 x
       grind)
    | exact superpose eq53 eq7539
    | exact resolve eq7539 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq7539
  have eq63118 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op X0 X1) (σ y))) X0) = X1 := by
    intro X0 X1
    first
    | exact superpose eq12638 eq956
    | exact resolve eq956 eq12638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq956 eq12638
  have eq225396 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op x y) x) X0) y) (M.op X1 X0)) = X1 := by
    intro X0 X1
    first
    | exact superpose eq4832 eq9445
    | exact resolve eq9445 eq4832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4832 eq9445
  have eq247963 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op X0 X1) X0)) (σ y)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4840 X1 X0
       have i₂ := eq11747 X0 X1 (M.op sF4 sF2) x
       grind)
    | (have i₁ := eq4840 (M.op sF4 sF2) X0
       have i₂ := eq11747 X0 X1 (M.op sF4 sF2) (M.op sF4 sF2)
       grind)
    | exact superpose eq11747 eq4840
    | exact resolve eq4840 eq11747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4840 eq11747
  have eq291359 : ∀ X0 X1 : G, y = (M.op (M.op X0 (M.op (M.op X1 (M.op (M.op y x) y)) X0)) X1) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq20573 y X0 X1 y
       have i₂ := eq115
       grind)
    | exact superpose eq115 eq20573
    | exact resolve eq20573 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq291401 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq291359 x x
       have i₂ := eq20573 x x x y
       grind)
    | exact superpose eq20573 eq291359
    | exact resolve eq291359 eq20573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20573 eq291359
  have eq403512 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq291401 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq291401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291401
  have eq403519 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq403512
    | exact resolve eq403512 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403512
  have eq403530 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq403519
       have r₂ := eq27
       grind)
    | exact resolve eq403519 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403519
  have eq403534 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq403530
    | exact resolve eq403530 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403530
  have eq403798 : (σ y) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ y) (σ x)) (σ y))) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq403534 eq247963
    | exact resolve eq247963 eq403534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247963 eq403534
  have eq403801 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq63118 eq403798
    | exact resolve eq403798 eq63118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63118 eq403798
  have eq404197 : (σ y) = (M.op (M.op (M.op (M.op (M.op x y) x) (σ y)) y) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq403801 eq225396
    | exact resolve eq225396 eq403801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225396 eq403801
  have eq404205 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq1520 eq404197
    | exact resolve eq404197 eq1520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1520 eq404197
  have eq404206 : (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq404205
  have eq404633 : y = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op y (M.op x y)) (σ y))) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq58356 y y
       have i₂ := eq404206
       grind)
    | exact superpose eq404206 eq58356
    | exact resolve eq58356 eq404206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58356 eq404206
  have eq404658 : x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1741 eq404633
    | exact resolve eq404633 eq1741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1741 eq404633
  have eq404659 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq404658
  have eq404853 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq404659 eq29
    | exact resolve eq29 eq404659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq404659
  have eq405191 : x = y ∨ x = y := by
    first
    | exact superpose eq28 eq404853
    | exact resolve eq404853 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq404853
  have eq405192 : x = y := by grind
  clear eq405191
  have eq405216 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq405192
       grind)
    | exact superpose eq405192 eq18
    | exact resolve eq18 eq405192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq405217 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq405192
       grind)
    | exact superpose eq405192 eq24
    | exact resolve eq24 eq405192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq405192
  have eq405562 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq405217
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq405217
    | exact resolve eq405217 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq405217
  have eq405615 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq405562 eq26
    | exact resolve eq26 eq405562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq405562
  have eq406652 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq405615 eq68
    | exact resolve eq68 eq405615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq405615
  have eq407122 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq406652
       have i₂ := eq405216
       grind)
    | exact superpose eq405216 eq406652
    | exact resolve eq406652 eq405216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405216 eq406652
  have eq407228 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq407122 eq15
    | exact resolve eq15 eq407122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407122
  have eq407312 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq407228
    | exact resolve eq407228 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq407228
  have eq407333 : False := by grind
  exact eq407333
